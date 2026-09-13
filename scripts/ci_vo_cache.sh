#!/usr/bin/env bash
# Make the CI cache of build products safe to reuse across commits.
#
# Why this exists. `make` decides what to rebuild from timestamps, and a
# restored cache cannot be trusted to have consistent ones: a commit authored
# before the previous CI run finished carries an mtime older than the cached
# .vo built by that run, so make would skip a file that genuinely changed and
# the run would report a proof as checked without checking it. Timestamps are
# the wrong key. Content is the right one.
#
#   record  writes the sha256 of every source file next to the build products.
#   prune   deletes the build products of every source whose sha256 differs
#           from the recorded one (and every orphan), so make is forced to
#           rebuild exactly what changed. Files whose hash still matches keep
#           their .vo, and make's own dependency graph takes care of their
#           dependents.
#   touch   marks the build products that survived `prune` as current. Run it
#           INSIDE the container, after the opam root has been restored:
#           coqdep makes every .vo depend on the rocqworker binary of the
#           switch, so a switch unpacked after the .vo were cached makes all
#           of them look stale and the cache buys nothing. Re-dating them is
#           safe precisely because `prune` already deleted the ones whose
#           source moved -- correctness rests on the hashes, never on mtimes.
#
# With no manifest, or a changed _CoqProject (file list and flags), nothing in
# the cache is trustworthy and everything goes.
set -eu

MANIFEST=".ci-vo-manifest.sha256"

sources() {
  find theories -name '*.v' -print | sort
}

products_of() {  # .v path -> the build products beside it
  local v="$1" base="${1%.v}"
  printf '%s.vo\n%s.vok\n%s.vos\n%s.glob\n' "$base" "$base" "$base" "$base"
}

drop_everything() {
  find theories \( -name '*.vo' -o -name '*.vok' -o -name '*.vos' \
                -o -name '*.glob' \) -delete
  rm -f "$MANIFEST"
}

case "${1:-}" in
  record)
    { sha256sum _CoqProject; sources | xargs -r sha256sum; } > "$MANIFEST"
    echo "recorded $(wc -l < "$MANIFEST") source hashes"
    ;;

  prune)
    if [ ! -f "$MANIFEST" ]; then
      echo "no manifest: dropping every cached build product"
      drop_everything
      exit 0
    fi
    if ! grep -q "  _CoqProject$" "$MANIFEST" \
       || ! sha256sum -c --status <(grep "  _CoqProject$" "$MANIFEST"); then
      echo "_CoqProject changed: dropping every cached build product"
      drop_everything
      exit 0
    fi

    dropped=0
    while IFS= read -r v; do
      recorded=$(awk -v f="$v" '$2 == f {print $1}' "$MANIFEST")
      current=$(sha256sum "$v" | cut -d' ' -f1)
      if [ "$recorded" != "$current" ]; then
        products_of "$v" | xargs -r rm -f
        dropped=$((dropped + 1))
      fi
    done < <(sources)

    # Build products whose source is gone would otherwise linger forever.
    while IFS= read -r vo; do
      [ -f "${vo%.vo}.v" ] || { rm -f "${vo%.vo}".{vo,vok,vos,glob}; \
                                dropped=$((dropped + 1)); }
    done < <(find theories -name '*.vo' -print)

    echo "pruned the build products of $dropped source file(s)"
    ;;

  touch)
    worker=$(find "$HOME/.opam" -name 'rocqworker*' -type f 2>/dev/null | head -1)
    sample=$(find theories -name '*.vo' 2>/dev/null | head -1)
    if [ -n "$sample" ]; then
      echo "before:"
      [ -n "$worker" ] && ls -l --time-style=long-iso "$worker"
      ls -l --time-style=long-iso "$sample"
    fi
    find theories \( -name '*.vo' -o -name '*.vok' -o -name '*.vos' \
                  -o -name '*.glob' \) -exec touch {} +
    if [ -n "$sample" ]; then
      echo "after:"
      ls -l --time-style=long-iso "$sample"
    fi
    ;;

  *)
    echo "usage: $0 {record|prune|touch}" >&2
    exit 2
    ;;
esac
