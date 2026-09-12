#!/usr/bin/env bash
# Headline audit: (optionally clean-)rebuild the project, then Print Assumptions
# of every theorem listed in HEADLINES and fail if anything beyond the accepted
# axiom budget shows up.
#
# Accepted axioms: the three mathcomp-classical (boolp) axioms that every
# mathcomp-analysis development depends on. Nothing else, and never Admitted.
#
# Usage: ./verify.sh            # make clean && make -j && audit
#        ./verify.sh --no-clean # incremental build && audit
set -euo pipefail
cd "$(dirname "$0")"

# Fully qualified names of the theorems to audit (Dynamics.<module>.<name>).
# Extend this list as the port progresses; PLAN.md tracks the intended set.
HEADLINES=(
  Dynamics.prelude.prelude_smoke
)

ACCEPTED_AXIOMS=(
  boolp.functional_extensionality_dep
  boolp.propositional_extensionality
  boolp.constructive_indefinite_description
)

if [[ "${1:-}" != "--no-clean" ]]; then
  make clean >/dev/null
fi
make -j"$(nproc)"

probe="$(mktemp --suffix=.v)"
trap 'rm -f "$probe"' EXIT
for h in "${HEADLINES[@]}"; do
  mod="${h%.*}"
  echo "From ${mod%.*} Require Import ${mod##*.}." >> "$probe"
done
for h in "${HEADLINES[@]}"; do
  echo "Print Assumptions $h." >> "$probe"
done

out="$(rocq repl -q -R theories Dynamics -batch -l "$probe" 2>&1)" || {
  echo "$out"; echo "verify.sh: rocq repl failed"; exit 1; }
echo "$out"

status=0
while IFS= read -r line; do
  [[ -z "$line" ]] && continue
  case "$line" in
    "Closed under the global context"|"Axioms:"|"Print Assumptions"*) continue ;;
  esac
  name="${line%% *}"
  ok=0
  for a in "${ACCEPTED_AXIOMS[@]}"; do
    [[ "$name" == *"$a"* ]] && ok=1
  done
  if [[ $ok -eq 0 ]]; then
    echo "verify.sh: UNEXPECTED ASSUMPTION: $line"; status=1
  fi
done <<< "$(echo "$out" | grep -vE '^\s+' )"

if [[ $status -eq 0 ]]; then
  echo "verify.sh: OK — headline theorems depend only on the accepted axioms."
fi
exit $status
