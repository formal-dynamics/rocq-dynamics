#!/usr/bin/env bash
# Install the pinned opam dependencies inside the docker-coq container.
#
# Compiling mathcomp-analysis from source costs ~25 min and both workflows
# (build.yml and blueprint.yml) need exactly the same switch, so the whole
# opam root is tarred into the workspace, where actions/cache can pick it up:
# the workflows key that cache on the hash of THIS file, so editing the
# package list below is what invalidates it. Keep the list here, not in the
# workflows, so that the key and the packages cannot drift apart.
set -eu

CACHE_TAR="${1:-.ci-opam.tar}"

if [ -f "$CACHE_TAR" ]; then
  echo "Restoring the opam root from $CACHE_TAR"
  tar -xf "$CACHE_TAR" -C "$HOME"
  exit 0
fi

opam repo add rocq-released https://rocq-prover.org/opam/released || true
opam update -y
opam install -y \
  rocq-mathcomp-classical.1.16.0 rocq-mathcomp-reals.1.16.0 \
  rocq-mathcomp-analysis.1.16.0 \
  coq-mathcomp-algebra-tactics.1.2.7 coq-mathcomp-zify

# download-cache holds the fetched tarballs, useless once the packages are
# built; everything else is kept so that the restored root stays consistent.
echo "Saving the opam root to $CACHE_TAR"
tar -cf "$CACHE_TAR" -C "$HOME" --exclude='.opam/download-cache' .opam
