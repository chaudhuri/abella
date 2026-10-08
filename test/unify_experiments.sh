#!/bin/sh
#
# Collect term-unification traces for every example under a directory
# (examples/ by default) into a single CBOR array at bad/unifications.cbor.
#
# Term.log_unifications is a compile-time switch, so this script enables it,
# rebuilds Abella, runs the examples in batch mode, and then restores the
# source and binary.

set -eu

cd "$(dirname "$0")/.."

dir=${1:-examples}
term=src/term.ml
makefile=bad/unifications.mk
out=bad/unifications.cbor
merge=src/tools/cbor_merge.exe

restore () {
  sed -i 's/^let log_unifications = true$/let log_unifications = false/' "$term"
  dune build src/abella.exe src/abella_dep.exe >/dev/null 2>&1 || true
}
trap restore EXIT HUP INT TERM

sed -i 's/^let log_unifications = false$/let log_unifications = true/' "$term"
dune build src/abella.exe src/abella_dep.exe "$merge"

mkdir -p bad
find "$dir" -name '*_unifications.cbor' -delete

_build/default/src/abella_dep.exe \
  -a "$PWD/_build/default/src/abella.exe" \
  -c -o "$makefile" -r "$dir"
make -k -j"$(nproc 2>/dev/null || echo 1)" -B -f "$makefile" all >/dev/null 2>&1 || true

find "$dir" -name '*_unifications.cbor' | sort \
  | xargs -r cat | "$PWD/_build/default/$merge" > "$out"

find "$dir" -name '*_unifications.cbor' -delete
rm -f "$makefile"
