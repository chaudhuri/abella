#!/bin/sh
#
# Generate term-unification traces as ReBella (.rbl) scripts for every
# example under a directory (examples/ by default).  Each example X.thm
# yields X_unifications.rbl next to it.
#
# Term.log_unifications is a compile-time switch, so this script enables
# it, rebuilds Abella, runs the examples in batch mode, and then restores
# the source and binary.

set -eu

cd "$(dirname "$0")/.."

dir=${1:-examples}
term=src/term.ml
makefile=bad/unifications.mk

restore () {
  sed -i 's/^let log_unifications = true$/let log_unifications = false/' "$term"
  dune build src/abella.exe src/abella_dep.exe >/dev/null 2>&1 || true
}
trap restore EXIT HUP INT TERM

sed -i 's/^let log_unifications = false$/let log_unifications = true/' "$term"
dune build src/abella.exe src/abella_dep.exe

mkdir -p bad
find "$dir" -name '*_unifications.rbl' -delete

_build/default/src/abella_dep.exe \
  -a "$PWD/_build/default/src/abella.exe" \
  -c -o "$makefile" -r "$dir"
make -k -j"$(nproc 2>/dev/null || echo 1)" -B -f "$makefile" all >/dev/null 2>&1 || true

find "$dir" -name '*_unifications.rbl' | sort

rm -f "$makefile"
