#!/usr/bin/env bash
# run_all.sh -- re-run the checks of all five counterexamples.
#
#   C       compiles the four search programs into build/ and runs them on small orders,
#           comparing the per-order counts with the files in wowii*/data/.
#           Needs nauty's gentreeg, copyg and geng on PATH (also as nauty-geng etc.) or in
#           $NAUTY; skipped otherwise.
#           FULL=1 repeats the full ranges of data/ (trees up to 24 vertices, connected
#           graphs up to 10 vertices; several hours on one core).
#   Python  wowii*/python/verify*.py
#   Julia   wowii*/julia/verify*.jl      (if julia is on PATH or $JULIA is set)
#   Lean    wowii*/lean/C*.lean          (if lean is on PATH; each folder pins its toolchain)
#
# Exit status 0 means every check that ran passed.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BUILD="$ROOT/build"
mkdir -p "$BUILD"
FAILED=0
fail() { echo "FAIL: $*"; FAILED=1; }
ok() { echo "ok:   $*"; }

tool() {  # tool NAME -> path of a nauty program, or empty (Debian names them nauty-NAME)
  if [ -n "${NAUTY:-}" ] && [ -x "$NAUTY/$1" ]; then echo "$NAUTY/$1"
  else command -v "$1" || command -v "nauty-$1" || true; fi
}

echo "== C"
for p in wowii352/c/search352 wowii358/c/search358 wowii319/c/c319 wowii427/c/c427; do
  cc -O2 -o "$BUILD/$(basename "$p")" "$ROOT/$p.c" || fail "compile $p.c"
done
GENTREEG=$(tool gentreeg); COPYG=$(tool copyg); GENG=$(tool geng)
if [ -z "$GENTREEG" ] || [ -z "$COPYG" ] || [ -z "$GENG" ]; then
  echo "nauty (gentreeg, copyg, geng) not found: skipping the searches; set NAUTY to its directory"
else
  if [ "${FULL:-0}" = 1 ]; then TMAX=24; GMAX=10; else TMAX=19; GMAX=9; fi
  trees() { for n in $(seq "$1" "$2"); do "$GENTREEG" -q "$n" | "$COPYG" -g -q; done; }
  same_counts() {  # same_counts NAME OUTPUT DATAFILE: per-order summary lines must agree
    local got want
    got=$(grep '^n=' "$2"); want=$(grep -F -x -f <(echo "$got") "$3")
    if [ -n "$got" ] && [ "$got" = "$want" ]; then ok "$1: $(echo "$got" | wc -l) orders agree with data"
    else fail "$1: counts differ from $3"; fi
  }
  # brute-force cross-check of the tree dynamic programme
  trees 3 16 | "$BUILD/search352" -b > "$BUILD/brute352.txt" && ok "search352 -b: dp = brute force on all trees up to 16 vertices" || fail "search352 -b"
  trees 3 16 | "$BUILD/search358" -b > "$BUILD/brute358.txt" && ok "search358 -b: dp = brute force on all trees up to 16 vertices" || fail "search358 -b"
  trees 3 "$TMAX" | "$BUILD/search352" > "$BUILD/search352.txt"
  same_counts "Conjecture 352, trees 3..$TMAX" "$BUILD/search352.txt" "$ROOT/wowii352/data/search_3_24.txt"
  trees 3 "$TMAX" | "$BUILD/search358" > "$BUILD/search358.txt"
  same_counts "Conjectures 358/359, trees 3..$TMAX" "$BUILD/search358.txt" "$ROOT/wowii358/data/search_3_24.txt"
  for n in $(seq 2 "$GMAX"); do echo "== n=$n"; "$GENG" -cq "$n" | "$BUILD/c319"; done > "$BUILD/c319.txt"
  counts319() { grep -E '^(==|graphs|C3[0-9][0-9][IX] tested)' "$1"; }
  if diff -q <(counts319 "$BUILD/c319.txt") \
       <(sed "/^== n=$((GMAX + 1))\$/,\$d" "$ROOT/wowii319/data/connected_2_10.txt" | counts319 /dev/stdin) > /dev/null
  then ok "Conjecture 319, connected graphs 2..$GMAX: counts agree with data"
  else fail "Conjecture 319: output differs from data"; fi
  for n in $(seq 4 "$GMAX"); do "$GENG" -cq "$n"; done | "$BUILD/c427" > "$BUILD/c427.txt"
  same_counts "Conjecture 427, connected graphs 4..$GMAX" "$BUILD/c427.txt" "$ROOT/wowii427/data/connected_4_10.txt"
fi

echo "== Python"
for d in 352 358 319 427; do
  python3 "$ROOT/wowii$d/python/verify$d.py" > "$BUILD/py$d.txt" 2>&1 && grep -q '^ALL OK' "$BUILD/py$d.txt" \
    && ok "verify$d.py" || fail "verify$d.py (see build/py$d.txt)"
done

echo "== Julia"
JULIA="${JULIA:-$(command -v julia || true)}"
if [ -z "$JULIA" ]; then echo "julia not found: skipping"; else
  for d in 352 358 319 427; do
    "$JULIA" "$ROOT/wowii$d/julia/verify$d.jl" > "$BUILD/jl$d.txt" 2>&1 && grep -q '^ALL OK' "$BUILD/jl$d.txt" \
      && ok "verify$d.jl" || fail "verify$d.jl (see build/jl$d.txt)"
  done
fi

echo "== Lean"
if ! command -v lean > /dev/null; then echo "lean not found: skipping (install elan)"; else
  for d in 352 358 319 427; do
    out=$(cd "$ROOT/wowii$d/lean" && lean "C$d.lean" 2>&1); st=$?
    if [ $st -eq 0 ] && ! echo "$out" | grep -q 'error\|sorry'; then
      ok "C$d.lean"; echo "$out" | sed 's/^/        /'
    else fail "C$d.lean"; echo "$out"; fi
  done
fi

[ $FAILED = 0 ] && echo "ALL CHECKS PASSED" || echo "SOME CHECKS FAILED"
exit $FAILED
