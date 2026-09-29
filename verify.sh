#!/usr/bin/env bash
# One-command entry point for the whole verification.
#
#   ./verify.sh
#
# Runs, in order:
#   1. the Python differential checks and fuzz-corpus generation,
#   2. the Lean proofs (Add.lean + the generated FuzzVectors.lean + Conformance.lean),
#   3. the executable conformance run,
#   4. a negative control asserting that buggy models are *rejected*.
#
# Exits non-zero if any stage fails, including if the negative control unexpectedly
# compiles (which would mean the suite is vacuous).
set -uo pipefail
cd "$(dirname "$0")"

fail=0
step() { printf '\n\033[1m=== %s ===\033[0m\n' "$*"; }

step "1. Python differential checks + fuzz-corpus generation"
python3 refinement.py || fail=1

step "2. Lean proofs (Add.lean, FuzzVectors.lean, Conformance.lean)"
lake build || fail=1

step "3. Executable conformance run"
lake exe conformance || fail=1

step "4. Negative control: buggy models must be rejected"
neglog="$(mktemp)"
if lake env lean NegativeControl.lean >"$neglog" 2>&1; then
  echo "FAIL: the checker ACCEPTED a buggy model — the verification is vacuous."
  fail=1
else
  rejected="$(grep -c 'proved that the proposition' "$neglog")"
  echo "PASS: the checker rejected buggy claims (${rejected} rejection(s) recorded)."
  echo "      See NegativeControl.lean for the bugs and why they must fail."
fi
rm -f "$neglog"

step "Summary"
if [ "$fail" -eq 0 ]; then
  echo "ALL CHECKS PASSED"
else
  echo "SOME CHECKS FAILED"
fi
exit "$fail"
