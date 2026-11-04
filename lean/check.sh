#!/usr/bin/env bash
# Checks the Lean proof: downloads Mathlib's prebuilt files, builds the proof, audits every claim, prints the result.
# Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
set -euo pipefail
cd "$(dirname "$0")"
# CHECK_SKIP_CACHE_GET=1 is only for a maintainers' test that links an already built Mathlib; it must never download.
case ${CHECK_SKIP_CACHE_GET-} in
    "") lake exe cache get ;;
    1) echo "check.sh: CHECK_SKIP_CACHE_GET=1: not running lake exe cache get" ;;
    *) echo "check.sh: CHECK_SKIP_CACHE_GET must be unset or 1, not '$CHECK_SKIP_CACHE_GET'" >&2; exit 2 ;;
esac
lake build
LEAN_RUN_LOCK=none LEAN_RUN_GATE=none python3 scripts/audit.py
python3 scripts/final_gate.py Robinson/Paper/Statements.lean CLAIMS.json scripts/OPEN_ROWS.txt
