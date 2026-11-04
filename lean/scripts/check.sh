#!/usr/bin/env bash
# check.sh — the full gate of the Lean project: token policy, shipped-text policy, build, and the claim audit.
# Version 0.30.
#
# Usage:  scripts/check.sh           work gate: the scans below; build; audit (no FAIL row; unproved rows are allowed)
#         scripts/check.sh --final   freeze gate: as above, and the unproved rows are exactly those of scripts/OPEN_ROWS.txt
#         scripts/check.sh --scan    the scans only (no Lean)
#         scripts/check.sh --test    self-test of this gate and of every other script here (no Lean)
# Scans:  (1) tokens: no proof hole or forbidden construct in any Lean file; in Statements.lean the placeholder only as
#             the whole body of a row (scripts/final_gate.py);
#         (2) shipped text: no house name, machine path or working note in any shipped file (all files of the project
#             except .lake/, .git/, versions/). House names come from the roster file named by the REQUIRED variable CHECK_ROSTER.
#             Exempt, and printed as NOTE: the DEFAULT_ lines of scripts/ (machine-local defaults that can be overridden).
# Every Lean/lake command goes through scripts/lean_run.sh (the shared compile lock and the priority gate).
# Exit: 0 PASS | 1 a policy, build or audit failure | 2 usage/setup error
set -euo pipefail

project_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
statements=Robinson/Paper/Statements.lean
forbidden='sorry|admit|sorryAx|axiom|native_decide|implemented_by|extern|unsafe|debug[.]skipKernelTC|csimp'
author_name=Dave                      # the paper author's name is allowed (author and copyright lines)
machine_paths='/[h]ome/|/[t]mp/dave'  # the bracket keeps this line from matching itself
working_notes='(?i)\b(?:[r]eview\w*|[v]erifier\w*|[a]vatar\w*|[s]print\w*|[t]odo|[f]ixme|[x]xx)\b'
exempt_line='^\./scripts/[^:]+:[0-9]+:\s*(readonly\s+)?DEFAULT_[A-Z_]+\s*='
# rg: a later --glob wins over an earlier one, so the exclusions come after any '*.lean'.
not_shipped=(--glob '!.lake/**' --glob '!.git/**' --glob '!versions/**')

# (1) Deliberately conservative: forbidden words in comments/strings also fail.
scan_sources() {
    local source_dir=$1 status=0 failed=0
    [[ -d "$source_dir" ]] || { echo "ERROR: missing source directory: $source_dir" >&2; return 2; }
    (cd "$source_dir" && rg --hidden --no-ignore -n -w --glob '*.lean' "${not_shipped[@]}" --glob "!$statements" \
        "$forbidden" .) || status=$?
    if (( status == 0 )); then
        echo 'ERROR: proof hole or forbidden construct in a Lean file.' >&2
        failed=1
    elif (( status != 1 )); then return "$status"; fi
    if [[ -f "$source_dir/$statements" ]]; then
        # Statements.lean: every forbidden word but the placeholder, whose placement final_gate.py checks.
        status=0
        (cd "$source_dir" && rg -n -w "${forbidden#sorry|}" "$statements") || status=$?
        if (( status == 0 )); then
            echo "ERROR: forbidden construct in $statements." >&2
            failed=1
        elif (( status != 1 )); then return "$status"; fi
    fi
    return "$failed"
}

# The house names of the roster (lines "Name | role | ..."), without trailing digits and without the author's name.
roster_names() {
    local roster=$1 names
    [[ -r "$roster" ]] || { echo "ERROR: cannot read the roster file: $roster (set CHECK_ROSTER)" >&2; return 2; }
    names=$(grep -v '^#' "$roster" | awk -F'|' 'NF >= 2 { gsub(/[[:space:]]/, "", $1); sub(/[0-9]+$/, "", $1); print $1 }' \
        | grep -E '^[A-Za-z]+$' | grep -vx "$author_name" | sort -u | paste -sd '|')
    (( $(tr '|' '\n' <<< "$names" | wc -l) >= 3 )) || { echo "ERROR: fewer than 3 names in the roster file: $roster" >&2; return 2; }
    echo "$names"
}

# (2) House names (case-sensitive, optional digits), machine paths, working notes (any case).
scan_shipped_text() {
    local source_dir=$1 roster=$2 names hits status=0
    names=$(roster_names "$roster") || return 2
    hits=$(cd "$source_dir" && rg --hidden --no-ignore -n "${not_shipped[@]}" \
        -e "\\b(?:$names)[0-9]*\\b" -e "$machine_paths" -e "$working_notes" .) || status=$?
    (( status <= 1 )) || return "$status"
    local exempt offending
    exempt=$(grep -E "$exempt_line" <<< "$hits" || true)
    offending=$(grep -vE "$exempt_line" <<< "$hits" | grep -v '^$' || true)
    [[ -z $exempt ]] || sed 's/^/NOTE (machine-local default, exempt): /' <<< "$exempt"
    if [[ -n $offending ]]; then
        printf '%s\n' "$offending"
        echo "ERROR: house name, machine path or working note in shipped files ($(wc -l <<< "$offending") lines)." >&2
        return 1
    fi
}

run_tests() (
    local fixture
    fixture=$(mktemp -d "$project_dir/scripts/.check-test.XXXXXX")
    trap 'python3 -c "import shutil, sys; shutil.rmtree(sys.argv[1])" "$fixture"' EXIT
    local tree="$fixture/tree" roster="$fixture/roster.txt"   # the roster stays outside the scanned tree
    mkdir -p "$tree/Robinson/Paper" "$tree/.lake/packages/dependency" "$tree/versions" "$tree/scripts"
    printf 'theorem good : True := True.intro\n' > "$tree/Robinson/Basic.lean"
    printf 'theorem row_open : True := by\n  sorry\n' > "$tree/$statements"
    printf 'theorem dependency_result : True := by sorry\n' > "$tree/.lake/packages/dependency/Basic.lean"
    printf 'axiom old_assumption : True\ntheorem old_gap : True := by sorry\n' > "$tree/versions/Old.lean"
    printf '%s\n' '# roster' 'Alpha | role | 1 | 1' 'Alpha01 | ext | 1 | 1' 'Beta02 | ext | 1 | 1' 'Gamma | x | 1 | 1' \
        'Dave | author | 1 | 1' > "$roster"
    printf '/- Paper author: Dave Goel. Copyright (C) Dave Goel 2026--now. Alphabet, Betamax. -/\n' > "$tree/Robinson/Head.lean"
    scan_sources "$tree" || { echo 'TEST FAILED: rejected a clean tree.' >&2; return 1; }
    scan_shipped_text "$tree" "$roster" > /dev/null || { echo 'TEST FAILED: shipped text rejected a clean tree.' >&2; return 1; }
    local bad_source
    for bad_source in 'theorem hole : True := by sorry' 'theorem hole : True := by admit' \
        'axiom invented : True' 'axiom\ninvented : True' 'def hidden := sorryAx' \
        'example : True := by native_decide' '@[implemented_by replacement] def original := 1' \
        '@[extern "foreign"] opaque external : Nat' 'unsafe def unchecked := 1' \
        'set_option debug.skipKernelTC true' '@[csimp] theorem compiled_replacement : True := True.intro' \
        '-- NEVER an axiom (a comment also fails)'; do
        printf '%b\n' "$bad_source" > "$tree/Robinson/Basic.lean"
        if scan_sources "$tree" >/dev/null 2>&1; then
            echo "TEST FAILED: accepted $bad_source" >&2; return 1
        fi
    done
    printf 'theorem good : True := True.intro\n' > "$tree/Robinson/Basic.lean"
    printf 'theorem row_open : True := by\n  admit\n' > "$tree/$statements"
    if scan_sources "$tree" >/dev/null 2>&1; then
        echo 'TEST FAILED: accepted admit in Statements.' >&2; return 1
    fi
    printf 'theorem row_open : True := by\n  sorry\n' > "$tree/$statements"
    local bad_text
    # The quotes are split ('re''viewer') so that this file does not match the scan it tests.
    for bad_text in 'checked by Alpha' 'see Beta02 mail' 'ask alpha?' 'at /ho''me/x/y' 'in /t''mp/dave/a' \
        'read by a re''viewer' 'Veri''fier pass' 'TO''DO later' 'ava''tar notes'; do
        printf '%s\n' "-- $bad_text" > "$tree/Robinson/Note.lean"
        [[ $bad_text == 'ask alpha?' ]] && continue   # names are case-sensitive: lower-case "alpha" is a word
        if scan_shipped_text "$tree" "$roster" >/dev/null 2>&1; then
            echo "TEST FAILED: shipped text accepted: $bad_text" >&2; return 1
        fi
    done
    printf -- '-- ask alpha?\n' > "$tree/Robinson/Note.lean"
    scan_shipped_text "$tree" "$roster" > /dev/null || { echo 'TEST FAILED: lower-case word taken as a name.' >&2; return 1; }
    printf 'DEFAULT_LOCK=/t''mp/dave/x/Alpha01/a.lock\n' > "$tree/scripts/run.sh"
    local notes
    notes=$(scan_shipped_text "$tree" "$roster") || { echo 'TEST FAILED: a DEFAULT_ line in scripts/ was not exempt.' >&2; return 1; }
    [[ $notes == *"NOTE (machine-local default, exempt)"* ]] || { echo 'TEST FAILED: exempt line not printed.' >&2; return 1; }
    printf 'x\nDEFAULT_LOCK=/t''mp/dave/x/a.lock\n' > "$tree/Robinson/Note.lean"
    if scan_shipped_text "$tree" "$roster" >/dev/null 2>&1; then
        echo 'TEST FAILED: a DEFAULT_ line outside scripts/ was exempt.' >&2; return 1
    fi
    printf -- '-- fine\n' > "$tree/Robinson/Note.lean"
    printf 'see Gamma\n' > "$tree/.lake/packages/dependency/README"
    scan_shipped_text "$tree" "$roster" > /dev/null || { echo 'TEST FAILED: .lake/ was scanned.' >&2; return 1; }
    if scan_shipped_text "$tree" "$fixture/missing-roster.txt" >/dev/null 2>&1; then
        echo 'TEST FAILED: accepted a missing roster file.' >&2; return 1
    fi
    if main --sloppy >/dev/null 2>&1; then
        echo 'TEST FAILED: accepted an unknown mode.' >&2; return 1
    fi
    local script
    for script in final_gate.py audit.py; do
        python3 "$project_dir/scripts/$script" --test >/dev/null || { echo "TEST FAILED: $script --test" >&2; return 1; }
    done
    for script in lean_run.sh kernel_replay.sh; do
        "$project_dir/scripts/$script" --test >/dev/null 2>&1 || { echo "TEST FAILED: $script --test" >&2; return 1; }
    done
    echo 'PASS: token policy, shipped-text policy, roster, exemptions and the other scripts self-tests.'
)

run_lean_steps() {
    local runner=$project_dir/scripts/lean_run.sh
    # Fail before the real build if Mathlib would need compilation.
    "$runner" lake --no-build build mathlib/Mathlib
    "$runner" lake build
    nice -n 19 python3 scripts/audit.py
}

main() {
    local mode
    case "${1:-}" in
        --test) [[ $# == 1 ]] || return 2; run_tests; return ;;
        --final) [[ $# == 1 ]] || return 2; mode=final ;;
        --scan) [[ $# == 1 ]] || return 2; mode=scan ;;
        '') [[ $# == 0 ]] || return 2; mode=work ;;
        *) echo "Usage: $0 [--test | --scan | --final]   (no flag = the work gate)" >&2; return 2 ;;
    esac
    cd "$project_dir"
    local failed=0
    scan_sources . || failed=1
    python3 scripts/final_gate.py --placement "$statements" || failed=1
    scan_shipped_text . "${CHECK_ROSTER:?check.sh: set CHECK_ROSTER (the roster file of names kept out of shipped text)}" || failed=1
    if [[ $mode == scan ]]; then
        (( failed == 0 )) && echo 'PASS (scan): token policy and shipped-text policy.'
        return "$failed"
    fi
    run_lean_steps || failed=1
    if [[ $mode == final ]]; then
        python3 scripts/final_gate.py "$statements" CLAIMS.json scripts/OPEN_ROWS.txt || failed=1
    fi
    (( failed == 0 )) || { echo "FAIL ($mode): see the errors above." >&2; return 1; }
    echo "PASS ($mode): project builds; token and shipped-text policies pass; no FAIL row in the audit."
}

main "$@"
