#!/usr/bin/env bash
# reproduce.sh - re-run the computer checks of "Robinson's (1947) one-half conjecture is true" (cited there as [Repo]).
## version 0.50 - 20261104 - usage line: quick checks take about 80 seconds (as the README says).
## version 0.40 - 20261104 - check labels name the lemma each check proves.
## version 0.30 - 20261104 - stored results re-computed with the shipped Program B files; one hash per file.
## version 0.20 - 20261104 - public copy: neutral file names; one P55 packet; stored results bound via programB/MANIFEST.json.
# Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
#
# Usage:  ./reproduce.sh                 quick checks only (about 80 seconds, one thread)
#         ./reproduce.sh --band 90-95    quick checks + Program B replay of ONE band (names: see BANDS below)
#         ./reproduce.sh --full          quick checks + Program B replay of all 11 bands (about 4 CPU hours)
#         ./reproduce.sh --rebuild ...   also rebuild Program A (C++) and compare with the frozen binary hashes
#                                        (bit-identical only with GCC 13.3.0 of Ubuntu 24.04; other compilers will FAIL)
#         ./reproduce.sh --verbose ...   also print every program's own output
#
# Interpreters (both default to python3; each is tested before use and the script stops loudly if a module is missing):
#   PYTHON      runs the exact rational checks          - needs sympy and mpmath
#   PYTHON_ARB  runs Program B (Arb ball arithmetic)    - needs python-flint, numpy and scipy
# ARB_MAX_CPU_SECONDS (optional) replaces each band's internal CPU budget (authors' values below) for slow machines.
# A budget can only turn a replay into a loud FAIL (unconfirmed leaves), never into a false PASS.
#
# This script writes NOTHING inside this folder: outputs go to stdout or to a mktemp directory removed on exit,
# and Python byte-code caching is switched off, so 'git status --porcelain' stays empty after a run.
# Needs bash >= 5 and GNU coreutils (sha256sum, mktemp); tested on Ubuntu 24.04.
# Exit status: 0 = every check passed; 1 = at least one check failed; 2 = setup error (missing tool or file).
set -uo pipefail

HERE="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
PYTHON="${PYTHON:-python3}"
PYTHON_ARB="${PYTHON_ARB:-python3}"
export PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMEXPR_NUM_THREADS=1
unset PYTHONOPTIMIZE PYTHONPATH      # the checks rely on Python 'assert'; -O would silently remove them

# band   stored result JSON (middle/results/)       low     high  objective  authors' internal CPU budget (s)
BANDS=(
  "50.3-55  HOLQ_JOINT_50p30_55_Arb001.json          503/10  55    JOINT      3500"
  "55-60    HOLQ_JOINT_55_60_Arb001.json             55      60    JOINT      3500"
  "60-70    HOLQ_JOINT_60_70_Arb001.json             60      70    JOINT      3500"
  "70-80    HOLQ_JOINT_70_80_Arb001.json             70      80    JOINT      5000"
  "80-90    HOLQ_JOINT_80_90_Arb001.json             80      90    JOINT      5000"
  "90-95    HOLQ_90_95_Arb001.json                   90      95    PLAIN      580"
  "95-100   HOLQ_95_100_Arb001.json                  95      100   PLAIN      580"
  "100-105  HOLQ_100_105_Arb002.json                 100     105   PLAIN      580"
  "105-115  HOLQ_105_115_Arb001.json                 105     115   PLAIN      580"
  "115-125  HOLQ_115_125_Arb001.json                 115     125   PLAIN      580"
  "125-135  HOLQ_125_135_Arb001.json                 125     135   PLAIN      580"
)

FAILURES=0
CHECKS=0
VERBOSE=0
REBUILD=0
WORK=""

die() { printf 'SETUP ERROR: %s\n' "$*" >&2; exit 2; }

usage() { sed -n '8,24p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; }

record() {          # $1 = PASS|FAIL, $2 = name, $3 = detail
    CHECKS=$((CHECKS + 1))
    [[ "$1" == PASS ]] || FAILURES=$((FAILURES + 1))
    printf '%-4s  %-58s  %s\n' "$1" "$2" "$3"
}

elapsed() {         # $1 = start EPOCHREALTIME; some locales print a decimal comma
    local start="${1/,/.}" stop="${EPOCHREALTIME/,/.}"
    awk -v start="$start" -v stop="$stop" 'BEGIN { printf "%.1f s", stop - start }'
}

run_check() {       # $1 = name, $2 = required stdout text, rest = command. PASS = exit 0 AND the text is printed.
    local name="$1" marker="$2" log status start
    shift 2
    log="$(mktemp "$WORK/log.XXXXXX")"
    start="$EPOCHREALTIME"
    (cd -- "$WORK" && "$@") > "$log" 2>&1
    status=$?
    if (( VERBOSE )); then sed 's/^/    | /' "$log"; fi
    if (( status == 0 )) && grep -qF -- "$marker" "$log"; then
        record PASS "$name" "($(elapsed "$start"))"
    else
        record FAIL "$name" "(exit $status; marker '$marker' $(grep -qF -- "$marker" "$log" && echo found || echo missing))"
        tail -n 25 "$log" | sed 's/^/    ! /' >&2
    fi
}

parse_arguments() {
    MODE=quick
    BAND=""
    while (( $# )); do
        case "$1" in
            --full) MODE=full ;;
            --band) [[ $# -ge 2 ]] || die "--band needs a band name"; MODE=band; BAND="$2"; shift ;;
            --rebuild) REBUILD=1 ;;
            --verbose) VERBOSE=1 ;;
            --help|-h) usage; exit 0 ;;
            *) usage >&2; die "unknown argument: $1" ;;
        esac
        shift
    done
    if [[ "$MODE" == band ]] && ! printf '%s\n' "${BANDS[@]}" | awk '{print $1}' | grep -qxF -- "$BAND"; then
        die "unknown band '$BAND'; known: $(printf '%s\n' "${BANDS[@]}" | awk '{print $1}' | tr '\n' ' ')"
    fi
}

require_python() {  # $1 = interpreter, rest = modules it must import
    local python="$1"
    shift
    command -v "$python" > /dev/null || die "interpreter not found: $python"
    if "$python" -B -c 'assert False' 2> /dev/null; then die "$python ignores assert statements (optimised mode)"; fi
    "$python" -B -c "import $(IFS=,; echo "$*")" 2> /dev/null \
        || die "$python cannot import: $* (set PYTHON / PYTHON_ARB to an interpreter that can)"
}

check_integrity() { # every certificate file must match MANIFEST.sha256 (README/LICENSE/report lines are not checked)
    local start="$EPOCHREALTIME" lines
    [[ -f "$HERE/MANIFEST.sha256" ]] || die "MANIFEST.sha256 missing"
    lines="$(grep -E '^[0-9a-f]{64}  (middle|near|far)/' "$HERE/MANIFEST.sha256")"
    if (cd -- "$HERE" && printf '%s\n' "$lines" | sha256sum --check --quiet --strict > /dev/null 2>&1); then
        record PASS "integrity: $(printf '%s\n' "$lines" | wc -l) certificate files match MANIFEST.sha256" "($(elapsed "$start"))"
    else
        record FAIL "integrity: certificate files vs MANIFEST.sha256" "(run: sha256sum -c MANIFEST.sha256)"
    fi
}

check_stored_results() {    # each stored Program B result: confirmed, complete, bound to its tree's sha256
    run_check "middle Lemma 7.6: 11 stored results confirmed + bound to trees" "STORED RESULTS BOUND" \
        "$PYTHON" -B - "$HERE" "${BANDS[@]}" <<'PY'
import hashlib, json, sys
from pathlib import Path
here, rows = Path(sys.argv[1]), [row.split() for row in sys.argv[2:]]
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
leaves = 0
for band, result_name, *_ in rows:
    result = json.loads((here/'middle/results'/result_name).read_text())
    assert result['status'] == 'INDEPENDENT_BAND_CONFIRMED' and result['source_status'] == 'PASS', band
    assert result['confirmed_leaves'] == result['leaves'] and result['unconfirmed_leaves'] == 0, band
    assert result['source_pending_boxes'] == 0 and result['unconfirmed'] == [], band
    assert result['confirmed_root_fraction_exact'] == '1', band
    assert result['source_sha256'] == sha(here/'middle/trees'/band/'cover.tree'), band
    leaves += result['confirmed_leaves']
print(f'STORED RESULTS BOUND: {len(rows)} bands, {leaves} confirmed leaves')
PY
}

check_result_hashes() {     # stored results record the sha256 of the Program B sources + P55 packet they ran with
    run_check "middle: stored results' Program B + P55 hashes = MANIFEST.json" "RESULT HASHES BOUND" \
        "$PYTHON" -B - "$HERE" "${BANDS[@]}" <<'PY'
import hashlib, json, sys
from pathlib import Path
here, rows = Path(sys.argv[1]), [row.split() for row in sys.argv[2:]]
folder, packet = here/'middle/programB', 'HOLQ_joint_support_P55.json'
shipped = json.loads((folder/'MANIFEST.json').read_text())['files_sha256']
files_here = {path.name for path in folder.iterdir() if path.is_file()} - {'MANIFEST.json'}
assert set(shipped) == files_here, 'MANIFEST.json does not list exactly the files in middle/programB/'
for name, digest in shipped.items():
    assert hashlib.sha256((folder/name).read_bytes()).hexdigest() == digest, name
for band, result_name, _low, _high, kind, _budget in rows:
    result = json.loads((here/'middle/results'/result_name).read_text())
    for name, digest in result['own_source_hashes'].items():
        assert shipped[name] == digest, (band, name)
    if kind == 'JOINT':
        assert result['cap_packet_sha256'] == shipped[packet], band
    else:
        assert 'cap_packet_sha256' not in result, band
print(f'RESULT HASHES BOUND: {len(shipped)} Program B files match MANIFEST.json;',
      f'{len(rows)} stored results were computed with them')
PY
}

regenerate_S135() {         # author program must regenerate the stored certificate byte for byte
    "$PYTHON" -B "$HERE/far/check_sector135.py" --test --output "$WORK/S135_regenerated.json" \
        && cmp "$WORK/S135_regenerated.json" "$HERE/far/S135_certificate.json" && echo "certificate byte-identical"
}

run_quick_checks() {
    local near="$HERE/near" far="$HERE/far" middle="$HERE/middle"
    echo "== Quick checks (exact rational arithmetic; PYTHON=$PYTHON)"
    check_integrity
    run_check "near Lemmas 4.3, 4.5: check_B8_b.py (72 + 410 coefficients)" '"pass_certificate": true' \
        "$PYTHON" -B "$near/check_B8_b.py" --test
    run_check "near Lemmas 4.3, 4.5: check_B8_a.py (second program)" '"status": "INDEPENDENT EXACT PASS"' \
        "$PYTHON" -B "$near/check_B8_a.py" --test --radius 21/100 --cells 320
    run_check "near Lemma 4.8: check_B9_b.py (256 cells)" '"pass_certificate": true' \
        "$PYTHON" -B "$near/check_B9_b.py" --test --radius 17/80 --cells 256
    run_check "near Lemma 4.8: check_B9_a.py (320 cells, second program)" '"status": "INDEPENDENT EXACT PASS"' \
        "$PYTHON" -B "$near/check_B9_a.py" --test --radius 17/80 --cells 320
    run_check "far Lemmas 6.2, 6.4: check_sector135.py regenerates certificate" 'certificate byte-identical' \
        regenerate_S135
    run_check "far Lemmas 6.2, 6.4: S135_check_b.py (second program)" '"status": "PASS"' \
        "$PYTHON" -B "$far/S135_check_b.py" --test --certificate "$far/S135_certificate.json"
    run_check "far Lemmas 6.2, 6.4: audit_S135.py (third check: own 207-cell cover, interval arithmetic)" 'S135 AUDIT PASS' \
        "$PYTHON" -B "$far/audit_S135.py"
    run_check "middle Section 7.2: check_HOLQ_joint_P.py (the matrix P)" 'PASS: own exact P/J' \
        "$PYTHON" -B "$middle/check_HOLQ_joint_P.py" --test --packet "$middle/programB/HOLQ_joint_support_P55.json"
    check_stored_results
    check_result_hashes
}

compare_replay() {  # $1 = fresh JSON, $2 = stored JSON: identical except cpu_seconds; the program/packet hashes
                    # must be those of middle/programB/MANIFEST.json
    "$PYTHON" -B - "$1" "$2" "$HERE/middle/programB/MANIFEST.json" <<'PY'
import json, sys
fresh, stored, manifest = (json.load(open(path)) for path in sys.argv[1:4])
shipped, packet = manifest['files_sha256'], 'HOLQ_joint_support_P55.json'
assert fresh['status'] == 'INDEPENDENT_BAND_CONFIRMED', fresh['status']
assert all(shipped[name] == digest for name, digest in fresh['own_source_hashes'].items()), 'fresh: unlisted sources'
if 'cap_packet_sha256' in fresh:
    assert fresh['cap_packet_sha256'] == shipped[packet], 'P55'
for record in (fresh, stored):
    record.pop('cpu_seconds')
assert fresh == stored, sorted(key for key in set(fresh) | set(stored) if fresh.get(key) != stored.get(key))
print('REPLAY MATCHES STORED:', fresh['status'], fresh['confirmed_leaves'], 'leaves', fresh['independent_box_checks'], 'box checks')
PY
}

replay_and_compare() {      # $1 = fresh JSON, $2 = stored JSON, rest = Program B command
    local fresh="$1" stored="$2"
    shift 2
    "$@" > /dev/null && compare_replay "$fresh" "$stored"
}

replay_band() {     # $1 = one BANDS row. Fresh Program B replay; must equal the stored result except cpu_seconds.
    local band result low high kind budget output program
    read -r band result low high kind budget <<< "$1"
    budget="${ARB_MAX_CPU_SECONDS:-$budget}"
    output="$WORK/replay_${band}.json"
    program=("$PYTHON_ARB" -B "$HERE/middle/programB/holq_peer_tree_arb.py")
    if [[ "$kind" == JOINT ]]; then
        program=("$PYTHON_ARB" -B "$HERE/middle/programB/holq_support_tree_arb.py" --support 4/5 1/2 JOINT_P55
                 --cap-packet "$HERE/middle/programB/HOLQ_joint_support_P55.json" --target 0)
    fi
    run_check "Program B replay $band ($kind, 128 bits, depth 8, budget ${budget} s)" "REPLAY MATCHES STORED" \
        replay_and_compare "$output" "$HERE/middle/results/$result" \
        "${program[@]}" --precision 128 --source "$HERE/middle/trees/$band/cover.tree" --low "$low" --high "$high" \
        --max-cpu-seconds "$budget" --max-depth 8 --output "$output"
}

rebuild_binary() {  # $1 = programA subfolder, $2 = original source name, $3 = sha256 of the frozen binary
    local folder="$HERE/middle/programA/$1" build="$WORK/build_$1" binary="programA_$1"
    mkdir -p "$build" && cp "$folder/checker.cpp" "$build/$2" || return 1
    g++ --version | head -n 1
    (cd -- "$build" && g++ -std=c++17 -O2 -fno-fast-math -Wall -Wextra "$2" -o "$binary") || return 1
    echo "$3  $build/$binary" | sha256sum --check --strict && echo "BINARY BIT-IDENTICAL"
}

run_rebuilds() {    # the frozen binaries that produced the trees were built from checker.cpp under these source names
    echo "== Program A rebuild (g++ -std=c++17 -O2 -fno-fast-math -Wall -Wextra)"
    command -v g++ > /dev/null || die "g++ not found (needed for --rebuild)"
    run_check "Program A JOINT v0.40 rebuild = frozen binary" "BINARY BIT-IDENTICAL" \
        rebuild_binary joint_v040 check_holq_support_taylor.cpp ca648df392da8df97f503ad0903f1da46ee8fe9a23585da45cd25f0041a368ec
    run_check "Program A PLAIN v0.60 rebuild = frozen binary" "BINARY BIT-IDENTICAL" \
        rebuild_binary plain_v060 check_holo_sector_taylor.cpp 7c93179bc22ba1b6aef4b32a97bb1b7ce793992e515904b1daf13f2e398134e8
}

run_replays() {     # $1 = band name, or ALL
    local row
    echo "== Program B replays (Arb ball arithmetic; PYTHON_ARB=$PYTHON_ARB)"
    for row in "${BANDS[@]}"; do
        if [[ "$1" == ALL || "$(awk '{print $1}' <<< "$row")" == "$1" ]]; then replay_band "$row"; fi
    done
}

main() {
    parse_arguments "$@"
    require_python "$PYTHON" sympy mpmath
    [[ "$MODE" == quick ]] || require_python "$PYTHON_ARB" flint numpy scipy
    WORK="$(mktemp -d)" || die "mktemp failed"
    trap 'rm -rf -- "$WORK"' EXIT
    run_quick_checks
    if (( REBUILD )); then run_rebuilds; fi
    if [[ "$MODE" == full ]]; then run_replays ALL; fi
    if [[ "$MODE" == band ]]; then run_replays "$BAND"; fi
    if (( FAILURES )); then
        echo "RESULT: FAIL - $FAILURES of $CHECKS checks failed"
        exit 1
    fi
    echo "RESULT: PASS - all $CHECKS checks passed"
}

main "$@"; exit
