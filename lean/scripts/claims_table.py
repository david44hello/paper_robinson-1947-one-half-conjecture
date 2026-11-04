#!/usr/bin/env python3
"""claims_table.py — the status of every printed claim of CLAIM_MAP.tsv, from the row statuses of CLAIMS.json (project root).
Version 0.30, 2026-11-04: --write / --check keep column 5 (status) of CLAIM_MAP.tsv equal to the audit.
Version 0.20, 2026-11-04: REQUIRED may name a registered fact or check (the claim IS that fact/check).
Version 0.10, 2026-11-04: first. Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Rule (CLAIM_MAP header): a claim's status is the WORST status of its REQUIRED rows (FAIL < not proved yet < PROVED
GIVEN < PROVED); its PROVED GIVEN list is the union of those rows' Fact/Check binders. SUPPORT rows do not change the
status. A claim whose plan column starts with "NOT COUNTED" is listed apart. A claim with no REQUIRED row and not NOT
COUNTED is an ERROR (every counted claim needs a row). Unknown row names are an ERROR (fail loudly).
A REQUIRED name that is a registered check (fact) makes the claim "checked by computer, NOT proved in Lean" ("published
fact, not formalized"), provided its other REQUIRED rows are PROVED or PROVED GIVEN.
Usage: claims_table.py CLAIM_MAP.tsv CLAIMS.json      prints a Markdown table + counts; exit 1 on any ERROR
       claims_table.py --write CLAIM_MAP.tsv CLAIMS.json   sets column 5 of every counted claim to its audit status
       claims_table.py --check CLAIM_MAP.tsv CLAIMS.json   exit 1 if column 5 differs from the audit status anywhere
       claims_table.py --test
"""
import json
import re
import sys

RANK = {'FAIL': 0, 'not proved yet': 1, 'PROVED GIVEN': 2, 'PROVED': 3}
NAME_RE = re.compile(r'[A-Za-z_][A-Za-z0-9_]*')


def base_status(status):
    """CLAIMS.json writes 'PROVED GIVEN <list>' and 'not proved yet; waits on ...': reduce to the rank key."""
    for key in ('PROVED GIVEN', 'not proved yet', 'FAIL', 'PROVED'):
        if status.startswith(key):
            return key
    raise ValueError(f'unknown status: {status!r}')


def read_claims(tsv_text):
    """(id, text, required names, plan) for every non-comment line with at least 5 TAB fields."""
    claims = []
    for line in tsv_text.splitlines():
        if not line.strip() or line.startswith('#'):
            continue
        fields = line.split('\t')
        if len(fields) < 5:
            raise ValueError(f'claim line with fewer than 5 fields: {line[:80]!r}')
        required = [tok for tok in NAME_RE.findall(fields[2])]
        claims.append((fields[0], fields[1], required, fields[4]))
    return claims


CHECK_STATUS = 'checked by computer, NOT proved in Lean'
FACT_STATUS = 'published fact, not formalized'


def claim_row(claim, rows, facts, checks):
    """(status, binders, errors) of one claim."""
    cid, _text, required, plan = claim
    if plan.startswith('NOT COUNTED'):
        return 'NOT COUNTED', [], []
    trust = [name for name in required if name in facts or name in checks]
    errors = [f'{cid}: unknown row {name}' for name in required if name not in rows and name not in trust]
    known = [rows[name] for name in required if name in rows]
    if not required:
        errors.append(f'{cid}: no REQUIRED row and not NOT COUNTED')
    if errors:
        return 'ERROR', [], errors
    status = min((base_status(row['status']) for row in known), key=RANK.get, default='PROVED')
    binders = sorted({b.split('.')[-1] for row in known for b in row['binders']} | set(trust))
    if RANK[status] >= RANK['PROVED GIVEN'] and trust:
        status = CHECK_STATUS if any(name in checks for name in trust) else FACT_STATUS
    return status, binders, []


def main_claims_table(tsv_text, claims_json):
    """Return (markdown lines, counts, errors)."""
    rows = {row['name']: row for row in claims_json['rows']}
    facts = {item['name'].split('.')[-1] for item in claims_json['facts']}
    checks = {item['name'].split('.')[-1] for item in claims_json['checks']}
    lines = ['| claim | status | given (facts and checks) | REQUIRED rows |', '|---|---|---|---|']
    counts, errors = {}, []
    for claim in read_claims(tsv_text):
        status, binders, errs = claim_row(claim, rows, facts, checks)
        errors += errs
        counts[status] = counts.get(status, 0) + 1
        lines.append(f'| {claim[0]} | {status} | {", ".join(binders) or "-"} | {", ".join(claim[2]) or "-"} |')
    return lines, counts, errors


def status_text(status, binders):
    """Column 5 text of a counted claim."""
    return f'{status} {", ".join(binders)}' if status == 'PROVED GIVEN' else status


def sync_status_column(tsv_text, claims_json):
    """Return (new TSV text, number of changed claims, errors): column 5 of each counted claim = its audit status."""
    rows = {row['name']: row for row in claims_json['rows']}
    facts = {item['name'].split('.')[-1] for item in claims_json['facts']}
    checks = {item['name'].split('.')[-1] for item in claims_json['checks']}
    out, changed, errors = [], 0, []
    for line in tsv_text.split('\n'):
        if not line.strip() or line.startswith('#'):
            out.append(line)
            continue
        claim = read_claims(line)[0]
        status, binders, errs = claim_row(claim, rows, facts, checks)
        errors += errs
        if status not in ('NOT COUNTED', 'ERROR'):
            fields = line.split('\t')
            want = status_text(status, [b for b in binders if status == 'PROVED GIVEN'])
            if fields[4] != want:
                fields[4] = want
                changed += 1
            line = '\t'.join(fields)
        out.append(line)
    return '\n'.join(out), changed, errors


def run_tests():
    data = {'rows': [{'name': 'a', 'status': 'PROVED', 'binders': []},
                     {'name': 'b', 'status': 'PROVED GIVEN FactX', 'binders': ['FactX']},
                     {'name': 'c', 'status': 'not proved yet; waits on a', 'binders': []}],
            'facts': [{'name': 'R.FactX'}], 'checks': [{'name': 'R.CheckY'}]}
    tsv = '# header\nC1\tx\ta, b\t\tplan\nC2\ty\ta\tb\tplan\nC3\tz\t\t\tNOT COUNTED (run)\nC4\tw\tb, c\t\tplan\n'
    lines, counts, errors = main_claims_table(tsv, data)
    assert counts == {'PROVED GIVEN': 1, 'PROVED': 1, 'NOT COUNTED': 1, 'not proved yet': 1}, counts
    assert '| C1 | PROVED GIVEN | FactX | a, b |' in lines and not errors
    _l, counts, errors = main_claims_table('C5\tq\tzz\t\tplan\nC6\tq\t\t\tplan\n', data)
    assert counts == {'ERROR': 2} and len(errors) == 2, (counts, errors)
    lines, counts, errors = main_claims_table('C7\tq\tCheckY, a\t\tplan\nC8\tq\tFactX\t\tplan\nC9\tq\tCheckY, c\t\tplan\n', data)
    assert counts == {CHECK_STATUS: 1, FACT_STATUS: 1, 'not proved yet': 1} and not errors, (counts, errors)
    new, changed, errors = sync_status_column('# h\nC1\tx\ta, b\t\told plan\nC3\tz\t\t\tNOT COUNTED (run)\n', data)
    assert changed == 1 and 'C1\tx\ta, b\t\tPROVED GIVEN FactX' in new and 'NOT COUNTED (run)' in new, new
    assert sync_status_column(new, data)[1] == 0
    print('PASS: claims_table.py (worst REQUIRED status, union of binders, NOT COUNTED apart, loud errors).')


def main():
    if sys.argv[1:] == ['--test']:
        run_tests()
        return 0
    if len(sys.argv) == 4 and sys.argv[1] in ('--write', '--check'):
        with open(sys.argv[2], encoding='utf-8') as tsv, open(sys.argv[3], encoding='utf-8') as js:
            new, changed, errors = sync_status_column(tsv.read(), json.load(js))
        for err in errors:
            print('ERROR:', err, file=sys.stderr)
        if sys.argv[1] == '--write' and not errors:
            with open(sys.argv[2], 'w', encoding='utf-8') as tsv:
                tsv.write(new)
            print(f'status column: {changed} claims updated')
        elif sys.argv[1] == '--check':
            print(f'status column: {changed} claims differ from the audit')
            return 1 if changed or errors else 0
        return 1 if errors else 0
    if len(sys.argv) != 3:
        print(__doc__, file=sys.stderr)
        return 2
    with open(sys.argv[1], encoding='utf-8') as tsv, open(sys.argv[2], encoding='utf-8') as js:
        lines, counts, errors = main_claims_table(tsv.read(), json.load(js))
    print('\n'.join(lines))
    print('\nCounts: ' + ', '.join(f'{k} {v}' for k, v in sorted(counts.items())))
    for err in errors:
        print('ERROR:', err, file=sys.stderr)
    return 1 if errors else 0


if __name__ == '__main__':
    sys.exit(main())
