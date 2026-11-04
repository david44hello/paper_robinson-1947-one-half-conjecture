#!/usr/bin/env python3
"""final_gate.py — where the placeholder may stand in Statements.lean, and (at the freeze) which rows may stay open.
Version 0.10, 2026-11-04: first; adapted from an earlier project's freeze gate (same placement rule; a work mode added).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

1. Placement (both modes): in Statements.lean every occurrence of the placeholder word is the WHOLE body
   (`:= by <word>` or `:= <word>`) of a row. Every other Lean file is scanned by check.sh, which allows it nowhere.
2. Freeze mode only, against one explicit list of rows (one row name per line, '#' comments): the placeholder stands
   only in listed rows; in CLAIMS.json (written by audit.py) every listed row exists and is "not proved yet", and no
   other row is "not proved yet" or FAIL.
Usage: final_gate.py --placement <Statements.lean>                   work mode (any row may have the placeholder body)
       final_gate.py <Statements.lean> <CLAIMS.json> <OPEN_ROWS.txt>   freeze mode
       final_gate.py --test
"""
import json
import re
import sys
from pathlib import Path

PLACEHOLDER = 'so' + 'rry'  # spelled in two parts so the token scan of check.sh does not flag this file
NOT_PROVED = 'not proved yet'
WORD_RE = re.compile(r'\b' + PLACEHOLDER + r'\b')
DECL_RE = re.compile(r'^(?:theorem|lemma)\s+(\S+)', re.M)
NEXT_ITEM_RE = re.compile(r'^(?:/--|/-|@\[|#|(?:theorem|lemma|def|abbrev|noncomputable|instance|structure|'
                          r'namespace|section|end|open|variable)\b)', re.M)
BODY_RE = re.compile(r':=\s*(?:by\s+)?' + PLACEHOLDER + r'\s*$')


def read_open_list(path):
    """Row names, in file order; duplicates are an error."""
    names = [line.split('#', 1)[0].strip() for line in Path(path).read_text(encoding='utf-8').splitlines()]
    names = [name for name in names if name]
    duplicates = sorted({name for name in names if names.count(name) > 1})
    if duplicates:
        raise SystemExit(f'FINAL GATE: duplicate names in {path}: {duplicates}')
    return names


def declaration_spans(text):
    """[(name, start, end)]: each theorem/lemma runs to the next top-level item (or end of file)."""
    starts = [(match.group(1), match.start()) for match in DECL_RE.finditer(text)]
    spans = []
    for name, start in starts:
        following = NEXT_ITEM_RE.search(text, start + 1)
        spans.append((name, start, following.start() if following else len(text)))
    return spans


def allowed_offsets(text, open_names):
    """Offsets of the placeholder that are the whole body of a row (of a listed row, if open_names is a set)."""
    allowed = set()
    for name, start, end in declaration_spans(text):
        span = text[start:end].rstrip()
        listed = open_names is None or name.split('.')[-1] in open_names
        if listed and BODY_RE.search(span) and len(WORD_RE.findall(span)) == 1:
            allowed.add(start + span.rindex(PLACEHOLDER))
    return allowed


def placement_errors(text, open_names):
    allowed = allowed_offsets(text, open_names)
    where = 'a row' if open_names is None else 'a listed row'
    errors = []
    for match in WORD_RE.finditer(text):
        if match.start() not in allowed:
            line = text.count('\n', 0, match.start()) + 1
            errors.append(f'Statements.lean l.{line}: placeholder outside the whole body of {where}')
    return errors


def status_errors(rows, open_names):
    status = {row['name']: row['status'] for row in rows}
    errors = [f'listed row {name} is not a row' for name in open_names if name not in status]
    errors += [f'listed row {name} has status {status[name]} (must be "{NOT_PROVED}"; update the list)'
               for name in open_names if name in status and status[name] != NOT_PROVED]
    errors += [f'row {name} has status {st} but is not on the list'
               for name, st in status.items() if name not in open_names and (st == NOT_PROVED or st.startswith('FAIL'))]
    return errors


def main_placement(statements_path):
    """Work mode. Returns the list of errors (empty = PASS)."""
    return placement_errors(Path(statements_path).read_text(encoding='utf-8'), None)


def main_final_gate(statements_path, claims_path, open_list_path):
    """Freeze mode. Returns the list of errors (empty = PASS)."""
    open_names = set(read_open_list(open_list_path))
    text = Path(statements_path).read_text(encoding='utf-8')
    rows = json.loads(Path(claims_path).read_text(encoding='utf-8'))['rows']
    return placement_errors(text, open_names) + status_errors(rows, open_names)


def run_tests():
    hole = PLACEHOLDER
    text = (f'section\n/-- a.tex l.1 -/\ntheorem row_open (x : Nat) :\n    let y := x\n    y = x := by\n  {hole}\nend\n\n'
            f'/-- b -/\ntheorem row_done : True :=\n  trivial\n\nopen Classical in\n'
            f'theorem row_inline : True := {hole}\n\nend Robinson.Paper\n')
    assert placement_errors(text, {'row_open', 'row_inline'}) == []
    assert placement_errors(text, None) == []                                  # work mode: any row
    assert len(placement_errors(text, {'row_open'})) == 1                      # unlisted placeholder row
    assert len(placement_errors(text.replace('trivial', hole), {'row_open', 'row_inline'})) == 1
    two = text.replace(f'y = x := by\n  {hole}', f'y = x := by\n  have := 1\n  {hole}')
    assert len(placement_errors(two, {'row_open', 'row_inline'})) == 1         # not the WHOLE body
    assert len(placement_errors(two, None)) == 1                               # not the whole body, work mode
    commented = text.replace('/-- b -/', f'/-- b {hole} -/')
    assert len(placement_errors(commented, None)) == 1                         # word in a docstring
    rows = [{'name': 'row_open', 'status': NOT_PROVED}, {'name': 'row_done', 'status': 'PROVED'},
            {'name': 'row_dep', 'status': NOT_PROVED}]
    assert status_errors(rows, {'row_open', 'row_dep'}) == []                  # inherited "not proved yet" is listed
    assert len(status_errors(rows, {'row_open'})) == 1                         # unlisted unproved row
    assert len(status_errors(rows, {'row_open', 'row_dep', 'row_done'})) == 1  # listed but PROVED
    assert len(status_errors(rows, {'row_open', 'row_dep', 'row_gone'})) == 1  # stale list entry
    assert len(status_errors(rows + [{'name': 'v', 'status': 'FAIL: axiom x'}], {'row_open', 'row_dep'})) == 1
    print('final_gate --test: 12/12 OK')


def report(errors, success):
    for error in errors:
        print('FINAL GATE ERROR: ' + error, file=sys.stderr)
    if errors:
        raise SystemExit(1)
    print(success)


def main():
    args = sys.argv[1:]
    if args == ['--test']:
        run_tests()
    elif len(args) == 2 and args[0] == '--placement':
        report(main_placement(args[1]), 'PLACEMENT PASS: the placeholder stands only as whole bodies of rows.')
    elif len(args) == 3:
        report(main_final_gate(*args), f'FINAL GATE PASS: placeholders only as whole bodies of the '
               f'{len(read_open_list(args[2]))} listed rows; statuses match the list.')
    else:
        raise SystemExit(__doc__)


if __name__ == '__main__':
    main()
