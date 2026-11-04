#!/usr/bin/env python3
"""DATA-only Arb replay of the C++ HOLQ half-chart certificate tree.
Version 0.20 — Program B, 20261101__22:56 ET. Accept optional informational
leaf-method tags; exact root/partition/completeness controls fail loudly.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import time
from tempfile import TemporaryDirectory
from flint import arb, ctx
from fourlog_centered import rational_ball
from fourlog_arb_box import UnresolvedEnclosure
from holq_local_arb import check_endpoints


def exact_number(token):
    return Fraction.from_float(float.fromhex(token)) if '0x' in token.lower() else Fraction(token)


def volume(box):
    result = Fraction(1)
    for lower, upper in box:
        if not lower < upper:
            raise ValueError('nonpositive source rectangle')
        result *= upper-lower
    return result


def validate_root(box, low, high):
    pi = arb.pi()
    required = [(arb(0), pi/2), (-pi/2, pi/2), (-pi, pi), (arb(low)*pi/180, arb(high)*pi/180)]
    for (lower, upper), (required_lower, required_upper) in zip(box, required):
        if not (rational_ball(lower) <= required_lower and rational_ball(upper) >= required_upper):
            raise ValueError('ROOT does not enclose the full agreed HOLQ half-chart')
    volume(box)


def verify_leaf(box, deadline, max_depth):
    pending, nodes = [(box, 0)], 0
    while pending:
        if time.process_time() >= deadline:
            return False, nodes, 'CPU_BUDGET'
        current, depth = pending.pop()
        nodes += 1
        try:
            report = check_endpoints(current)
        except UnresolvedEnclosure:
            report = {'status': 'INCOMPLETE'}
        if report['status'] == 'INDEPENDENT_LOCAL_BOX_CONFIRMED':
            continue
        if depth >= max_depth:
            return False, nodes, 'DEPTH_LIMIT'
        dimension = max(range(4), key=lambda index: current[index][1]-current[index][0])
        middle = sum(current[dimension])/2
        left, right = list(map(list, current)), list(map(list, current))
        left[dimension][1], right[dimension][0] = middle, middle
        pending.extend([(right, depth+1), (left, depth+1)])
    return True, nodes, None


def replay(path, low, high, budget, max_depth):
    started, deadline = time.process_time(), time.process_time()+budget
    frontier, seen, pending_rows = {}, set(), set()
    confirmed, unconfirmed, checked_boxes = Fraction(0), Fraction(0), 0
    counts = {'nodes': 0, 'leaves': 0, 'confirmed_leaves': 0, 'unconfirmed_leaves': 0}
    footer, root, declared_status = False, None, None
    unresolved = []
    with path.open() as stream:
        for raw in stream:
            fields = raw.split()
            if not fields:
                continue
            kind = fields[0]
            if kind == 'ROOT':
                if root is not None or len(fields) != 9:
                    raise ValueError('duplicate or malformed ROOT')
                root = [[exact_number(fields[index]), exact_number(fields[index+1])] for index in range(1, 9, 2)]
                validate_root(root, low, high)
                frontier[1], seen = (root, 0), {1}
                continue
            if root is None:
                raise ValueError('record before ROOT')
            if kind in ['S', 'L']:
                if footer or pending_rows:
                    raise ValueError('proof nodes after pending/footer records')
                identifier = int(fields[1])
                if identifier not in frontier:
                    raise ValueError('unknown, duplicate or previously consumed proof node')
                box, depth = frontier.pop(identifier)
                counts['nodes'] += 1
                if kind == 'S':
                    if len(fields) != 6:
                        raise ValueError('malformed split')
                    dimension, middle, left_id, right_id = int(fields[2]), exact_number(fields[3]), int(fields[4]), int(fields[5])
                    if not 0 <= dimension < 4 or left_id == right_id or left_id in seen or right_id in seen:
                        raise ValueError('invalid split dimension/child identifiers')
                    if not box[dimension][0] < middle < box[dimension][1]:
                        raise ValueError('split point is outside parent interior')
                    left, right = list(map(list, box)), list(map(list, box))
                    left[dimension][1], right[dimension][0] = middle, middle
                    frontier[left_id], frontier[right_id] = (left, depth+1), (right, depth+1)
                    seen.update([left_id, right_id])
                else:
                    if len(fields) not in [3, 4]:
                        raise ValueError('malformed leaf')
                    counts['leaves'] += 1
                    # fields[2] is an untrusted claim, NEVER a positivity decision.
                    valid, checks, reason = verify_leaf(box, deadline, max_depth)
                    checked_boxes += checks
                    if valid:
                        confirmed += volume(box)
                        counts['confirmed_leaves'] += 1
                    else:
                        unconfirmed += volume(box)
                        counts['unconfirmed_leaves'] += 1
                        unresolved.append({'id': identifier, 'reason': reason})
                continue
            if kind == 'P':
                if footer or len(fields) != 11:
                    raise ValueError('malformed or late pending record')
                identifier, depth = int(fields[1]), int(fields[2])
                declared_box = [[exact_number(fields[index]), exact_number(fields[index+1])] for index in range(3, 11, 2)]
                if identifier in pending_rows or identifier not in frontier or frontier[identifier] != (declared_box, depth):
                    raise ValueError('pending record disagrees with reconstructed partition')
                pending_rows.add(identifier)
                continue
            if kind == 'END':
                if footer or len(fields) != 5:
                    raise ValueError('duplicate/malformed END')
                declared_status = fields[1]
                if int(fields[2]) != counts['nodes'] or int(fields[3]) != counts['leaves']:
                    raise ValueError('source counters mismatch')
                if pending_rows != set(frontier):
                    raise ValueError('source omitted or invented a pending box')
                if declared_status != ('PASS' if not frontier else 'INCOMPLETE'):
                    raise ValueError('source completeness claim contradicts partition')
                footer = True
                continue
            if kind == 'CPU' and footer:
                continue
            raise ValueError('unknown source record')
    if root is None or not footer:
        raise ValueError('source tree has no complete partition footer')
    pending_volume = sum((volume(box) for box, _ in frontier.values()), Fraction(0))
    root_volume = volume(root)
    if confirmed+unconfirmed+pending_volume != root_volume:
        raise ValueError('exact source-volume accounting does not sum to ROOT')
    return {'status': 'INDEPENDENT_BAND_CONFIRMED' if not frontier and not unresolved else 'INCOMPLETE',
            'source_status': declared_status, **counts, 'source_pending_boxes': len(frontier),
            'independent_box_checks': checked_boxes, 'unconfirmed': unresolved,
            'confirmed_root_fraction_exact': str(confirmed/root_volume),
            'confirmed_root_fraction': float(confirmed/root_volume),
            'unconfirmed_leaf_fraction_exact': str(unconfirmed/root_volume),
            'source_pending_fraction_exact': str(pending_volume/root_volume),
            'cpu_seconds': time.process_time()-started, 'source_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


def controls(source, low, high):
    root_line = source.read_text().splitlines()[0]
    fields = root_line.split()
    root = [[exact_number(fields[index]), exact_number(fields[index+1])] for index in range(1, 9, 2)]
    with TemporaryDirectory(prefix='holq-replay-') as temporary:  # system temp folder (TMPDIR); removed on exit
        path = Path(temporary)/'control.tree'
        pending = 'P 1 0 '+' '.join(fields[1:])+'\n'
        path.write_text(root_line+'\n'+pending+'END INCOMPLETE 0 0 0\n')
        result = replay(path, low, high, 1, 0)
        assert result['status'] == 'INCOMPLETE' and result['source_pending_boxes'] == 1
        middle = sum(root[0])/2
        malformed = [root_line+'\n'+pending+'END PASS 0 0 0\n',
                     root_line+f'\nS 1 0 {middle} 2 3\nS 1 0 {middle} 4 5\n',
                     root_line+'\nEND INCOMPLETE 0 0 0\n']
        for text in malformed:
            path.write_text(text)
            try:
                replay(path, low, high, 1, 0)
            except ValueError:
                continue
            raise AssertionError('invalid completeness/duplicate/pending record accepted')
    print('PASS: whole-root pending control and rejection of false PASS, duplicate node, omitted frontier')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--precision', type=int, required=True)
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--low', type=int, required=True)
    parser.add_argument('--high', type=int, required=True)
    parser.add_argument('--max-cpu-seconds', type=float, required=True)
    parser.add_argument('--max-depth', type=int, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--test', action='store_true')
    arguments = parser.parse_args()
    ctx.prec, ctx.threads = arguments.precision, 1
    if not 0 < arguments.low < arguments.high <= 180 or arguments.max_cpu_seconds <= 0 or arguments.max_depth < 0:
        parser.error('invalid band or budget')
    if arguments.test:
        controls(arguments.source, arguments.low, arguments.high)
        return
    result = replay(arguments.source, arguments.low, arguments.high, arguments.max_cpu_seconds, arguments.max_depth)
    directory = Path(__file__).resolve().parent
    result['own_source_hashes'] = {name: hashlib.sha256((directory/name).read_bytes()).hexdigest() for name in
                                  [Path(__file__).name, 'holq_local_arb.py', 'arb_differential.py', 'fourlog_arb_box.py']}
    arguments.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
