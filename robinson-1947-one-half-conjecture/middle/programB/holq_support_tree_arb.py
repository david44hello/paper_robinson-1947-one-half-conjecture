#!/usr/bin/env python3
"""Independent exact-partition Arb replay for generic HOLQ support.
Version 0.30 — Program B, 20261102__09:50 EST. Add a50.30–55 exact-degree
root control and reject malformed minimum metadata; JOINT_P55 remains bound.
"""
import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
from tempfile import TemporaryDirectory
import time
from flint import arb, ctx
from fourlog_arb_box import UnresolvedEnclosure
from holq_peer_tree_arb import exact_number, volume
from holq_support_arb import Support, check_endpoints
from holq_joint_cap_arb import JointCap
from fourlog_centered import rational_ball


def validate_root(box, low, high):
    pi = arb.pi()
    required = [(arb(0), pi/2), (-pi/2, pi/2), (-pi, pi),
                (rational_ball(low)*pi/180, rational_ball(high)*pi/180)]
    for (lower, upper), (required_lower, required_upper) in zip(box, required):
        if not (rational_ball(lower) <= required_lower and rational_ball(upper) >= required_upper):
            raise ValueError('ROOT does not enclose the exact requested rational-degree half-chart')
    volume(box)


def verify_leaf(box, support, target, deadline, max_depth):
    pending, nodes = [(box, 0)], 0
    while pending:
        if time.process_time() >= deadline:
            return False, nodes, 'CPU_BUDGET'
        current, depth = pending.pop()
        nodes += 1
        try:
            report = check_endpoints(current, support, target)
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


def replay(path, low, high, support, target, budget, max_depth):
    started, deadline = time.process_time(), time.process_time()+budget
    frontier, seen, pending_rows = {}, set(), set()
    confirmed, unconfirmed, checked_boxes = Fraction(0), Fraction(0), 0
    counts = {'nodes': 0, 'leaves': 0, 'confirmed_leaves': 0, 'unconfirmed_leaves': 0}
    footer, root, declared_status, support_seen = False, None, None, False
    declared_minimum = None
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
            if kind == 'SUPPORT':
                if support_seen or counts['nodes'] or pending_rows or footer or len(fields) != 4:
                    raise ValueError('duplicate, late or malformed SUPPORT')
                declared = Support(Fraction(fields[1]), Fraction(fields[2]), fields[3], support.cap_packet)
                if declared != support:
                    raise ValueError('exact SUPPORT header does not match required CLI weights/kind')
                support_seen = True
                continue
            if not support_seen:
                raise ValueError('missing SUPPORT immediately after ROOT')
            if kind in ['S', 'L']:
                if footer or pending_rows:
                    raise ValueError('proof nodes after pending/footer')
                identifier = int(fields[1])
                if identifier not in frontier:
                    raise ValueError('unknown, duplicated or consumed proof node')
                box, depth = frontier.pop(identifier)
                counts['nodes'] += 1
                if kind == 'S':
                    if len(fields) != 6:
                        raise ValueError('malformed split')
                    dimension, middle = int(fields[2]), exact_number(fields[3])
                    left_id, right_id = int(fields[4]), int(fields[5])
                    if not 0 <= dimension < 4 or left_id == right_id or left_id in seen or right_id in seen:
                        raise ValueError('invalid split dimension/identifiers')
                    if not box[dimension][0] < middle < box[dimension][1]:
                        raise ValueError('split not inside parent')
                    left, right = list(map(list, box)), list(map(list, box))
                    left[dimension][1], right[dimension][0] = middle, middle
                    frontier[left_id], frontier[right_id] = (left, depth+1), (right, depth+1)
                    seen.update([left_id, right_id])
                else:
                    if len(fields) not in [3, 4]:
                        raise ValueError('malformed leaf')
                    counts['leaves'] += 1
                    # Producer lower bound and method label are never arithmetic evidence.
                    valid, checks, reason = verify_leaf(box, support, target, deadline, max_depth)
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
                    raise ValueError('pending row does not match reconstructed box')
                pending_rows.add(identifier)
                continue
            if kind == 'END':
                if footer or len(fields) != 5:
                    raise ValueError('malformed or duplicate END')
                declared_status = fields[1]
                if int(fields[2]) != counts['nodes'] or int(fields[3]) != counts['leaves']:
                    raise ValueError('source counters mismatch')
                if pending_rows != set(frontier):
                    raise ValueError('source omitted or invented pending box')
                if declared_status != ('PASS' if not frontier else 'INCOMPLETE'):
                    raise ValueError('source completeness claim contradicts tree')
                declared_minimum = str(exact_number(fields[4]))
                footer = True
                continue
            if kind == 'CPU' and footer:
                continue
            raise ValueError('unknown source record')
    if root is None or not footer or not support_seen:
        raise ValueError('missing root, support or partition footer')
    pending_volume = sum((volume(box) for box, _ in frontier.values()), Fraction(0))
    root_volume = volume(root)
    if confirmed+unconfirmed+pending_volume != root_volume:
        raise ValueError('exact volume accounting fails')
    return {'status': 'INDEPENDENT_BAND_CONFIRMED' if not frontier and not unresolved else 'INCOMPLETE',
            'support_exact': support.tokens(), 'target_exact': str(target), 'band_degrees_exact': [str(low), str(high)],
            'cap_packet_sha256': None if support.cap_packet is None else support.cap_packet.packet_sha256,
            'producer_minimum_UNTRUSTED': declared_minimum,
            'source_status': declared_status, **counts, 'source_pending_boxes': len(frontier),
            'independent_box_checks': checked_boxes, 'unconfirmed': unresolved,
            'confirmed_root_fraction_exact': str(confirmed/root_volume),
            'unconfirmed_leaf_fraction_exact': str(unconfirmed/root_volume),
            'source_pending_fraction_exact': str(pending_volume/root_volume),
            'cpu_seconds': time.process_time()-started, 'source_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


def controls(source, low, high, support):
    root_line = source.read_text().splitlines()[0]
    if not root_line.startswith('ROOT '):
        raise ValueError('test source must start with ROOT')
    header = 'SUPPORT '+' '.join(support.tokens())+'\n'
    pending = 'P 1 0 '+' '.join(root_line.split()[1:])+'\n'
    with TemporaryDirectory(prefix='holq-support-controls-') as directory:  # system temp folder (TMPDIR); removed on exit
        path = Path(directory)/'control.tree'
        valid = root_line+'\n'+header+pending+'END INCOMPLETE 0 0 0\n'
        path.write_text(valid)
        result = replay(path, low, high, support, Fraction(0), 1, 0)
        if result['status'] != 'INCOMPLETE' or result['source_pending_boxes'] != 1:
            raise AssertionError('whole-root pending control failed')
        wrong = 'SUPPORT '+str(support.weight_u+1)+' '+str(support.weight_s)+' '+support.kind+'\n'
        malformed = [root_line+'\n'+pending+'END INCOMPLETE 0 0 0\n',
                     valid.replace(header, wrong), valid.replace(header, header+header),
                     valid.replace('END INCOMPLETE', 'END PASS'),
                     root_line+'\n'+header+'END INCOMPLETE 0 0 0\n']
        for text in malformed:
            path.write_text(text)
            try:
                replay(path, low, high, support, Fraction(0), 1, 0)
            except ValueError:
                continue
            raise AssertionError('invalid header or completeness accepted')
        lower = math.radians(50.3)
        upper = math.radians(55)
        for _ in range(2):
            lower, upper = math.nextafter(lower, -math.inf), math.nextafter(upper, math.inf)
        fraction_root = ' '.join(root_line.split()[:7]+[lower.hex(), upper.hex()])
        fraction_pending = 'P 1 0 '+' '.join(fraction_root.split()[1:])+'\n'
        path.write_text(fraction_root+'\n'+header+fraction_pending+'END INCOMPLETE 0 0 0\n')
        result = replay(path, Fraction('50.30'), Fraction(55), support, Fraction(0), 1, 0)
        if result['band_degrees_exact'] != ['503/10', '55'] or result['source_pending_boxes'] != 1:
            raise AssertionError('fractional-degree root control failed')
    return {'test': 'PASS', 'controls': ['whole-root pending', 'missing/mismatched/duplicate SUPPORT rejected',
                                      'false PASS and omitted pending rejected', 'exact503/10–55 degree root']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--precision', type=int, required=True)
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--low', type=Fraction, required=True)
    parser.add_argument('--high', type=Fraction, required=True)
    parser.add_argument('--support', nargs=3, required=True)
    parser.add_argument('--cap-packet', type=Path)
    parser.add_argument('--target', type=Fraction, required=True)
    parser.add_argument('--max-cpu-seconds', type=float, required=True)
    parser.add_argument('--max-depth', type=int, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--test', action='store_true')
    arguments = parser.parse_args()
    ctx.prec, ctx.threads = arguments.precision, 1
    packet = JointCap.from_file(arguments.cap_packet) if arguments.cap_packet is not None else None
    support = Support(Fraction(arguments.support[0]), Fraction(arguments.support[1]), arguments.support[2], packet)
    if not 0 < arguments.low < arguments.high <= 180 or arguments.target < 0 or arguments.max_cpu_seconds <= 0 or arguments.max_depth < 0:
        parser.error('invalid band, target or budget')
    if arguments.test:
        result = controls(arguments.source, arguments.low, arguments.high, support)
    else:
        result = replay(arguments.source, arguments.low, arguments.high, support, arguments.target,
                        arguments.max_cpu_seconds, arguments.max_depth)
    directory = Path(__file__).resolve().parent
    result['own_source_hashes'] = {name: hashlib.sha256((directory/name).read_bytes()).hexdigest() for name in
        [Path(__file__).name, 'holq_support_arb.py', 'holq_joint_cap_arb.py', 'holq_peer_tree_arb.py', 'holq_local_arb.py',
         'arb_differential.py', 'fourlog_arb_box.py', 'fourlog_centered.py']}
    arguments.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
