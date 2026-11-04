#!/usr/bin/env python3
"""Robinson 1947, Program A: structural replay of HOLQ partition artifacts.
Version 0.20 — 20261101__22:51 ET. Exact covered volume, leaf reasons, pending angle ranges; structural accounting ONLY, no independent leaf inequalities.
"""
import argparse
from fractions import Fraction
from pathlib import Path
import json
from collections import Counter


def coordinates(tokens):
    values = [float.fromhex(token) for token in tokens]
    assert len(values) == 8
    axes = tuple((values[index], values[index + 1]) for index in range(0, 8, 2))
    assert all(low <= high for low, high in axes)
    return axes


def volume(axes):
    result = Fraction(1)
    for low, high in axes:
        result *= Fraction.from_float(high) - Fraction.from_float(low)
    return result


def replay(path, target):
    active, seen, reported = {}, set(), {}
    split_count, leaf_count, minimum = 0, 0, None
    ending, cpu = None, None
    reasons = Counter()
    certified_volume, root_volume = Fraction(0), None
    for line in path.read_text().splitlines():
        fields = line.split()
        kind = fields[0]
        if kind == 'ROOT':
            assert not seen and not active
            active[1] = (coordinates(fields[1:]), 0)
            root_volume = volume(active[1][0])
            seen.add(1)
        elif kind == 'S':
            assert ending is None and not reported
            parent, dimension = map(int, fields[1:3])
            middle = float.fromhex(fields[3])
            left, right = map(int, fields[4:6])
            assert 0 <= dimension < 4 and left != right and left not in seen and right not in seen
            axes, depth = active.pop(parent)
            assert axes[dimension][0] < middle < axes[dimension][1]
            first, second = list(axes), list(axes)
            first[dimension] = (axes[dimension][0], middle)
            second[dimension] = (middle, axes[dimension][1])
            active[left], active[right] = (tuple(first), depth + 1), (tuple(second), depth + 1)
            seen.update([left, right])
            split_count += 1
        elif kind == 'L':
            assert ending is None and not reported
            identity = int(fields[1])
            lower = Fraction.from_float(float.fromhex(fields[2]))
            assert lower > target
            axes, _ = active.pop(identity)
            certified_volume += volume(axes)
            reason = fields[3] if len(fields) == 4 else 'UNSPECIFIED'
            assert reason in ['N', 'M', 'T', 'UNSPECIFIED']
            reasons[reason] += 1
            minimum = lower if minimum is None else min(lower, minimum)
            leaf_count += 1
        elif kind == 'P':
            assert ending is None
            identity, depth = map(int, fields[1:3])
            assert identity not in reported
            reported[identity] = (coordinates(fields[3:]), depth)
        elif kind == 'END':
            assert ending is None and reported == active
            status, nodes, leaves = fields[1], int(fields[2]), int(fields[3])
            assert nodes == split_count + leaf_count and leaves == leaf_count
            assert (status == 'PASS') == (not active)
            assert status in ['PASS', 'INCOMPLETE']
            if minimum is not None:
                assert Fraction.from_float(float.fromhex(fields[4])) == minimum
            ending = status
        elif kind == 'CPU':
            assert ending is not None and fields[2] == 'STOP_REQUESTED' and int(fields[3]) in [0, 1]
            cpu = float.fromhex(fields[1])
        else:
            raise ValueError(f'Unknown artifact record: {kind}')
    assert ending is not None and cpu is not None
    assert root_volume > 0
    assert certified_volume + sum((volume(axes) for axes, _ in active.values()), Fraction(0)) == root_volume
    share = certified_volume / root_volume
    ranges = Counter((axes[3][0].hex(), axes[3][1].hex()) for axes, _ in active.values())
    return {'status': ending, 'nodes': split_count + leaf_count, 'leaves': leaf_count, 'leaves_by_reason': dict(reasons),
            'pending': len(active), 'pending_angle_ranges_radians_hex': [{'low': low, 'high': high, 'boxes': count} for (low, high), count in sorted(ranges.items())],
            'certified_halfchart_volume_share_exact': str(share), 'certified_halfchart_volume_share_decimal': float(share),
            'cpu_seconds': cpu, 'replay': 'STRUCTURAL PASS ONLY'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--test', required=True, action='store_true')
    parser.add_argument('--tree', required=True, type=Path)
    parser.add_argument('--target', required=True, type=Fraction)
    arguments = parser.parse_args()
    print(json.dumps(replay(arguments.tree, arguments.target), indent=2))
