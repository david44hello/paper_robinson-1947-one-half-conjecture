#!/usr/bin/env python3
"""Robinson 1947, Program A: mandatory support binding plus exact structural accounting.
Version 0.10 — 20261102__09:50 EST. Not mathematical leaf verification. Plain replayer remains unchanged.
"""
import argparse
from fractions import Fraction
import json
from pathlib import Path
from replay_holo_tree import replay as replay_partition


class PartitionText:
    def __init__(self, text):
        self.text = text

    def read_text(self):
        return self.text


def support_binding(values):
    coefficient, mu = map(Fraction, values[:2])
    kind = values[2]
    assert coefficient >= 0 and mu >= 0
    assert ((kind == 'EVEN_VALUE' and mu == 0) or
            (kind == 'JOINT_P55' and coefficient == Fraction(4, 5) and mu == Fraction(1, 2)))
    return coefficient, mu, kind


def replay(path, target, support):
    expected = support_binding(support)
    lines = path.read_text().splitlines()
    assert len(lines) >= 4 and lines[0].split()[0] == 'ROOT'
    header = lines[1].split()
    assert len(header) == 4 and header[0] == 'SUPPORT'
    assert support_binding(header[1:]) == expected
    assert all(line.split()[0] != 'SUPPORT' for line in lines[2:])
    body = PartitionText('\n'.join([lines[0], *lines[2:]]))
    report = replay_partition(body, target)
    report['support'] = dict(coefficient=str(expected[0]), mu=str(expected[1]), kind=expected[2])
    report['replay'] = 'SUPPORT-BOUND STRUCTURAL PASS ONLY; no independent leaf arithmetic'
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--test', required=True, action='store_true')
    parser.add_argument('--tree', required=True, type=Path)
    parser.add_argument('--target', required=True, type=Fraction)
    parser.add_argument('--support', required=True, nargs=3)
    arguments = parser.parse_args()
    print(json.dumps(replay(arguments.tree, arguments.target, arguments.support), indent=2))


if __name__ == '__main__':
    main()
