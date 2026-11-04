#!/usr/bin/env python3
"""Robinson 1947, Program A author: independent rational verification of joint support.
Version 0.10 — 20261102__09:43 EST. Own Fraction elimination, not author code; no angle search.
"""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path


def multiply(first, second):
    return [[sum((first[row][inner] * second[inner][column]
                  for inner in range(len(second))), F(0))
             for column in range(len(second[0]))] for row in range(len(first))]


def inverse(matrix):
    size = len(matrix)
    rows = [list(row) + [F(column == index) for column in range(size)]
            for index, row in enumerate(matrix)]
    for column in range(size):
        pivot = next(index for index in range(column, size) if rows[index][column])
        rows[column], rows[pivot] = rows[pivot], rows[column]
        scale = rows[column][column]
        rows[column] = [item / scale for item in rows[column]]
        for index in range(size):
            if index != column:
                scale = rows[index][column]
                rows[index] = [item - scale * other
                               for item, other in zip(rows[index], rows[column])]
    return [row[size:] for row in rows]


def determinant(matrix):
    rows = [list(row) for row in matrix]
    result = F(1)
    for column in range(len(rows)):
        pivot = next(index for index in range(column, len(rows)) if rows[index][column])
        if pivot != column:
            rows[column], rows[pivot] = rows[pivot], rows[column]
            result = -result
        scale = rows[column][column]
        result *= scale
        for index in range(column + 1, len(rows)):
            factor = rows[index][column] / scale
            rows[index] = [item - factor * other
                           for item, other in zip(rows[index], rows[column])]
    return result


def check_packet(path):
    packet = json.loads(path.read_text())
    integers = [[16946, 3451, -992, 2537], [3451, 30184, 856, -108],
                [-992, 856, 2733, -344], [2537, -108, -344, 879]]
    positive = [[F(item, 10000) for item in row] for row in integers]
    coupling = [[F(0) for _ in range(4)] for _ in range(4)]
    coupling[0][1] = coupling[1][0] = -2 * F(4, 5)
    for first, second in [(0, 2), (1, 3)]:
        coupling[first][second] = coupling[second][first] = -F(1, 2)
    assert F(packet['lambda_exact']) == F(4, 5) and F(packet['mu_exact']) == F(1, 2)
    assert positive == [[F(item) for item in row] for row in packet['P']]
    assert coupling == [[F(item) for item in row] for row in packet['J']]
    minors = [determinant([row[:size] for row in positive[:size]]) for size in range(1, 5)]
    assert all(item > 0 for item in minors)
    assert minors == list(map(F, packet['positive_leading_principal_minors']))
    product = multiply(multiply(coupling, inverse(positive)), coupling)
    majorant = [[(positive[row][column] + product[row][column]) / 2
                 for column in range(4)] for row in range(4)]
    assert majorant == [[F(item) for item in row] for row in packet['K']]
    coefficients = dict(Ae=(majorant[0][0] + majorant[1][1]) / 2,
                        ReZe=(majorant[0][0] - majorant[1][1]) / 2, ImZe=majorant[0][1],
                        Me=(majorant[2][2] + majorant[3][3]) / 2,
                        ReMz=(majorant[2][2] - majorant[3][3]) / 2, ImMz=majorant[2][3],
                        Le=majorant[0][2] + majorant[1][3],
                        ReLz=majorant[0][2] - majorant[1][3],
                        ImLz=majorant[0][3] + majorant[1][2])
    assert coefficients == {key: F(value) for key, value in packet['elementary_coefficients'].items()}
    print('PASS: own exact P/J, four positive minors, inverse, all16 K entries, all9 cap coefficients.')
    print('MINORS', ', '.join(map(str, minors)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--test', action='store_true', required=True)
    parser.add_argument('--packet', type=Path, required=True)
    arguments = parser.parse_args()
    check_packet(arguments.packet)


if __name__ == '__main__':
    main()
