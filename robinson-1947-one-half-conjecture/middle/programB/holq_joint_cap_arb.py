#!/usr/bin/env python3
"""Exact P55 data validation and independent Arb cap arithmetic.
Version 0.10 — Program B, 20261102__09:45 EST. Code preparation only; this
module does not enable JOINT in the support objective or authorize any pilot.
"""
from dataclasses import dataclass
from fractions import Fraction
import hashlib
import json
from flint import arb, acb
from arb_differential import SecondDifferential
from fourlog_centered import rational_ball
from fourlog_arb_box import require_positive
from holq_local_arb import exact_intersection


CANONICAL_P = ((16946, 3451, -992, 2537), (3451, 30184, 856, -108),
               (-992, 856, 2733, -344), (2537, -108, -344, 879))


def inverse(matrix):
    size = len(matrix)
    rows = [list(row)+[Fraction(int(index == column)) for column in range(size)]
            for index, row in enumerate(matrix)]
    determinant = Fraction(1)
    for column in range(size):
        pivot = next((index for index in range(column, size) if rows[index][column]), None)
        if pivot is None:
            raise ValueError('singular rational matrix')
        if pivot != column:
            rows[column], rows[pivot] = rows[pivot], rows[column]
            determinant = -determinant
        scale = rows[column][column]
        determinant *= scale
        rows[column] = [value/scale for value in rows[column]]
        for row in range(size):
            if row != column:
                coefficient = rows[row][column]
                rows[row] = [left-coefficient*right for left, right in zip(rows[row], rows[column])]
    return tuple(tuple(row[size:]) for row in rows), determinant


def multiply(first, second):
    return tuple(tuple(sum((first[row][index]*second[index][column] for index in range(len(second))), Fraction(0))
                       for column in range(len(second[0]))) for row in range(len(first)))


def exact_matrix(values):
    matrix = tuple(tuple(Fraction(value) for value in row) for row in values)
    if len(matrix) != 4 or any(len(row) != 4 for row in matrix):
        raise ValueError('joint cap matrix must be4x4')
    return matrix


@dataclass(frozen=True)
class JointCap:
    matrix: tuple
    coefficients: tuple
    packet_sha256: str

    @classmethod
    def from_file(cls, path):
        raw = path.read_bytes()
        packet = json.loads(raw)
        if Fraction(packet['lambda_exact']) != Fraction(4, 5) or Fraction(packet['mu_exact']) != Fraction(1, 2):
            raise ValueError('P55 weights mismatch')
        positive = exact_matrix(packet['P'])
        canonical = tuple(tuple(Fraction(value, 10000) for value in row) for row in CANONICAL_P)
        if positive != canonical:
            raise ValueError('JOINT_P55 packet does not match canonical rational P')
        expected_j = ((0, Fraction(-8, 5), Fraction(-1, 2), 0),
                      (Fraction(-8, 5), 0, 0, Fraction(-1, 2)),
                      (Fraction(-1, 2), 0, 0, 0), (0, Fraction(-1, 2), 0, 0))
        if exact_matrix(packet['J']) != expected_j:
            raise ValueError('joint coefficient matrix mismatch')
        minors = []
        for size in range(1, 5):
            _, determinant = inverse(tuple(tuple(row[:size]) for row in positive[:size]))
            if determinant <= 0:
                raise ValueError('P is not positive definite by exact Sylvester test')
            minors.append(determinant)
        if minors != [Fraction(value) for value in packet['positive_leading_principal_minors']]:
            raise ValueError('packet minor values mismatch')
        reciprocal, _ = inverse(positive)
        correction = multiply(multiply(expected_j, reciprocal), expected_j)
        matrix = tuple(tuple((positive[row][column]+correction[row][column])/2 for column in range(4))
                       for row in range(4))
        if matrix != exact_matrix(packet['K']):
            raise ValueError('packet K is not exact(P+J inverseP J)/2')
        coefficients = ((matrix[0][0]+matrix[1][1])/2, (matrix[0][0]-matrix[1][1])/2, matrix[0][1],
                        (matrix[2][2]+matrix[3][3])/2, (matrix[2][2]-matrix[3][3])/2, matrix[2][3],
                        matrix[0][2]+matrix[1][3], matrix[0][2]-matrix[1][3], matrix[0][3]+matrix[1][2])
        names = ['Ae', 'ReZe', 'ImZe', 'Me', 'ReMz', 'ImMz', 'Le', 'ReLz', 'ImLz']
        if coefficients != tuple(Fraction(packet['elementary_coefficients'][name]) for name in names):
            raise ValueError('packet elementary coefficients mismatch')
        return cls(matrix, coefficients, hashlib.sha256(raw).hexdigest())

    def evaluate(self, theta):
        squared_endpoint = (acb(0, 1)*theta).exp()/4
        denominator = 1-squared_endpoint
        require_positive(denominator.real, 'even cap kernel Log right half-plane unresolved')
        ze = -denominator.log()/2
        lz = squared_endpoint/denominator
        mz = 2*squared_endpoint/(denominator*denominator)
        ae, le, me = -(arb(3)/4).log()/2, arb(1)/3, arb(8)/9
        terms = [ae, ze.real, ze.imag, me, mz.real, mz.imag, le, lz.real, lz.imag]
        expanded = sum(rational_ball(coefficient)*value for coefficient, value in zip(self.coefficients, terms))
        def block(diagonal, cross):
            return [[(diagonal+cross.real)/2, cross.imag/2], [cross.imag/2, (diagonal-cross.real)/2]]
        upper, mixed, lower = block(ae, ze), block(le, lz), block(me, mz)
        gram = [upper[0]+mixed[0], upper[1]+mixed[1], mixed[0]+lower[0], mixed[1]+lower[1]]
        direct = sum(gram[row][column]*rational_ball(self.matrix[column][row]) for row in range(4) for column in range(4))
        if isinstance(expanded, SecondDifferential):
            return exact_intersection(expanded, direct).real
        return expanded.intersection(direct)
