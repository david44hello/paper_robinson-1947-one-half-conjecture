#!/usr/bin/env python3
"""Robinson 1947, program a: independent B9 cell checker, no program-b code.
Version 0.10 — 20261101__23:25 ET. Reuses accepted B8 finite inputs; only the exact coupled pole cap changes.
"""
import argparse
from fractions import Fraction as F
import json
from check_B8_a import tail_and_model_h, quadratic_minimum
from check_B7R_a import operators, resummed_value_derivative
from check_EUC_B5_area import gamma_upper, sqrt_upper, model_caps


def cell_certificate(low, high, radius):
    size = radius**2
    gamma = min(F(1), gamma_upper(low, high))
    kappa = max(F(20, 29), 2 - F(8, 3) * low)
    tail, model_h = tail_and_model_h(radius, kappa)
    norm = 20 + tail**2
    hz, _ = operators(radius, lambda point: resummed_value_derivative(point, kappa, gamma, False))
    hr, wr = operators(radius, lambda point: resummed_value_derivative(point, kappa, gamma, True))
    universal = F(16, 3) * size / (1 - 4 * size)**2 + 4 * size / (1 - 4 * size)
    actual_h = max(1 - universal, model_h - gamma * hz)
    assert actual_h > 0
    tcap, _ = model_caps(kappa, size)
    norm_upper = sqrt_upper(norm + 520 * (1 - low))
    remainder = (wr + tcap * hr + norm_upper * hz) / actual_h
    linear = (F(22, 25) + F(21, 100) * low) / size - high * remainder
    return quadratic_minimum(F(16, 27) - F(1, 20), linear, norm, high, 4 * (1 - low))


def run_certificate(radius, cells):
    assert F(1, 4) - radius**2 >= F(9, 20)**2
    rows = []
    for index in range(cells):
        try:
            rows.append((cell_certificate(F(index, cells), F(index + 1, cells), radius), index))
        except AssertionError as error:
            raise AssertionError(f'Uncertified B9 radius {radius}, cell {index}/{cells}') from error
    affine, affine_index = min((result[0], index) for result, index in rows)
    quadratic, quadratic_index = min((result[1], index) for result, index in rows)
    print(json.dumps({'status': 'INDEPENDENT EXACT PASS', 'radius': str(radius), 'cells': cells,
                      'min_affine_exact': str(affine), 'min_affine_decimal': float(affine), 'min_affine_cell': affine_index,
                      'min_quadratic_exact': str(quadratic), 'min_quadratic_decimal': float(quadratic), 'min_quadratic_cell': quadratic_index,
                      'method': 'coupled rational pole cap, complete rational functions, exact whole-e vertex; no author code'}, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--test', required=True, action='store_true')
    parser.add_argument('--radius', required=True, type=F)
    parser.add_argument('--cells', required=True, type=int)
    args = parser.parse_args()
    run_certificate(args.radius, args.cells)
