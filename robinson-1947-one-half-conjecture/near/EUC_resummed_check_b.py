#!/usr/bin/env python3
"""Exact all-order cell check with resummed area bounds and cancelled high tail.
Version 0.40 — program b (module of check_B8_b.py). Exact recurrences and Cauchy tails with resummed area bounds.
"""

import argparse
import json
from fractions import Fraction as Rat
from EUC_B3_check_b import product
from EUC_B4_check_b import polynomial_power, rational_coefficients
from EUC_B5_check_b import root_upper, series_operators, model_caps
from EUC_B7_check_b import area_square


def sharp_coefficients(kappa, beta, quadratic):
    affine = [Rat(1), -kappa]
    denominator = [Rat(1), -(2+kappa), 2*kappa-beta]
    if quadratic:
        budget = [Rat(0)]*4+[Rat(256, 243), Rat(4096, 3645)-2*Rat(256, 243)]
        numerator = product(product([0, 1, Rat(2, 3)], budget), [3, -3*(2+kappa), 6*kappa-2*beta])
        denominator = product(product(polynomial_power([1, -Rat(2, 3)], 2), polynomial_power(affine, 3)),
                              polynomial_power(denominator, 2))
    else:
        numerator = product([0, 0, 0, Rat(16, 15), Rat(32, 45)], [2, -2*(2+kappa), 4*kappa-beta])
        denominator = product(polynomial_power(affine, 2), polynomial_power(denominator, 2))
    result = rational_coefficients(numerator, denominator, 64)
    assert all(value == 0 for value in result[:5 if quadratic else 3])
    return result


def sharp_circle_caps():
    point = Rat(1, 4)
    affine = 1-2*point
    denominator = affine-Rat(16, 15)*point**2/(1-2*point)
    assert denominator > 0
    numerator = point*(1+Rat(2, 3)*point)
    linear = numerator*Rat(16, 15)*point**2/(1-2*point)
    linear *= 1/(affine**2*denominator)+1/(affine*denominator**2)
    quadratic = numerator*area_square(point)
    quadratic *= 2/(affine**3*denominator)+1/(affine**2*denominator**2)
    return linear, quadratic


def cancelled_high_tail(radius):
    size, larger = radius**2, Rat(1, 4)
    scale = Rat(20, 33)*Rat(4, 3)**6
    numerator = [Rat(0)]*7+[scale]
    denominator = product(polynomial_power([1, -Rat(2, 3)], 3), polynomial_power([1, -2], 4))
    coefficients = rational_coefficients(numerator, denominator, 64)
    circle = scale*larger**7/((1-Rat(2, 3)*larger)**3*(1-2*larger)**4)
    hh, ww, _ = series_operators(coefficients, circle, radius)
    tcap, _ = model_caps(Rat(2), size)
    return (ww+tcap*hh)/((1-Rat(20, 9)*size)/(1+4*size)**2)


def complete_cells(radius, norm_constant, square_constant):
    size = radius**2
    linear_circle, quadratic_circle = sharp_circle_caps()
    universal = Rat(16, 3)*size/(1-4*size)**2+4*size/(1-4*size)
    assert universal < 1
    records = []
    for index in range(224):
        low, high = Rat(index, 224), Rat(index+1, 224)
        peak = Rat(1, 4) if low <= Rat(1, 2) <= high else max(low*(1-low), high*(1-high))
        gamma = min(Rat(1), 2*root_upper(peak))
        kappa = (min(Rat(2), root_upper(Rat(16, 9)*(Rat(27, 50)**2+4*(1-low)*(Rat(1, 2)-low))))
                 if low < Rat(1, 2) else Rat(7, 10))
        beta = Rat(16, 15)*gamma
        hr, wr, _ = series_operators(sharp_coefficients(kappa, beta, True), quadratic_circle, radius)
        hz, _, _ = series_operators(sharp_coefficients(kappa, beta, False), linear_circle, radius)
        tcap, _ = model_caps(kappa, size)
        norm = root_upper(norm_constant+520*(1-low))
        model_h = (1-Rat(20, 9)*size)/(1+kappa**2*size)**2-gamma*hz
        lower_h = max(1-universal, model_h)
        assert lower_h > 0
        remainder = (wr+tcap*hr+norm*hz)/lower_h
        score = high*remainder+root_upper(130*high)+square_constant*high
        records.append((score*size/(Rat(24, 25)+Rat(17, 100)*low), index))
    return max(records)


def run_tests():
    radius = Rat(39, 200)
    assert Rat(1, 4)-radius**2 > Rat(23, 50)**2
    tail = cancelled_high_tail(radius)
    assert tail*tail < Rat(5, 2)
    norm_constant, square_constant = Rat(45, 2), Rat(21, 2)
    maximum, index = complete_cells(radius, norm_constant, square_constant)
    print(json.dumps(dict(radius=str(radius), tail_upper=float(tail), completion_maximum=float(maximum),
                          completion_cell=index, cells=224, norm_constant=str(norm_constant),
                          pass_certificate=maximum < Rat(199, 200), status='PASS' if maximum < Rat(199, 200) else 'FAIL'), indent=2), flush=True)
    assert maximum < Rat(199, 200)
    assert norm_constant/(4*(Rat(16, 27)-Rat(1, 20))) < square_constant


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--test', required=True, action='store_true')
    parser.parse_args()
    run_tests()


if __name__ == '__main__':
    main()
