#!/usr/bin/env python3
"""First program for Lemmas 4.3 and 4.5: the comparison polynomials and their exact positivity certificates.
Version 0.60 — program b. Exact rational arithmetic; it also checks a cell chain up to R=21/100, which the paper does not use (the cells of Lemma 4.8 are checked by check_B9_b.py).
"""

import argparse
from fractions import Fraction as Rat
from functools import lru_cache
import json
import sympy as sp
from EUC_B3_check_b import product
from EUC_B4_check_b import polynomial_power, rational_coefficients
from EUC_B5_check_b import root_upper, series_operators, model_caps
from EUC_B5_model_check_b import real_laurent_product
from EUC_B6_check_b import derive_model_area, circle_square, projective_coefficients
from EUC_resummed_check_b import sharp_coefficients, sharp_circle_caps


def rectangle_certificate(polynomial, lower):
    midpoint, cosine = sp.symbols('t x')
    degree_t, degree_x = polynomial.degree(midpoint), polynomial.degree(cosine)
    rows = [projective_coefficients([Rat(polynomial.nth(power, other)) for other in range(degree_x+1)], Rat(-1), Rat(1))
            for power in range(degree_t+1)]
    output = []
    for power in range(degree_x+1):
        output.extend(projective_coefficients([row[power] for row in rows], lower, Rat(1, 2)))
    minimum = min(output)
    return dict(degrees=[degree_t, degree_x], count=len(output), minimum=str(minimum), positive=minimum>0)


def finite_certificates(lower, margin_linear, margin_square, norm_base, norm_slope):
    base, values, quotient = derive_model_area()
    midpoint, parameter, cosine = sp.symbols('t c x')
    numerator, denominator = quotient.numer.as_expr(), quotient.denom.as_expr()
    square = circle_square(denominator, midpoint, parameter, cosine)
    real_numerator = real_laurent_product(numerator, denominator, parameter, cosine)
    baseline_num, baseline_den = sp.Rational(1, 2)-midpoint, sp.Rational(3, 4)*(sp.Rational(5, 4)+2*midpoint)
    difference = sp.Poly(baseline_den*real_numerator-baseline_num*square.as_expr(), cosine)
    divided, residual = sp.div(difference, sp.Poly(1-cosine, cosine))
    assert residual.is_zero
    multiplier = 2*margin_linear-4*margin_square+4*margin_square*cosine
    target = sp.Poly(divided.as_expr()-multiplier*baseline_den*square.as_expr(), midpoint, cosine)
    model_result = rectangle_certificate(target, lower)
    print('MODEL', json.dumps(model_result), flush=True)
    common = base(values[-1].denom)
    residual = common/base(quotient.denom)**2
    assert residual.numer.degrees()[1] == residual.denom.degrees()[1] == 0
    for expression in [residual.numer.as_expr(), residual.denom.as_expr()]:
        polynomial = sp.Poly(expression, midpoint, domain=sp.QQ)
        assert polynomial.eval(sp.Rational(lower)) != 0 and polynomial.eval(sp.Rational(1, 2)) != 0
        assert polynomial.count_roots(sp.Rational(lower), sp.Rational(1, 2)) == 0
    target = sp.Poly(norm_base+2*norm_slope*(1-cosine), midpoint, cosine)*circle_square(common.as_expr(), midpoint, parameter, cosine)
    for index, value in enumerate(values, 2):
        cleared = value*common
        assert all(degree == 0 for degree in cleared.denom.degrees())
        target -= circle_square(cleared.as_expr(), midpoint, parameter, cosine)*sp.Rational(1, 2*index-1)
    norm_result = rectangle_certificate(target, lower)
    print('FINITE NORM', json.dumps(norm_result), flush=True)
    assert model_result['positive'] and norm_result['positive']
    return model_result, norm_result


@lru_cache(maxsize=1024)
def extended_sharp_coefficients(kappa, beta, quadratic):
    result = list(sharp_coefficients(kappa, beta, quadratic))
    affine, denominator = [1, -kappa], [1, -(2+kappa), 2*kappa-beta]
    denominator = product(polynomial_power(affine, 3 if quadratic else 2), polynomial_power(denominator, 2))
    if quadratic:
        denominator = product(denominator, polynomial_power([1, -Rat(2, 3)], 2))
    # The cleared numerator has degree<=9, so every following recurrence numerator is0.
    for index in range(len(result), 97):
        result.append(-sum(denominator[offset]*result[index-offset] for offset in range(1, len(denominator))))
    assert all(value >= 0 for value in result)
    return tuple(result)


@lru_cache(maxsize=512)
def cell_high_tail(kappa, radius):
    larger, size = Rat(1, 4), radius**2
    scale = Rat(20, 33)*Rat(4, 3)**6
    denominator = product(product(polynomial_power([1, -Rat(2, 3)], 3), [1, -2]), polynomial_power([1, -kappa], 3))
    coefficients = rational_coefficients([Rat(0)]*7+[scale], denominator, 96)
    circle = scale*larger**7/((1-Rat(2, 3)*larger)**3*(1-2*larger)*(1-kappa*larger)**3)
    hh, ww, _ = series_operators(coefficients, circle, radius)
    tcap, _ = model_caps(kappa, size)
    lcap = min(Rat(20, 9), kappa**2+Rat(4, 3)*kappa)
    return (ww+tcap*hh)/((1-lcap*size)/(1+kappa**2*size)**2)


def quadratic_minimum(constant, linear, quadratic, endpoint):
    candidates = [constant, constant+linear*endpoint+quadratic*endpoint**2]
    if quadratic > 0 and 0 < -linear < 2*quadratic*endpoint:
        candidates.append(constant-linear**2/(4*quadratic))
    return min(candidates)


def cell_caps(low, high, lower):
    peak = Rat(1, 4) if low <= Rat(1, 2) <= high else max(low*(1-low), high*(1-high))
    gamma = min(Rat(1), 2*root_upper(peak))
    kappa = (min(Rat(2), root_upper(Rat(16, 9)*((1-lower)**2+4*(1-low)*(Rat(1, 2)-low))))
             if low < Rat(1, 2) else Rat(7, 10))
    return gamma, kappa


def complete_cells(radius, lower, margin_linear, margin_square, norm_base, norm_slope, cell_count):
    size, offset = radius**2, Rat(16, 27)-Rat(1, 20)
    linear_circle, quadratic_circle = sharp_circle_caps()
    universal = Rat(16, 3)*size/(1-4*size)**2+4*size/(1-4*size)
    assert universal < 1 and 1/(1+lower) < Rat(7, 10)
    records = []
    for index in range(cell_count):
        low, high = Rat(index, cell_count), Rat(index+1, cell_count)
        gamma, kappa = cell_caps(low, high, lower)
        beta, endpoint = Rat(16, 15)*gamma, 4*(1-low)
        hr, wr, _ = series_operators(extended_sharp_coefficients(kappa, beta, True), quadratic_circle, radius)
        hz, _, _ = series_operators(extended_sharp_coefficients(kappa, beta, False), linear_circle, radius)
        tail = cell_high_tail(kappa, radius)
        norm_constant = norm_base+tail*tail
        norm = root_upper(norm_constant+norm_slope*endpoint)
        tcap, _ = model_caps(kappa, size)
        lcap = min(Rat(20, 9), kappa**2+Rat(4, 3)*kappa)
        model_h = (1-lcap*size)/(1+kappa**2*size)**2-gamma*hz
        lower_h = max(1-universal, model_h)
        assert lower_h > 0
        remainder = (wr+tcap*hr+norm*hz)/lower_h
        margin = margin_linear-4*margin_square+2*margin_square*low
        slope = margin/size-high*remainder
        positive_affine = min(offset, offset+slope*endpoint)
        polynomial_minimum = quadratic_minimum(offset**2, 2*offset*slope-norm_constant*high,
                                                slope*slope-norm_slope*high, endpoint)
        records.append((min(positive_affine, polynomial_minimum), index))
    return min(records)


def run_tests():
    assert quadratic_minimum(Rat(2), Rat(-2), Rat(1), Rat(2)) == 1
    assert quadratic_minimum(Rat(2), Rat(1), Rat(-1), Rat(2)) == 0
    lower, radius = Rat(9, 20), Rat(21, 100)
    margin_linear, margin_square, norm_base, norm_slope = Rat(13, 10), Rat(21, 200), Rat(20), Rat(130)
    assert Rat(1, 4)-radius**2 >= lower**2
    model, norm = finite_certificates(lower, margin_linear, margin_square, norm_base, norm_slope)
    minimum, index = complete_cells(radius, lower, margin_linear, margin_square, norm_base, norm_slope, 256)
    print(json.dumps(dict(status='PASS' if minimum > 0 else 'FAIL', radius=str(radius), midpoint_lower=str(lower),
                          minimum=float(minimum), minimum_cell=index, cells=256,
                          model=model, finite_norm=norm, pass_certificate=minimum>0), indent=2), flush=True)
    assert minimum > 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--test', action='store_true', required=True)
    parser.parse_args()
    run_tests()


if __name__ == '__main__':
    main()
