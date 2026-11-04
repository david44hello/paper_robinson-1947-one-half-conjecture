#!/usr/bin/env python3
"""Independent B6 exact model derivatives, positive polynomial and infinite tails.
Version 0.10 — program b, 20261101__22:17 EST. Own quadratic field, projective coefficient positivity,192 cells with rigorous48-term Cauchy tails. No author imports.
"""

import argparse
import json
from fractions import Fraction as Rat
from math import comb
import sympy as sp
from sympy.polys.fields import field
from EUC_B3_check_b import product
from EUC_B4_check_b import OuterPair, polynomial_power, rational_coefficients
from EUC_B5_model_check_b import coercivity_polynomial
from EUC_B5_check_b import root_upper, coefficients, series_operators, majorant_value, model_caps


def projective_coefficients(coeffs, low, high):
    """(1+u)^n p((low+high*u)/(1+u)), by homogeneous Horner."""
    degree = len(coeffs)-1
    result = [coeffs[-1]]
    for power in range(degree-1, -1, -1):
        next_result = [Rat(0)]*(len(result)+1)
        for index, value in enumerate(result):
            next_result[index] += low*value
            next_result[index+1] += high*value
        homogenizing = degree-power
        for index in range(homogenizing+1):
            next_result[index] += coeffs[power]*comb(homogenizing, index)
        result = next_result
    return result


def certify_projective_positive(poly, midpoint, cosine):
    degree_t, degree_x = poly.degree(midpoint), poly.degree(cosine)
    transformed_x = [[Rat(0)]*(degree_x+1) for _ in range(degree_t+1)]
    for tpower in range(degree_t+1):
        row = [Rat(poly.nth(tpower, xpower)) for xpower in range(degree_x+1)]
        transformed_x[tpower] = projective_coefficients(row, Rat(-1), Rat(1))
    all_coefficients = []
    for xpower in range(degree_x+1):
        column = [transformed_x[tpower][xpower] for tpower in range(degree_t+1)]
        all_coefficients.extend(projective_coefficients(column, Rat(47, 100), Rat(1, 2)))
    assert min(all_coefficients) > 0
    return min(all_coefficients), len(all_coefficients)


def derive_model_area():
    base, midpoint, model = field('t,c', sp.QQ)
    variance, size = 1-midpoint**2, base(1)/4-midpoint**2
    increment = OuterPair(base.zero, base.one, -size)
    constant = lambda value: OuterPair(value, base.zero, -size)
    tt, vv = constant(midpoint), constant(variance)
    aa, bb = constant((model-midpoint)/variance), constant(midpoint/variance)
    physical = increment*(1+bb*increment)/(1-aa*increment)**2
    prime = (1+(2*bb+aa)*increment)/(1-aa*increment)**3
    span = physical-physical.opposite()
    quotient = 1+((-tt+increment)*prime-(-tt-increment)*prime.opposite())/span
    assert quotient.second == 0
    output = []
    for index in range(2, 6):
        variation = -2*increment**(index+1)/(vv**index*(1-aa*increment)**3*(1+bb*increment)**(index-2))
        logarithmic = (index+1)/increment+(2-index)*bb/(1+bb*increment)+3*aa/(1-aa*increment)
        derivative = variation*logarithmic
        numerator = (-tt+increment)*derivative-(-tt-increment)*derivative.opposite()
        numerator -= (quotient-1)*(variation-variation.opposite())
        value = -numerator/span/constant(size)
        assert value.second == 0
        output.append(value.first)
        print('Derived physical model area coefficient', index, flush=True)
    return base, output, quotient.first


def circle_square(expression, midpoint, model, cosine):
    polynomial = sp.Poly(expression, model)
    coeffs = [sp.Poly(polynomial.nth(index), midpoint, domain=sp.QQ) for index in range(polynomial.degree()+1)]
    harmonics = [sp.Poly(1, cosine), sp.Poly(cosine, cosine)]
    for _ in range(2, polynomial.degree()+1):
        harmonics.append(2*sp.Poly(cosine, cosine)*harmonics[-1]-harmonics[-2])
    terms = {}
    for gap in range(polynomial.degree()+1):
        correlation = sum((coeffs[index]*coeffs[index-gap] for index in range(gap, len(coeffs))), sp.Poly(0, midpoint))
        if gap:
            correlation *= 2
        for (tdegree,), value in correlation.terms():
            for (xdegree,), harmonic in harmonics[gap].terms():
                key = tdegree, xdegree
                terms[key] = terms.get(key, 0)+value*harmonic
    return sp.Poly.from_dict(terms, (midpoint, cosine), domain=sp.QQ)


def certify_low_area_envelope():
    base, values, quotient = derive_model_area()
    midpoint, model, cosine = sp.symbols('t c x')
    common = base(values[-1].denom)
    # All c-poles are the independently derived model denominator's poles.
    residual = common/base(quotient.denom)**2
    assert residual.numer.degrees()[1] == residual.denom.degrees()[1] == 0
    for expression in [residual.numer.as_expr(), residual.denom.as_expr()]:
        polynomial = sp.Poly(expression, midpoint, domain=sp.QQ)
        assert polynomial.eval(sp.Rational(47, 100)) != 0 and polynomial.eval(sp.Rational(1, 2)) != 0
        assert polynomial.count_roots(sp.Rational(47, 100), sp.Rational(1, 2)) == 0
    denominator = circle_square(common.as_expr(), midpoint, model, cosine)
    target = sp.Poly(324-300*cosine, midpoint, cosine)*denominator
    for index, value in enumerate(values, 2):
        cleared = value*common
        assert all(degree == 0 for degree in cleared.denom.degrees())
        target -= circle_square(cleared.as_expr(), midpoint, model, cosine)*sp.Rational(1, 2*index-1)
    assert target.degree(midpoint) == 40 and target.degree(cosine) == 9
    minimum, count = certify_projective_positive(target, midpoint, cosine)
    assert count == 410
    print('PASS: independent410 positive projective coefficients and common-denominator nonvanishing', flush=True)
    return minimum


def certify_tail(radius, size):
    scalar = Rat(2, 3)*Rat(4, 3)**6
    numerator = [Rat(0)]*7+[scalar, scalar*Rat(2, 3)]
    denominator = product(polynomial_power([1, -Rat(2, 3)], 4), polynomial_power([1, -2], 4))
    tail_coeffs = rational_coefficients(numerator, denominator, 48)
    larger = Rat(1, 4)
    circle = scalar*larger**7*(1+Rat(2, 3)*larger)/((1-Rat(2, 3)*larger)**4*(1-2*larger)**4)
    hh, ww, _ = series_operators(tail_coeffs, circle, radius)
    cap, _ = model_caps(Rat(2), size)
    ha = (1-Rat(20, 9)*size)/(1+4*size)**2
    upper = (ww+cap*hh)/ha
    assert upper < 1
    return upper


def certify_completion(radius, size):
    larger = Rat(1, 4)
    cm = majorant_value(larger, Rat(2), Rat(16, 15), Rat(1), Rat(1), 3)
    cr = majorant_value(larger, Rat(2), Rat(16, 15), Rat(1), Rat(1), 4)
    uniform = Rat(16, 3)*size/(1-4*size)**2+4*size/(1-4*size)
    assert uniform < 1
    rows = []
    for index in range(192):
        low, high = Rat(index, 192), Rat(index+1, 192)
        peak = Rat(1, 4) if low <= Rat(1, 2) <= high else max(low*(1-low), high*(1-high))
        gamma = min(Rat(1), 2*root_upper(peak))
        kappa = (min(Rat(2), root_upper(Rat(16, 9)*(Rat(53, 100)**2+4*(1-low)*(Rat(1, 2)-low))))
                 if low < Rat(1, 2) else Rat(7, 10))
        beta = Rat(16, 15)*gamma
        remainder = coefficients(kappa, beta, Rat(0), Rat(1), 4)
        assert all(value == 0 for value in remainder[:5])
        linear = coefficients(kappa, beta, Rat(0), Rat(1), 3)
        hr, wr, _ = series_operators(remainder, cr, radius)
        hz, _, _ = series_operators(linear, cm, radius)
        cap, _ = model_caps(kappa, size)
        norm = root_upper(25+600*(1-low))
        jj = (wr+cap*hr+norm*hz)/(1-uniform)
        score = high*jj+root_upper(150*high)+12*high
        assert score < 1/size, (index, float(score))
        rows.append((score, index))
    assert 25/(4*(Rat(16, 27)-Rat(1, 20))) < 12
    return max(rows)


def run_tests():
    target, midpoint, cosine = coercivity_polynomial()
    model_minimum, model_count = certify_projective_positive(target, midpoint, cosine)
    assert model_count == 60
    print('PASS: complete model coercivity extended to t>=47/100', flush=True)
    envelope_minimum = certify_low_area_envelope()
    radius, size = Rat(17, 100), Rat(289, 10000)
    assert Rat(1, 4)-size > Rat(47, 100)**2
    tail = certify_tail(radius, size)
    maximum, index = certify_completion(radius, size)
    print(json.dumps(dict(status='PASS', finite_projective_coefficients=410,
                          finite_minimum=str(envelope_minimum), model_minimum=str(model_minimum),
                          high_tail_upper=float(tail), nonlinear_cells=192,
                          nonlinear_max=float(maximum), nonlinear_index=index,
                          nonlinear_target=float(1/size), method='independent quadratic-field quotient; positive Mobius coefficients; exact recurrences plus complete Cauchy tails'), indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--test', action='store_true', required=True)
    parser.parse_args()
    run_tests()


if __name__ == '__main__':
    main()
