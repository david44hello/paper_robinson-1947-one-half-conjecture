#!/usr/bin/env python3
"""Independent B7 audit of quadratic model margin and shared area square.
Version 0.10 — program b, 20261101__22:25 EST. Physical quotient differentiation, projective positivity, 64-term recurrences with complete Cauchy tails, 224 independent q cells. No author imports.
"""

import argparse
import json
from fractions import Fraction as Rat
import sympy as sp
from EUC_B3_check_b import product
from EUC_B4_check_b import polynomial_power, rational_coefficients
from EUC_B5_check_b import root_upper, series_operators, model_caps
from EUC_B5_model_check_b import real_laurent_product
from EUC_B6_check_b import derive_model_area, circle_square, projective_coefficients


def positive_rectangle(polynomial, midpoint, cosine):
    degree_t, degree_x = polynomial.degree(midpoint), polynomial.degree(cosine)
    rows = []
    for power in range(degree_t+1):
        values = [Rat(polynomial.nth(power, other)) for other in range(degree_x+1)]
        rows.append(projective_coefficients(values, Rat(-1), Rat(1)))
    output = []
    for power in range(degree_x+1):
        values = [row[power] for row in rows]
        output.extend(projective_coefficients(values, Rat(23, 50), Rat(1, 2)))
    assert min(output) > 0
    return dict(degrees=[degree_t, degree_x], count=len(output), minimum=str(min(output)))


def model_margin(quotient):
    midpoint, parameter, cosine = sp.symbols('t c x')
    numerator, denominator = quotient.numer.as_expr(), quotient.denom.as_expr()
    real_numerator = real_laurent_product(numerator, denominator, parameter, cosine)
    square = circle_square(denominator, midpoint, parameter, cosine)
    baseline_num = sp.Rational(1, 2)-midpoint
    baseline_den = sp.Rational(3, 4)*(sp.Rational(5, 4)+2*midpoint)
    difference = sp.Poly(baseline_den*real_numerator-baseline_num*square.as_expr(), cosine)
    divided, residual = sp.div(difference, sp.Poly(1-cosine, cosine))
    assert residual.is_zero
    multiplier = sp.Rational(113, 50)+sp.Rational(17, 50)*cosine
    target = sp.Poly(divided.as_expr()-multiplier*baseline_den*square.as_expr(), midpoint, cosine)
    result = positive_rectangle(target, midpoint, cosine)
    assert result['degrees'] == [11, 5] and result['count'] == 72
    print('PASS: quadratic model boundary polynomial', result, flush=True)
    return result


def finite_area(base, values, quotient):
    midpoint, parameter, cosine = sp.symbols('t c x')
    common = base(values[-1].denom)
    factor = common/base(quotient.denom)**2
    assert factor.numer.degrees()[1] == factor.denom.degrees()[1] == 0
    for expression in [factor.numer.as_expr(), factor.denom.as_expr()]:
        polynomial = sp.Poly(expression, midpoint, domain=sp.QQ)
        assert polynomial.eval(sp.Rational(23, 50)) != 0
        assert polynomial.eval(sp.Rational(1, 2)) != 0
        assert polynomial.count_roots(sp.Rational(23, 50), sp.Rational(1, 2)) == 0
    square = circle_square(common.as_expr(), midpoint, parameter, cosine)
    target = sp.Poly(280-260*cosine, midpoint, cosine)*square
    for index, value in enumerate(values, 2):
        numerator = value*common
        assert all(degree == 0 for degree in numerator.denom.degrees())
        target -= circle_square(numerator.as_expr(), midpoint, parameter, cosine)*sp.Rational(1, 2*index-1)
    result = positive_rectangle(target, midpoint, cosine)
    assert result['degrees'] == [40, 9] and result['count'] == 410
    print('PASS: finite area envelope and denominator nonvanishing', result, flush=True)
    return result


def area_square(point):
    denominator = (1-Rat(2, 3)*point)**2
    return Rat(256, 243)*point**4/denominator+Rat(4096, 3645)*point**5/(denominator*(1-2*point))


def positive_series(kappa, beta, quadratic):
    """Clear the complete rational denominators before a 64-coefficient recurrence."""
    denominator = [Rat(1), -(2+kappa), 2*kappa-beta]
    if quadratic:
        budget = [Rat(0)]*4+[Rat(256, 243), Rat(4096, 3645)-2*Rat(256, 243)]
        numerator = product(product([0, 3], [1, Rat(2, 3)]), budget)
        numerator = product(numerator, polynomial_power([1, -2], 3))
        denominator = product(polynomial_power([1, -Rat(2, 3)], 2), polynomial_power(denominator, 4))
    else:
        numerator = product([0, 0, 0, Rat(32, 15)], [1, Rat(2, 3)])
        numerator = product(numerator, polynomial_power([1, -2], 2))
        denominator = polynomial_power(denominator, 3)
    result = rational_coefficients(numerator, denominator, 64)
    leading = 5 if quadratic else 3
    assert all(value == 0 for value in result[:leading])
    assert result[leading] > 0
    return result


def circle_caps():
    larger = Rat(1, 4)
    inverse = 1-2*larger-Rat(16, 15)*larger**2/(1-2*larger)
    assert inverse > 0
    linear = 2*larger*(1+Rat(2, 3)*larger)*Rat(16, 15)*larger**2/(1-2*larger)/inverse**3
    quadratic = 3*larger*(1+Rat(2, 3)*larger)*area_square(larger)/inverse**4
    return linear, quadratic


def all_high_tail(radius):
    size, larger = radius**2, Rat(1, 4)
    scale = Rat(20, 33)*Rat(4, 3)**6
    numerator = [Rat(0)]*7+[scale, scale*Rat(2, 3)]
    denominator = product(polynomial_power([1, -Rat(2, 3)], 4), polynomial_power([1, -2], 4))
    coefficients = rational_coefficients(numerator, denominator, 64)
    circle = scale*larger**7*(1+Rat(2, 3)*larger)/((1-Rat(2, 3)*larger)**4*(1-2*larger)**4)
    hh, ww, _ = series_operators(coefficients, circle, radius)
    tcap, _ = model_caps(Rat(2), size)
    ha = (1-Rat(20, 9)*size)/(1+4*size)**2
    result = (ww+tcap*hh)/ha
    assert result < 2
    return result


def independent_cells(radius):
    size = radius**2
    linear_circle, quadratic_circle = circle_caps()
    universal = Rat(16, 3)*size/(1-4*size)**2+4*size/(1-4*size)
    assert universal < 1
    records = []
    model_choices = 0
    for index in range(224):
        low, high = Rat(index, 224), Rat(index+1, 224)
        peak = Rat(1, 4) if low <= Rat(1, 2) <= high else max(low*(1-low), high*(1-high))
        gamma = min(Rat(1), 2*root_upper(peak))
        kappa = (min(Rat(2), root_upper(Rat(16, 9)*(Rat(27, 50)**2+4*(1-low)*(Rat(1, 2)-low))))
                 if low < Rat(1, 2) else Rat(7, 10))
        beta = Rat(16, 15)*gamma
        hr, wr, _ = series_operators(positive_series(kappa, beta, True), quadratic_circle, radius)
        hz, _, _ = series_operators(positive_series(kappa, beta, False), linear_circle, radius)
        tcap, _ = model_caps(kappa, size)
        norm = root_upper(24+520*(1-low))
        model_lower = (1-Rat(20, 9)*size)/(1+kappa**2*size)**2-gamma*hz
        lower_h = max(1-universal, model_lower)
        model_choices += model_lower > 1-universal
        assert lower_h > 0
        remainder = (wr+tcap*hr+norm*hz)/lower_h
        score = high*remainder+root_upper(130*high)+Rat(45, 4)*high
        ratio = score*size/(Rat(24, 25)+Rat(17, 100)*low)
        assert ratio < Rat(199, 200), (index, float(ratio))
        records.append((ratio, index))
    return max(records), model_choices


def algebra_checks():
    real, imag = sp.symbols('x y', real=True)
    defect, area = 2*(1-real), 1-real**2-imag**2
    harmonic = 6-8*real+2*(real**2-imag**2)
    assert sp.expand(harmonic-defect**2-2*area) == 0
    assert (Rat(4, 15))**2 > Rat(1, 15)
    assert Rat(10, 33)**2 > Rat(1, 11)
    assert Rat(1, 3)*Rat(4, 3)**4 == Rat(256, 243)
    assert Rat(4, 15)*Rat(4, 3)**5 == Rat(4096, 3645)
    assert Rat(24, 1)/(4*(Rat(16, 27)-Rat(1, 20))) < Rat(45, 4)
    assert Rat(1271, 900)**2 < 2
    assert Rat(23, 60)**2 == (2-Rat(1271, 900))/4  # Strictness comes from sqrt(2)>1271/900.
    # Physical factors nonzero throughout the wider rectangle, including s=0.
    maximum_size = Rat(1, 4)-Rat(23, 50)**2
    assert 4*maximum_size < 1 and Rat(20, 9)*maximum_size < 1


def run_tests():
    algebra_checks()
    base, values, quotient = derive_model_area()
    model = model_margin(quotient)
    finite = finite_area(base, values, quotient)
    radius = Rat(23, 120)
    assert Rat(1, 4)-radius**2 > Rat(23, 50)**2
    tail = all_high_tail(radius)
    maximum, model_choices = independent_cells(radius)
    print(json.dumps(dict(status='PASS', model=model, finite=finite,
                          full_high_tail_upper=float(tail), cells=224,
                          maximum_ratio=float(maximum[0]), maximum_cell=maximum[1],
                          model_H_cells=model_choices, series_degree=64,
                          method='own exact physical derivatives and projective positivity; independent recurrence and complete Cauchy tails; different q partition'), indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--test', required=True, action='store_true')
    parser.parse_args()
    run_tests()


if __name__ == '__main__':
    main()
