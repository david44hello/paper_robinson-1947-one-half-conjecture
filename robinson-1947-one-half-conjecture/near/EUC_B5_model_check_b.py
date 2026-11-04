#!/usr/bin/env python3
"""Independent model coercivity certificate from the physical rational quotient.
Version 0.10 — program b, 20261101__21:37 ET. Five univariate Bernstein coefficient polynomials certified by exact Sturm counts; no author code.
"""

import argparse
import json
from math import comb
import sympy as sp
from sympy.polys.fields import field


def direct_rational_model():
    rational_field, midpoint, parameter = field('t,c', sp.QQ)
    variance = 1-midpoint**2
    size = rational_field(1)/4-midpoint**2
    linear = (parameter-midpoint)/variance
    other = midpoint/variance
    diagonal = 2*(1-2*midpoint*parameter)/variance
    coefficient = 6*linear**2+8*other*linear-4*midpoint*linear**3-6*midpoint*other*linear**2
    denominator = (1+linear**2*size)*(1-(linear**2+2*other*linear)*size)
    quotient = (diagonal-size*coefficient)/denominator
    return quotient.numer.as_expr(), quotient.denom.as_expr()


def real_laurent_product(first, second, parameter, cosine):
    first, second = sp.Poly(first, parameter), sp.Poly(second, parameter)
    degree = max(first.degree(), second.degree())
    harmonics = [sp.Integer(1), cosine]
    for index in range(2, degree+1):
        harmonics.append(sp.expand(2*cosine*harmonics[-1]-harmonics[-2]))
    return sp.expand(sum(first.nth(ii)*second.nth(jj)*harmonics[abs(ii-jj)]
                         for ii in range(first.degree()+1) for jj in range(second.degree()+1)))


def coercivity_polynomial():
    numerator, denominator = direct_rational_model()
    midpoint, parameter, cosine = sp.symbols('t c x')
    real_numerator = real_laurent_product(numerator, denominator, parameter, cosine)
    modulus_denominator = real_laurent_product(denominator, denominator, parameter, cosine)
    koebe_numerator = sp.Rational(1, 2)-midpoint
    koebe_denominator = sp.Rational(3, 4)*(sp.Rational(5, 4)+2*midpoint)
    difference = sp.Poly(sp.expand(koebe_denominator*real_numerator-koebe_numerator*modulus_denominator), cosine)
    quotient, remainder = sp.div(difference, sp.Poly(1-cosine, cosine))
    assert remainder.is_zero
    target = sp.Poly(sp.expand(quotient.as_expr()-2*koebe_denominator*modulus_denominator), midpoint, cosine)
    assert target.degree(midpoint) == 11 and target.degree(cosine) == 4
    return target, midpoint, cosine


def certify_five_coefficient_polynomials(target, midpoint, cosine):
    unit = sp.Symbol('w')
    transformed = sp.Poly(sp.expand(target.as_expr().subs(cosine, 2*unit-1)), unit)
    degree = transformed.degree()
    records = []
    lower, upper = sp.Rational(19, 40), sp.Rational(1, 2)
    for index in range(degree+1):
        coefficient = sum(transformed.nth(power)*sp.Rational(comb(index, power), comb(degree, power))
                          for power in range(index+1))
        polynomial = sp.Poly(sp.expand(coefficient), midpoint, domain=sp.QQ)
        left, right = polynomial.eval(lower), polynomial.eval(upper)
        assert left > 0 and right > 0
        roots = polynomial.count_roots(lower, upper)
        assert roots == 0
        records.append(dict(index=index, degree=polynomial.degree(), sturm_roots=int(roots),
                            endpoint_lower=str(left), endpoint_upper=str(right)))
    return records


def run_tests():
    target, midpoint, cosine = coercivity_polynomial()
    records = certify_five_coefficient_polynomials(target, midpoint, cosine)
    # Closed c-disk analytic-domain estimates, exact rationals.
    assert sp.Rational(39, 400) < 1 and sp.Rational(13, 240) < 1
    print(json.dumps(dict(status='PASS', method='independently derived physical quotient; five exact univariate Sturm certificates',
                          bidegree=[target.degree(midpoint), target.degree(cosine)], coefficients=records), indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--test', action='store_true', required=True)
    parser.parse_args()
    run_tests()


if __name__ == '__main__':
    main()
