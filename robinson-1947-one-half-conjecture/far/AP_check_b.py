#!/usr/bin/env python3
"""Independent exact checks for program a's AP proof.
Version 0.10 — program b, 20261101__19:06 ET. Rational certificates; --test.
"""

import argparse
from fractions import Fraction as Q
from math import factorial
import json
import sympy as sp


def exponential_bounds(argument, order):
    lower = sum((argument**index/Q(factorial(index)) for index in range(order+1)), Q(0))
    remainder = argument**(order+1)/factorial(order+1)/(1-argument/(order+2))
    return lower, lower+remainder


def check_transcendental_certificates():
    radius = Q(1387, 1000)
    angle = Q(271, 200)
    sine_upper = sum(((-1)**index*angle**(2*index+1)/factorial(2*index+1) for index in range(5)), Q(0))
    cosine_lower = sum(((-1)**index*angle**(2*index)/factorial(2*index) for index in range(6)), Q(0))
    assert angle-radius*sine_upper > 0 and cosine_lower > Q(107, 500)
    assert exponential_bounds(radius, 12)[0] > 4
    assert exponential_bounds(radius, 12)[1] < 5
    assert exponential_bounds(Q(148409, 500000), 10)[1] < Q(214, 159)
    assert exponential_bounds(Q(2), 9)[0] > Q(2000, 271)
    assert exponential_bounds(Q(13, 200), 2)[0] > Q(16, 15)
    assert exponential_bounds(Q(511, 1000), 8)[0] > Q(5, 3)


def check_poisson_identity():
    radial, cosine = sp.symbols('a c')
    kernels = (1-radial**2)/(1+radial**2-2*radial*cosine)
    kernels += (1-radial**2)/(1+radial**2+2*radial*cosine)
    expected = 2*(1-radial**4)/((1-radial**2)**2+4*radial**2*(1-cosine**2))
    assert sp.cancel(kernels-expected) == 0


def check_final_constants():
    minimum, coefficient = Q(159, 1000), Q(1271, 1000)
    moment = Q(9, 25)*coefficient/(1-minimum)
    radial = Q(5, 6)
    coupled = 2*minimum+(1-minimum)*2*(1-radial**4)/(1+radial**4+2*radial**2*moment)
    assert moment < 1 and coupled == Q(431206711, 609792250)
    assert coupled > Q(707, 1000)
    assert Q(16, 225)*Q(13, 200) < Q(17, 250)**2
    assert Q(34, 225)*Q(511, 1000) < Q(139, 500)**2
    assert 2*(Q(17, 250)+Q(139, 500)) == Q(173, 250)
    assert coupled-Q(173, 250) > Q(3, 200)
    return {'status': 'PASS', 'mu2_bound': str(moment),
            'coupled_p_margin': str(coupled),
            'final_margin': str(coupled-Q(173, 250))}


def run_checks():
    check_transcendental_certificates()
    check_poisson_identity()
    print(json.dumps(check_final_constants(), indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--test', action='store_true', required=True)
    parser.parse_args()
    run_checks()


if __name__ == '__main__':
    main()
