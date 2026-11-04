#!/usr/bin/env python3
"""First program for Lemma 4.8: the 256 cells of [0, 1] in exact rational arithmetic.
Version 0.30 — program b. Exact q-circle cap max(1/(1+L), 2-8low/3); reuses the B8 polynomials and complete 96-term tails.
"""

import argparse
from fractions import Fraction as Rat
import json
from EUC_B5_check_b import root_upper, series_operators, model_caps
from check_B8_b import cell_caps, cell_high_tail, extended_sharp_coefficients, sharp_circle_caps, quadratic_minimum


def completion_test(slope, norm_constant, high, endpoint):
    offset = Rat(16, 27)-Rat(1, 20)
    affine = min(offset, offset+slope*endpoint)
    polynomial = quadratic_minimum(offset**2, 2*offset*slope-norm_constant*high,
                                   slope*slope-130*high, endpoint)
    return min(affine, polynomial)


def exact_caps(low, high, lower):
    gamma, _ = cell_caps(low, high, lower)
    kappa = max(1/(1+lower), 2-Rat(8, 3)*low)
    assert 0 < kappa <= 2
    return gamma, kappa


def inspect_cell(radius, low, high, lower, caps, diagnostics):
    size, endpoint = radius**2, 4*(1-low)
    gamma, kappa = caps(low, high, lower)
    linear_circle, quadratic_circle = sharp_circle_caps()
    hr, wr, _ = series_operators(extended_sharp_coefficients(kappa, Rat(16, 15)*gamma, True), quadratic_circle, radius)
    hz, _, _ = series_operators(extended_sharp_coefficients(kappa, Rat(16, 15)*gamma, False), linear_circle, radius)
    tail = cell_high_tail(kappa, radius)
    norm_constant = 20+tail*tail
    norm = root_upper(norm_constant+130*endpoint)
    tcap, _ = model_caps(kappa, size)
    universal_h = 1-Rat(16, 3)*size/(1-4*size)**2-4*size/(1-4*size)
    lcap = min(Rat(20, 9), kappa**2+Rat(4, 3)*kappa)
    model_h = (1-lcap*size)/(1+kappa**2*size)**2
    lower_h = max(universal_h, model_h-gamma*hz)
    assert lower_h > 0
    contributions = [wr/lower_h, tcap*hr/lower_h, norm*hz/lower_h]
    margin_over_size = (Rat(22, 25)+Rat(21, 100)*low)/size
    remainder = sum(contributions)
    minimum = completion_test(margin_over_size-high*remainder, norm_constant, high, endpoint)
    counterfactuals = {}
    if diagnostics:
        no_tail_cost = (wr+tcap*hr+root_upper(20+130*endpoint)*hz)/lower_h
        counterfactuals = dict(without_tail_allowance=completion_test(margin_over_size-high*no_tail_cost, Rat(20), high, endpoint),
                          without_WR=completion_test(margin_over_size-high*(remainder-contributions[0]), norm_constant, high, endpoint),
                          without_Tcap_HR=completion_test(margin_over_size-high*(remainder-contributions[1]), norm_constant, high, endpoint),
                          without_norm_HZ=completion_test(margin_over_size-high*(remainder-contributions[2]), norm_constant, high, endpoint),
                          H_lower_one=completion_test(margin_over_size-high*remainder*lower_h, norm_constant, high, endpoint))
    return minimum, dict(radius=str(radius), q_low=str(low), q_high=str(high), kappa=float(kappa),
                         Ktail=float(tail), Mcell=float(norm_constant), H_universal=float(universal_h),
                         H_model=float(model_h), gamma_HZ=float(gamma*hz), Hcell=float(lower_h),
                         J_WR=float(contributions[0]), J_Tcap_HR=float(contributions[1]), J_norm_HZ=float(contributions[2]),
                         J_total=float(remainder), d=float(margin_over_size-high*remainder),
                         minimum=float(minimum), pass_certificate=minimum>0,
                         diagnostic_counterfactuals={key: float(value) for key, value in counterfactuals.items()})


def diagnose():
    reports = []
    for radius, index in [(Rat(87, 400), 57), (Rat(87, 400), 61), (Rat(17, 80), 57)]:
        low, high = Rat(index, 256), Rat(index+1, 256)
        _, report = inspect_cell(radius, low, high, Rat(9, 20), cell_caps, True)
        reports.append(report)
    midpoint = Rat(123, 512)
    _, report = inspect_cell(Rat(87, 400), midpoint, midpoint, Rat(9, 20), cell_caps, True)
    report['purpose'] = 'zero-width q diagnostic; not a continuous certificate'
    reports.append(report)
    print(json.dumps(reports, indent=2))


def certificate(radius, cells):
    lower = Rat(9, 20)
    assert 0 < radius < Rat(1, 4) and Rat(1, 4)-radius**2 >= lower**2
    assert cells > 0
    results = []
    for index in range(cells):
        minimum, report = inspect_cell(radius, Rat(index, cells), Rat(index+1, cells), lower, exact_caps, False)
        results.append((minimum, index, report))
    minimum, index, report = min(results, key=lambda result: result[:2])
    print(json.dumps(dict(status='PASS' if minimum > 0 else 'FAIL', radius=str(radius), cells=cells,
                          minimum=float(minimum), minimum_cell=index, worst_cell=report,
                          pass_certificate=minimum>0), indent=2), flush=True)
    assert minimum > 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--diagnose', action='store_true')
    mode.add_argument('--test', action='store_true')
    parser.add_argument('--radius', type=Rat)
    parser.add_argument('--cells', type=int)
    arguments = parser.parse_args()
    if arguments.diagnose:
        diagnose()
    elif arguments.radius is None or arguments.cells is None:
        parser.error('--radius and --cells are required with --test')
    else:
        certificate(arguments.radius, arguments.cells)


if __name__ == '__main__':
    main()
