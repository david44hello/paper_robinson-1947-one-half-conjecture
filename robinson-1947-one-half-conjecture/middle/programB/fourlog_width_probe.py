#!/usr/bin/env python3
"""Short validated width measurements around attained screen points.
Version 0.10 — Program B, 20261101__21:07 ET. Compare Cartesian-log and rotated
cap-coordinate boxes, at fixed angle and with angle radius in radians.
These local excluded boxes are not continuous global screen certificates.
"""
import argparse
from fractions import Fraction
import json
from pathlib import Path
import time
import numpy as np
from flint import arb, acb, fmpq, ctx
from fourlog_arb_box import necessary_cuts, unit_ball_cuts, decode_cap_coordinates, UnresolvedEnclosure
from fourlog_global_probe import gram_data


def center_for(angle):
    directory = Path(__file__).resolve().parent
    candidates = [json.loads(path.read_text())['best'] for path in
                  directory.glob(f'fourlog_global_{angle}_00*.json')]
    point = min((item for item in candidates if item), key=lambda item: item['required_norm'])['point']
    data = gram_data(angle)['odd']
    norm, kernel = data['norm'], data['kernel']
    phase, transverse = kernel/abs(kernel), np.sqrt(norm**2-abs(kernel)**2)
    first, second = complex(*point[:2]), complex(*point[2:])
    uu = (phase.conjugate()*first+phase*second)/(4*norm)
    vv = (phase.conjugate()*first-phase*second)/(4j*transverse)
    normal_first, normal_second = norm*phase.real, -transverse*phase.imag
    sigma = np.sqrt(normal_first**2+normal_second**2)
    rotated = [(normal_first*uu.real+normal_second*vv.real)/sigma,
               (-normal_second*uu.real+normal_first*vv.real)/sigma, uu.imag, vv.imag]
    return list(point), list(map(float, rotated))


def exclusion(angle, center, radius, chart, varying_angle):
    rational_radius = arb(fmpq(radius.numerator, radius.denominator))
    theta = arb(angle)*arb.pi()/180
    if varying_angle:
        theta += arb(0, rational_radius)
    coordinates = [arb(float(value), rational_radius) for value in center]
    try:
        if chart == 'logs':
            logs = [acb(coordinates[0], coordinates[1]), acb(coordinates[2], coordinates[3])]
            cuts, reason = necessary_cuts(theta, logs, 1)
        else:
            variables, _ = decode_cap_coordinates(theta, coordinates)
            cuts, reason = unit_ball_cuts(theta, variables, 1)
    except UnresolvedEnclosure as error:
        return None, str(error)
    names = [name for name, value in cuts.items() if value > 0]
    return (names[0] if names else None), reason


def measure(angle, center, chart, varying_angle):
    lower, upper = Fraction(1, 2**32), Fraction(1, 4)
    name, _ = exclusion(angle, center, lower, chart, varying_angle)
    if name is None:
        return {'status': 'NO_EXCLUSION_EVEN_AT_TINY_RADIUS'}
    if exclusion(angle, center, upper, chart, varying_angle)[0] is not None:
        return {'status': 'EXCLUDED_AT_MAX_TESTED_RADIUS', 'halfwidth': float(upper)}
    for _ in range(24):
        middle = (lower+upper)/2
        candidate, _ = exclusion(angle, center, middle, chart, varying_angle)
        if candidate is not None:
            lower, name = middle, candidate
        else:
            upper = middle
    assert exclusion(angle, center, lower, chart, varying_angle)[0] is not None
    return {'status': 'VALIDATED_LOCAL_BOX_ONLY', 'excluded_halfwidth': float(lower),
            'excluded_halfwidth_exact': str(lower), 'unresolved_halfwidth': float(upper),
            'cut': name, 'full_width': float(2*lower), 'center': center}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--precision', type=int, required=True)
    parser.add_argument('--output', type=Path, required=True)
    arguments = parser.parse_args()
    ctx.prec, ctx.threads = arguments.precision, 1
    started = time.process_time()
    rows = []
    for angle in [30, 60, 90]:
        cartesian, rotated = center_for(angle)
        for chart, center in [('logs', cartesian), ('cap', rotated)]:
            for varying in [False, True]:
                row = measure(angle, center, chart, varying)
                row.update(angle_degrees=angle, chart=chart, angle_radius_in_radians=varying)
                rows.append(row)
    result = {'status': 'LOCAL_BOX_WIDTHS_NOT_A_GLOBAL_CERTIFICATE', 'precision': arguments.precision,
              'cpu_seconds': time.process_time()-started, 'rows': rows}
    arguments.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'cpu_seconds': result['cpu_seconds'], 'rows': [
        {key: row.get(key) for key in ['angle_degrees', 'chart', 'angle_radius_in_radians',
                                     'excluded_halfwidth', 'cut']} for row in rows]}, indent=2))


if __name__ == '__main__':
    main()
