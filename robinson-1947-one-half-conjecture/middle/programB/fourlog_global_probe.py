#!/usr/bin/env python3
"""Independent global exploration of the four-real collision screen.
Version 0.30 — Program B, 20261101__20:28 ET. Interleave broad complex starts
with near-Koebe seeds and retain each starting point; short budgets per branch.
All outputs are UNCERTIFIED numerical searches, never global lower bounds.
"""
import argparse
import json
import math
from pathlib import Path
import time
import numpy as np
from scipy.optimize import differential_evolution, minimize


def gram_data(angle):
    theta = math.radians(angle)
    endpoint = .5 * np.exp(.5j * theta)
    root = np.sqrt(endpoint)
    data = {'z': endpoint, 'w': endpoint.conjugate(), 's': root, 't': root.conjugate()}
    for label, norm, kernel, jet, jet_kernel, derivative_norm in [
        ('odd', np.arctanh(.5), np.arctanh(endpoint), 2/3, endpoint/(1-endpoint**2), 10/9),
        ('even', -.5*np.log(.75), -.5*np.log(1-endpoint**2), 1/3, endpoint**2/(1-endpoint**2), 8/9)]:
        gram = np.array([[norm, kernel.conjugate()], [kernel, norm]], complex)
        mixed = np.array([[jet, jet_kernel.conjugate()], [jet_kernel, jet]], complex)
        inverse = np.linalg.inv(gram)
        projection = inverse @ mixed
        residual = float((derivative_norm - mixed[:, 0].conj() @ inverse @ mixed[:, 0]).real)
        assert residual > 0
        modulus = abs(kernel)
        phase = np.sqrt(kernel/modulus)
        first, second = np.sqrt((norm+modulus)/2), np.sqrt((norm-modulus)/2)
        coordinates = np.array([[phase*first, phase.conjugate()*first],
                                [1j*phase*second, -1j*phase.conjugate()*second]])
        np.testing.assert_allclose(coordinates.conj().T @ coordinates, gram, atol=2e-15)
        data[label] = {'norm': norm, 'kernel': kernel, 'gram': gram,
                       'inverse_bar': inverse.conjugate(), 'projection': projection,
                       'residual': residual, 'coordinates_inverse': np.linalg.inv(coordinates)}
    return data


def fixed_screen(logs, ratio, data):
    first, second = np.exp(logs)
    left, right, root, conjugate_root = [data[key] for key in ['z', 'w', 's', 't']]
    difference = np.log(root/(conjugate_root*ratio))
    plus_exp, minus_exp = np.exp(difference/2), np.exp(-difference/2)
    minus_log = np.log((root*minus_exp-conjugate_root*plus_exp)/(root-conjugate_root))
    plus_log = np.log((root*minus_exp+conjugate_root*plus_exp)/(root+conjugate_root))
    odd_form = np.array([[logs[0]/2, (minus_log-plus_log)/2],
                         [(minus_log-plus_log)/2, logs[1]/2]])
    even_form = np.array([[(difference+logs[0])/2, (minus_log+plus_log)/2],
                          [(minus_log+plus_log)/2, (-difference+logs[1])/2]])
    odd = data['odd']
    compressed = odd['coordinates_inverse'].T @ odd_form @ odd['coordinates_inverse']
    norm = float(np.linalg.svd(compressed, compute_uv=False)[0])
    projected_gram = odd_form.conj().T @ odd['inverse_bar'] @ odd_form
    denominator = ratio*ratio-1
    targets_odd = [first*ratio/denominator-root*conjugate_root/(left-right),
                   -second*ratio/denominator+root*conjugate_root/(left-right)]
    bounds = [norm]
    for index, column in [(0, 1), (1, 0)]:
        residual = targets_odd[index] - odd['projection'][:, index] @ odd_form[:, column]
        square = (projected_gram[column, column].real + abs(residual)**2/odd['residual'])/odd['norm']
        bounds.append(math.sqrt(max(0, square)))
    even = data['even']
    difference_column = even_form[:, 0]-even_form[:, 1]
    value_square = float((difference_column.conj() @ even['inverse_bar'] @ difference_column).real)
    value_square /= 2*(even['norm']-even['kernel'].real)
    bounds.append(math.sqrt(max(0, value_square)))
    targets_even = [first/denominator-right/(left-right),
                    -second*ratio*ratio/denominator+left/(left-right)]
    ones = np.ones(2, complex)
    coefficients = []
    for index, column in [(0, 1), (1, 0)]:
        fixed = even_form[:, column]
        projection = even['projection'][:, index]
        slope = projection @ ones
        residual = targets_even[index] - projection @ fixed
        quadratic = ((ones @ even['inverse_bar'] @ ones).real + abs(slope)**2/even['residual'])/even['norm']
        linear = (ones @ even['inverse_bar'] @ fixed - slope.conjugate()*residual/even['residual'])/even['norm']
        constant = ((fixed.conj() @ even['inverse_bar'] @ fixed).real + abs(residual)**2/even['residual'])/even['norm']
        coefficients.append((quadratic, linear, constant))
    quadratic, linear, constant = np.mean(coefficients, axis=0)
    average_square = float((constant-abs(linear)**2/quadratic).real)
    bounds.append(math.sqrt(max(0, average_square)))
    domains = [math.log(3)**2-abs(value)**2 for value in logs]
    domains.extend([(2*math.log(2))**2-abs(value)**2 for value in [difference, minus_log, plus_log]])
    domains.extend([abs(ratio-1)-5/143, abs(ratio+1)-20/117])
    return np.array(bounds), np.array(domains), {
        'Delta': difference, 'mixed_logs': [minus_log, plus_log], 'ratio': ratio,
        'best_average_even_T': -linear/quadratic}


def screen(point, data, branch):
    logs = np.array([point[0]+1j*point[1], point[2]+1j*point[3]])
    ratio = branch*np.sqrt((1+np.exp(logs[1]))/(1+np.exp(logs[0])))
    if min(abs(ratio-1), abs(ratio+1)) < 1e-11:
        return np.full(5, 1e5), np.full(7, -1e5), {'ratio': ratio}
    return fixed_screen(logs, ratio, data)


def serialize_complex(value):
    return [float(value.real), float(value.imag)]


def candidate_record(point, data, branch, stage, success, evaluations):
    bounds, domains, auxiliary = screen(point, data, branch)
    return {'point': list(map(float, point[:4])), 'ell': [list(map(float, point[:2])), list(map(float, point[2:4]))],
            'branch': branch, 'required_norm': float(max(bounds)), 'components': list(map(float, bounds)),
            'domain_slacks': list(map(float, domains)), 'admissible_numeric': bool(min(domains) >= -1e-8),
            'ratio': serialize_complex(auxiliary['ratio']),
            'Delta': serialize_complex(auxiliary['Delta']) if 'Delta' in auxiliary else None,
            'stage': stage, 'optimizer_success': bool(success), 'evaluations': int(evaluations),
            'asymmetry': float(abs(complex(*point[:2])-complex(*point[2:4]).conjugate()))}


def probe(arguments):
    cpu = time.process_time()
    data = gram_data(arguments.angle)
    generator = np.random.default_rng(arguments.seed)
    radius = math.log(3)
    box = [(-radius, radius)]*4
    rows = []
    for branch in [1, -1]:
        branch_started = time.process_time()
        def penalty(point):
            bounds, domains, _ = screen(point, data, branch)
            return float(max(bounds)+500*np.sum(np.minimum(domains, 0)**2))
        result = differential_evolution(penalty, box, popsize=arguments.population,
                                        maxiter=arguments.generations, seed=generator,
                                        polish=False, tol=1e-8, workers=1)
        rows.append(candidate_record(result.x, data, branch, 'four-real differential evolution',
                                     result.success, result.nfev))
        seeds = [result.x]
        if branch == 1:
            near = -2*np.arctanh(data['z'])
            near_point = np.array([near.real, near.imag, near.real, -near.imag])
            seeds += [near_point, -near_point]
            for index in range(max(0, arguments.starts-3)):
                if index % 2 == 0:
                    scale = [1e-4, .002, .02, .1][(index//2) % 4]
                    initial = near_point + scale*generator.normal(size=4)
                else:
                    moduli = radius*np.sqrt(generator.uniform(size=2))
                    phases = generator.uniform(-math.pi, math.pi, 2)
                    logs = moduli*np.exp(1j*phases)
                    initial = np.array([logs[0].real, logs[0].imag, logs[1].real, logs[1].imag])
                seeds.append(np.clip(initial, -radius, radius))
        else:
            # This branch is analytically excluded below90deg by the Delta phase bound.
            # Still search it independently and retain its actual domain failures.
            seeds += [generator.uniform(-radius, radius, 4) for _ in range(3)]
        for initial in seeds:
            if time.process_time()-branch_started >= arguments.branch_cpu_seconds:
                break
            bounds, _, _ = screen(initial, data, branch)
            starting = np.r_[initial, min(1e5, max(bounds)+.01)]
            def constraint(point):
                required, domains, _ = screen(point, data, branch)
                return np.r_[point[4]-required, domains]
            result = minimize(lambda point: point[4], starting,
                              jac=lambda point: np.array([0., 0., 0., 0., 1.]),
                              method='SLSQP', bounds=box+[(0, 1e6)],
                              constraints=[{'type': 'ineq', 'fun': constraint}],
                              options={'maxiter': arguments.iterations, 'ftol': 2e-11})
            record = candidate_record(result.x, data, branch, 'asymmetric epigraph multistart',
                                      result.success, result.nfev)
            record['initial_point'] = list(map(float, initial))
            rows.append(record)
    admissible = [row for row in rows if row['admissible_numeric']]
    best = min(admissible, key=lambda row: row['required_norm']) if admissible else None
    output = {'status': 'UNCERTIFIED_MULTISTART_FOUR_REAL_SCREEN', 'angle_degrees': arguments.angle,
              'seed': arguments.seed, 'settings': vars(arguments) | {'output': str(arguments.output)},
              'component_order': ['odd_O2', 'odd_jet1', 'odd_jet2', 'even_value', 'even_average_jet'],
              'cpu_seconds': time.process_time()-cpu, 'attempts': rows, 'best': best,
              'admissible_attempts': len(admissible), 'point_at_or_below_one_found':
              any(row['required_norm'] <= 1 for row in admissible)}
    arguments.output.write_text(json.dumps(output, indent=2, allow_nan=False)+'\n')
    print(json.dumps({key: output[key] for key in ['angle_degrees', 'cpu_seconds', 'admissible_attempts',
                                                'point_at_or_below_one_found', 'best']}, indent=2))


def tests():
    for degree in [15, 30, 60, 90]:
        data = gram_data(degree)
        for sign in [-1, 1]:
            logs = 2*sign*np.arctanh(np.array([data['z'], data['w']]))
            ratio = (data['s']/(1-sign*data['z']))/(data['t']/(1-sign*data['w']))
            bounds, _, _ = fixed_screen(logs, ratio, data)
            np.testing.assert_allclose(bounds[:4], np.ones(4), atol=3e-9)
            assert bounds[-1] <= 1+3e-9, bounds
    print('PASS: independent real Gram basis, odd compression, both odd jets, even values and averaged jets on Koebe signs')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--test', action='store_true')
    parser.add_argument('--angle', type=float)
    parser.add_argument('--starts', type=int)
    parser.add_argument('--population', type=int)
    parser.add_argument('--generations', type=int)
    parser.add_argument('--iterations', type=int)
    parser.add_argument('--seed', type=int)
    parser.add_argument('--branch-cpu-seconds', type=float)
    parser.add_argument('--output', type=Path)
    arguments = parser.parse_args()
    if arguments.test:
        tests()
        return
    if any(value is None for key, value in vars(arguments).items() if key != 'test'):
        parser.error('all probe settings must be explicit')
    probe(arguments)


if __name__ == '__main__':
    main()
