#!/usr/bin/env python3
"""Bounded independent audit of the four-weight classification certificate.

Uses only the standard library. Linear algebra uses determinants and Cramer's
rule, not the classification module's RREF implementation. Every excluded
space is independently rejected using a nonzero nonnegative vector in its row
space. These checks supplement, and do not replace, the written coverage proof.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, permutations, product
from math import gcd, lcm
from pathlib import Path
import json


def check(condition, message):
    if not condition:
        raise ValueError(message)


def determinant(matrix):
    n = len(matrix)
    if not n:
        return 1
    if n == 1:
        return matrix[0][0]
    return sum((-1)**j * matrix[0][j] * determinant(
        [row[:j] + row[j+1:] for row in matrix[1:]])
        for j in range(n))


def pivot_columns(rows):
    r = len(rows)
    return next((cols for cols in combinations(range(4), r)
                 if determinant([[row[j] for j in cols] for row in rows])), None)


def span_test(rows):
    cols = pivot_columns(rows)
    check(cols is not None, 'Dependent purported basis')
    outside = [j for j in range(4) if j not in cols]
    def contains(v):
        return all(determinant([[row[j] for j in (*cols, k)]
                                for row in [*rows, v]]) == 0
                   for k in outside)
    return contains


def exact_solve(matrix, rhs):
    denominator = determinant(matrix)
    if not denominator:
        return None
    result = []
    for k in range(len(matrix)):
        modified = [[rhs[i] if j == k else matrix[i][j]
                     for j in range(len(matrix))] for i in range(len(matrix))]
        result.append(F(determinant(modified), denominator))
    return tuple(result)


def primitive(vector):
    vector = tuple(F(x) for x in vector)
    denominator = lcm(*(x.denominator for x in vector))
    integers = tuple(int(x * denominator) for x in vector)
    common = gcd(*integers)
    check(common > 0, 'Zero primitive ray')
    return tuple(x // common for x in integers)


def integer_rows(encoded):
    return [primitive(row) for row in encoded]


def vertex_rays(basis):
    rank = len(basis)
    rays = set()
    for zeros in combinations(range(4), 3-rank):
        matrix = [list(row) for row in basis] + [[1, 1, 1, 1]]
        matrix += [[int(i == j) for i in range(4)] for j in zeros]
        point = exact_solve(matrix, [0]*rank + [1] + [0]*(3-rank))
        if point is not None and min(point) >= 0:
            rays.add(primitive(point))
    return tuple(sorted(rays))


def positive_dual_witness(basis):
    """Return y in span(basis), y >= 0, sum(y)=1, when one is found."""
    rank = len(basis)
    for zeros in combinations(range(4), rank-1):
        matrix = [[sum(row) for row in basis]]
        matrix += [[row[j] for row in basis] for j in zeros]
        coefficients = exact_solve(matrix, [1] + [0]*(rank-1))
        if coefficients is None:
            continue
        point = tuple(sum(coefficients[k]*basis[k][i] for k in range(rank))
                      for i in range(4))
        if min(point) >= 0 and sum(point) == 1:
            return primitive(point)
    return None


def subset_partition(weights):
    groups = {}
    for size in range(5):
        for indices in combinations(range(4), size):
            value = sum(weights[j] for j in indices)
            mask = sum(2**j for j in indices)
            groups.setdefault(value, []).append(mask)
    return tuple(sorted(tuple(sorted(masks)) for masks in groups.values()))


def template(partition):
    return tuple(sorted(tuple(sum(sum((mask >> j) & 1 for j in range(4)) == k
                                  for mask in group) for k in range(5))
                        for group in partition))


def main():
    root = Path(__file__).resolve().parent
    data = json.loads((root/'classification.json').read_text())
    normals = tuple(h for h in product((-1, 0, 1), repeat=4)
                    if 1 in h and -1 in h and next(x for x in h if x) == 1)
    check(len(normals) == 25, 'Hyperplane count')
    check(normals == tuple(map(tuple, data['hyperplane_normals'])), 'Normals')
    universe = {}
    for rank in range(4):
        for basis in combinations(normals, rank):
            if pivot_columns(basis) is None:
                continue
            contains = span_test(basis)
            closure = tuple(i for i, h in enumerate(normals) if contains(h))
            universe.setdefault(closure, basis)
    check(dict(Counter(len(b) for b in universe.values())) ==
          {0: 1, 1: 25, 2: 181, 3: 315}, 'Independent universe count')
    template_records = {rec['id']: rec for rec in data['templates']}
    seen = set()
    positive = {}
    dual_count = 0
    for is_positive, records in ((True, data['positive_flats']),
                                 (False, data['excluded_flats'])):
        for record in records:
            supplied_basis = integer_rows(record['basis'])
            contains = span_test(supplied_basis)
            closure = tuple(i for i, h in enumerate(normals) if contains(h))
            check(closure in universe and closure not in seen, 'Coverage/duplicate')
            seen.add(closure)
            basis = universe[closure]
            check(len(supplied_basis) == len(basis), 'Certificate basis rank')
            rays = vertex_rays(basis)
            check(rays == tuple(map(tuple, record['rays'])), 'Cramer vertex list')
            uncovered = [i for i in range(4) if all(ray[i] == 0 for ray in rays)]
            if not is_positive:
                check(uncovered == record['uncovered_coordinates'] and uncovered,
                      'Infeasibility coordinate obstruction')
                dual = positive_dual_witness(basis)
                check(dual is not None and min(dual) >= 0 and any(dual) and
                      span_test(basis)(dual), 'Independent dual infeasibility')
                dual_count += 1
                continue
            check(not uncovered, 'Positive space coordinate support')
            w = tuple(record['witness'])
            check(min(w) > 0, 'Witness positivity')
            actual = tuple(i for i, h in enumerate(normals)
                           if sum(h[j]*w[j] for j in range(4)) == 0)
            check(actual == closure == tuple(record['hyperplane_indices']),
                  'Exact witness equality pattern')
            parameter = record['curve_parameter']
            bound = (25-len(closure)) * (len(rays)-1) + 1
            check(record['curve_search_bound'] == bound and 1 <= parameter <= bound,
                  'Polynomial avoidance search bound')
            curve = tuple(sum(parameter**j*ray[i] for j, ray in enumerate(rays))
                          for i in range(4))
            check(primitive(curve) == w, 'Polynomial curve witness')
            partition = subset_partition(w)
            check(partition == tuple(map(tuple, record['subset_partition'])),
                  'Independent subset partition')
            shape = template(partition)
            check(shape == tuple(map(tuple, template_records[record['template_id']]
                                        ['count_vectors'])), 'Template association')
            positive[closure] = (basis, record['template_id'])
    check(seen == set(universe), 'Exhaustive independent universe coverage')
    check(dual_count == 306 and len(positive) == 216, 'Feasible/excluded counts')
    check(Counter(len(basis) for basis, _ in positive.values()) ==
          {0: 1, 1: 25, 2: 115, 3: 75}, 'Feasible rank counts')
    orbit_seen, orbit_templates, orbit_ranks = set(), [], Counter()
    for closure, (basis, template_id) in positive.items():
        if closure in orbit_seen:
            continue
        orbit = set()
        for permutation in permutations(range(4)):
            transformed = [tuple(row[j] for j in permutation) for row in basis]
            contains = span_test(transformed)
            orbit.add(tuple(i for i, h in enumerate(normals) if contains(h)))
        check(orbit <= positive.keys(), 'Orbit completeness')
        check({positive[c][1] for c in orbit} == {template_id}, 'Orbit/template link')
        orbit_seen.update(orbit)
        orbit_templates.append(template_id)
        orbit_ranks[len(basis)] += 1
    check(len(orbit_templates) == len(set(orbit_templates)) == 23,
          'Distinct template per permutation orbit')
    check(dict(orbit_ranks) == {0: 1, 1: 4, 2: 10, 3: 8}, 'Orbit rank counts')
    for identifier, record in template_records.items():
        shape = tuple(map(tuple, record['count_vectors']))
        check(record['outcome_count'] == len(shape), 'Outcome-count metadata')
        check(record['labeled_flat_count'] == sum(t == identifier
                                                 for _, t in positive.values()),
              'Labeled-flat-count metadata')
        multiplicities = [{'vector': list(v), 'multiplicity': n}
                          for v, n in sorted(Counter(shape).items())]
        check(record['vector_multiplicities'] == multiplicities,
              'Vector-multiplicity metadata')
        example = record['small_integer_example']
        check(template(subset_partition(example)) == shape, 'Example template')
        example_closure = tuple(i for i, h in enumerate(normals)
                                if sum(h[j]*example[j] for j in range(4)) == 0)
        example_basis = integer_rows(record['representative_equality_basis'])
        contains = span_test(example_basis)
        check(example_closure == tuple(i for i, h in enumerate(normals) if contains(h)),
              'Representative equality-basis metadata')
        check(record['equality_rank'] == len(universe[example_closure]) == len(example_basis),
              'Representative equality-rank metadata')
    print('Independent determinant universe: 522 spaces (1, 25, 181, 315).')
    print('Cramer vertex enumeration: 216 positive spaces (1, 25, 115, 75).')
    print('Nonzero nonnegative row-space witnesses: all 306 excluded spaces.')
    print('Exact polynomial-avoidance witnesses, partitions, and metadata: PASS.')
    print('Independent coordinate permutation orbits: 23 (1, 4, 10, 8).')


if __name__ == '__main__':
    main()
