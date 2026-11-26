#!/usr/bin/env python3
"""Exact classification of four positive weighted Bernoulli entropy templates.

Standard library only. No floating point and no assumed integer bound are used
for completeness. The auxiliary small-integer scan supplies short examples only.

Run:
    python proof/classification.py
    python proof/classification.py --verify proof/classification.json

The JSON certificate is written next to this script by default.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as F
from functools import reduce
from itertools import combinations, combinations_with_replacement, permutations, product
import json
from math import comb, gcd, lcm
from pathlib import Path

N = 4
MASKS = tuple(range(1 << N))
BITS = tuple(tuple((m >> i) & 1 for i in range(N)) for m in MASKS)


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def rref(rows, ncols=N):
    """Canonical rational row-space basis; omit all-zero rows."""
    a = [[F(x) for x in row] for row in rows]
    pivot_row = 0
    for col in range(ncols):
        pivot = next((j for j in range(pivot_row, len(a)) if a[j][col]), None)
        if pivot is None:
            continue
        a[pivot_row], a[pivot] = a[pivot], a[pivot_row]
        scale = a[pivot_row][col]
        a[pivot_row] = [x / scale for x in a[pivot_row]]
        for j in range(len(a)):
            if j != pivot_row and a[j][col]:
                scale = a[j][col]
                a[j] = [x - scale * y for x, y in zip(a[j], a[pivot_row])]
        pivot_row += 1
        if pivot_row == len(a):
            break
    return tuple(tuple(row) for row in a if any(row[:ncols]))


def in_span(v, basis):
    residual = [F(x) for x in v]
    for row in basis:
        p = next(i for i, x in enumerate(row) if x)
        scale = residual[p]
        if scale:
            residual = [x - scale * y for x, y in zip(residual, row)]
    return not any(residual)


def hyperplanes():
    """All mixed-sign {-1,0,1} normals, identifying h and -h."""
    hs = []
    for h in product((-1, 0, 1), repeat=N):
        if 1 not in h or -1 not in h:
            continue
        if next(x for x in h if x) == 1:
            hs.append(h)
    hs.sort()
    assert len(hs) == 25
    return tuple(hs)


def all_flats(hs):
    """Every possible equality row space has rank at most three."""
    spaces = {()}
    attempted = Counter({0: 1})
    for size in (1, 2, 3):
        for chosen in combinations(hs, size):
            attempted[size] += 1
            basis = rref(chosen)
            if len(basis) == size:
                spaces.add(basis)
    return sorted(spaces, key=lambda b: (len(b), b)), attempted


def unique_solution(rows, rhs):
    """Return an exact solution when the square system is nonsingular."""
    augmented = rref([tuple(row) + (b,) for row, b in zip(rows, rhs)], N)
    if len(augmented) != N:
        return None
    if any(row[:N] != tuple(F(int(i == j)) for i in range(N))
           for j, row in enumerate(augmented)):
        return None
    return tuple(row[N] for row in augmented)


def primitive_integer(v):
    denominator = lcm(*(x.denominator for x in v))
    values = tuple(int(x * denominator) for x in v)
    divisor = reduce(gcd, (abs(x) for x in values))
    assert divisor
    return tuple(x // divisor for x in values)


def nonnegative_extreme_rays(basis):
    """Enumerate vertices of Aw=0, sum(w)=1, w>=0, as integer rays.

    If dim ker(A)=d, every vertex has d-1 linearly independent active
    coordinate inequalities. Thus fixing every set of d-1 coordinates to zero
    and solving the resulting square system is complete.
    """
    d = N - len(basis)
    rays = set()
    identity = [tuple(int(i == j) for i in range(N)) for j in range(N)]
    for zeros in combinations(range(N), d - 1):
        rows = list(basis) + [(1, 1, 1, 1)] + [identity[j] for j in zeros]
        rhs = [0] * len(basis) + [1] + [0] * (d - 1)
        point = unique_solution(rows, rhs)
        if point is not None and min(point) >= 0:
            rays.add(primitive_integer(point))
    return tuple(sorted(rays))


def generic_positive_witness(basis, rays, hs):
    """Give an integer point in exactly this equality stratum.

    The polynomial curve sum(t**j * ray_j) is strictly positive for t>0.
    Any hyperplane not containing the flat has a nonzero polynomial on this
    curve, of degree at most len(rays)-1. Testing more integers than the sum
    of those degree bounds guarantees an exact-stratum witness.
    """
    if not rays or any(all(ray[i] == 0 for ray in rays) for i in range(N)):
        return None
    assert len(rref(rays)) == N - len(basis)
    closure = tuple(i for i, h in enumerate(hs) if in_span(h, basis))
    outside = tuple(i for i in range(len(hs)) if i not in closure)
    bound = len(outside) * (len(rays) - 1) + 1
    for t in range(1, bound + 1):
        w = tuple(sum(t ** j * ray[i] for j, ray in enumerate(rays))
                  for i in range(N))
        if all(dot(hs[i], w) != 0 for i in outside):
            w = primitive_integer(tuple(F(x) for x in w))
            assert min(w) > 0
            assert all(dot(row, w) == 0 for row in basis)
            assert tuple(i for i, h in enumerate(hs) if dot(h, w) == 0) == closure
            return w, closure, t, bound
    raise AssertionError("The polynomial avoidance bound was violated")


def partition_from_basis(basis):
    remaining = set(MASKS)
    groups = []
    while remaining:
        first = min(remaining)
        group = tuple(m for m in sorted(remaining)
                      if in_span(tuple(x - y for x, y in zip(BITS[m], BITS[first])), basis))
        groups.append(group)
        remaining.difference_update(group)
    return tuple(groups)


def partition_from_weights(w):
    groups = {}
    for m, bits in enumerate(BITS):
        groups.setdefault(dot(bits, w), []).append(m)
    return tuple(sorted(tuple(ms) for ms in groups.values()))


def template_from_partition(groups):
    counts = []
    for group in groups:
        nk = [0] * (N + 1)
        for mask in group:
            nk[mask.bit_count()] += 1
        counts.append(tuple(nk))
    return tuple(sorted(counts))


def template_from_weights(w):
    return template_from_partition(partition_from_weights(w))


def small_examples(bound):
    """This finite scan is solely for readable representatives, not coverage."""
    result = {}
    count = 0
    for w in combinations_with_replacement(range(1, bound + 1), N):
        count += 1
        key = template_from_weights(w)
        if key not in result or (max(w), sum(w), w) < (max(result[key]), sum(result[key]), result[key]):
            result[key] = w
    return result, count


def permutation_orbits(positive_flats):
    """Independently check the quotient by relabeling the four weights."""
    lookup = {decode_basis(flat["basis"]): flat["template_id"] for flat in positive_flats}
    visited = set()
    orbit_records = []
    for basis, template_id in lookup.items():
        if basis in visited:
            continue
        orbit = {rref([tuple(row[i] for i in perm) for row in basis])
                 for perm in permutations(range(N))}
        assert orbit <= lookup.keys()
        assert {lookup[b] for b in orbit} == {template_id}
        visited.update(orbit)
        orbit_records.append({"template_id": template_id, "orbit_size": len(orbit),
                              "rank": len(basis)})
    return sorted(orbit_records, key=lambda rec: rec["template_id"])


def encode_basis(basis):
    return [[str(x) for x in row] for row in basis]


def decode_basis(basis):
    return tuple(tuple(F(x) for x in row) for row in basis)


def build(bound=24):
    hs = hyperplanes()
    spaces, attempted = all_flats(hs)
    feasible = []
    rejected = []
    templates = set()
    for basis in spaces:
        rays = nonnegative_extreme_rays(basis)
        witness = generic_positive_witness(basis, rays, hs)
        if witness is None:
            rejected.append({"basis": encode_basis(basis), "rays": rays,
                             "uncovered_coordinates": [i for i in range(N)
                                 if all(ray[i] == 0 for ray in rays)]})
            continue
        weights, closure, t, t_bound = witness
        groups = partition_from_basis(basis)
        assert groups == partition_from_weights(weights)
        key = template_from_partition(groups)
        assert key == template_from_weights(weights)
        assert tuple(sum(row[k] for row in key) for k in range(N + 1)) == (1, 4, 6, 4, 1)
        templates.add(key)
        feasible.append({"basis": encode_basis(basis), "rank": len(basis),
                         "rays": rays, "witness": weights,
                         "curve_parameter": t, "curve_search_bound": t_bound,
                         "hyperplane_indices": closure, "subset_partition": groups,
                         "template": key})
    ordered = sorted(templates, key=lambda key: (len(key), key))
    ids = {key: f"T{i + 1:02d}" for i, key in enumerate(ordered)}
    examples, scanned = small_examples(bound)
    assert set(examples) <= templates
    missing_short_examples = templates - set(examples)
    for flat in feasible:
        key = flat.pop("template")
        flat["template_id"] = ids[key]
    template_records = []
    for key in ordered:
        example = examples.get(key)
        example_basis = rref([h for h in hs if dot(h, example) == 0]) if example else None
        template_records.append({"id": ids[key], "outcome_count": len(key),
                                 "count_vectors": key,
                                 "vector_multiplicities": [
                                     {"vector": row, "multiplicity": mult}
                                     for row, mult in sorted(Counter(key).items())],
                                 "small_integer_example": example,
                                 "representative_equality_basis": encode_basis(example_basis) if example is not None else None,
                                 "equality_rank": len(example_basis) if example is not None else None,
                                 "labeled_flat_count": sum(f["template_id"] == ids[key] for f in feasible)})
    orbits = permutation_orbits(feasible)
    assert len(orbits) == len(ordered)
    return {
        "schema": "bernoulli-four-positive-weight-entropy-templates-v1",
        "arithmetic": "exact rational; Python fractions.Fraction and arbitrary-precision integers",
        "scope": "all ordered quadruples of strictly positive real weights; all equality strata included",
        "hyperplane_normals": hs,
        "summary": {
            "hyperplane_count": len(hs),
            "independent_basis_candidates_examined": dict(attempted),
            "row_spaces_by_rank": dict(sorted(Counter(len(b) for b in spaces).items())),
            "positive_flats_by_rank": dict(sorted(Counter(f["rank"] for f in feasible).items())),
            "row_space_count": len(spaces),
            "positive_flat_count": len(feasible),
            "excluded_flat_count": len(rejected),
            "template_count": len(ordered),
            "positive_flat_permutation_orbit_count": len(orbits),
            "permutation_orbits_by_rank": dict(sorted(Counter(o["rank"] for o in orbits).items())),
            "auxiliary_integer_scan_max_weight": bound,
            "auxiliary_integer_scan_ordered_quadruples": scanned,
            "templates_without_example_in_auxiliary_scan": len(missing_short_examples),
        },
        "templates": template_records,
        "permutation_orbits": orbits,
        "positive_flats": feasible,
        "excluded_flats": rejected,
    }


def verify(data):
    """Check the finite certificate, including exhaustive flat coverage."""
    if not __debug__:
        raise RuntimeError('Run without -O: assertions are part of the verifier.')
    hs = hyperplanes()
    assert data["hyperplane_normals"] == [list(h) for h in hs]
    all_spaces, attempted = all_flats(hs)
    supplied = []
    template_map = {rec["id"]: tuple(tuple(v) for v in rec["count_vectors"])
                    for rec in data["templates"]}
    assert len(template_map) == len(data["templates"])
    assert len(set(template_map.values())) == len(template_map)
    assert all(key == tuple(sorted(key)) for key in template_map.values())
    seen_templates = set()
    for flat in data["positive_flats"]:
        basis = decode_basis(flat["basis"])
        supplied.append(basis)
        assert rref(basis) == basis
        assert flat["rank"] == len(basis)
        rays = nonnegative_extreme_rays(basis)
        assert rays == tuple(tuple(v) for v in flat["rays"])
        assert len(rref(rays)) == N - len(basis)
        w = tuple(flat["witness"])
        assert len(w) == N and all(type(x) is int for x in w)
        assert min(w) > 0 and all(dot(row, w) == 0 for row in basis)
        actual = tuple(i for i, h in enumerate(hs) if dot(h, w) == 0)
        closure = tuple(i for i, h in enumerate(hs) if in_span(h, basis))
        assert actual == closure == tuple(flat["hyperplane_indices"])
        bound = (len(hs) - len(closure)) * (len(rays) - 1) + 1
        t = flat["curve_parameter"]
        assert type(t) is int and 1 <= t <= bound
        assert flat["curve_search_bound"] == bound
        curve = tuple(F(sum(t ** j * ray[i] for j, ray in enumerate(rays)))
                      for i in range(N))
        assert primitive_integer(curve) == w
        groups = partition_from_weights(w)
        assert groups == tuple(tuple(g) for g in flat["subset_partition"])
        assert groups == partition_from_basis(basis)
        key = template_from_partition(groups)
        assert tuple(sum(row[k] for row in key) for k in range(N + 1)) == (1, 4, 6, 4, 1)
        assert key == template_map[flat["template_id"]]
        seen_templates.add(key)
    for flat in data["excluded_flats"]:
        basis = decode_basis(flat["basis"])
        supplied.append(basis)
        assert rref(basis) == basis
        rays = nonnegative_extreme_rays(basis)
        assert rays == tuple(tuple(v) for v in flat["rays"])
        uncovered = [i for i in range(N) if all(ray[i] == 0 for ray in rays)]
        assert uncovered and uncovered == flat["uncovered_coordinates"]
    assert len(supplied) == len(set(supplied))
    assert set(supplied) == set(all_spaces)
    assert seen_templates == set(template_map.values())
    orbits = permutation_orbits(data["positive_flats"])
    assert orbits == data["permutation_orbits"]
    assert len(orbits) == len(template_map)
    assert len({rec["template_id"] for rec in orbits}) == len(orbits)
    labeled_counts = Counter(flat["template_id"] for flat in data["positive_flats"])
    for orbit in orbits:
        assert orbit["orbit_size"] == labeled_counts[orbit["template_id"]]
    for rec in data["templates"]:
        key = template_map[rec["id"]]
        assert rec["outcome_count"] == len(key)
        assert rec["labeled_flat_count"] == labeled_counts[rec["id"]]
        assert rec["vector_multiplicities"] == [
            {"vector": list(row), "multiplicity": multiplicity}
            for row, multiplicity in sorted(Counter(key).items())]
        w = rec["small_integer_example"]
        if w is not None:
            assert len(w) == N and all(type(x) is int for x in w) and min(w) > 0
            assert template_from_weights(w) == key
            basis = rref([h for h in hs if dot(h, w) == 0])
            assert rec["representative_equality_basis"] == encode_basis(basis)
            assert rec["equality_rank"] == len(basis)
        else:
            assert rec["representative_equality_basis"] is None
            assert rec["equality_rank"] is None
    summary = data["summary"]
    expected_summary = {
        "hyperplane_count": len(hs),
        "independent_basis_candidates_examined": {str(k): v for k, v in attempted.items()},
        "row_spaces_by_rank": {str(k): v for k, v in Counter(len(b) for b in all_spaces).items()},
        "positive_flats_by_rank": {str(k): v for k, v in
                                  Counter(len(decode_basis(flat["basis"]))
                                          for flat in data["positive_flats"]).items()},
        "row_space_count": len(all_spaces),
        "positive_flat_count": len(data["positive_flats"]),
        "excluded_flat_count": len(data["excluded_flats"]),
        "template_count": len(seen_templates),
        "positive_flat_permutation_orbit_count": len(orbits),
        "permutation_orbits_by_rank": {str(k): v for k, v in
                                     Counter(rec["rank"] for rec in orbits).items()},
    }
    assert all(summary[k] == v for k, v in expected_summary.items())
    example_bound = summary["auxiliary_integer_scan_max_weight"]
    assert type(example_bound) is int and example_bound >= 0
    assert summary["auxiliary_integer_scan_ordered_quadruples"] == comb(example_bound + N - 1, N)
    assert summary["templates_without_example_in_auxiliary_scan"] == sum(
        rec["small_integer_example"] is None for rec in data["templates"])
    assert all(rec["small_integer_example"] is None or
               max(rec["small_integer_example"]) <= example_bound for rec in data["templates"])
    return True


def main():
    if not __debug__:
        raise SystemExit('Run without -O: assertions are part of the verifier.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("classification.json"))
    parser.add_argument("--example-bound", type=int, default=24)
    parser.add_argument("--verify", type=Path)
    args = parser.parse_args()
    if args.verify:
        data = json.loads(args.verify.read_text())
        verify(data)
        print("Exact coverage certificate verified.")
        print(json.dumps(data["summary"], indent=2, sort_keys=True))
    else:
        data = build(args.example_bound)
        serialized = json.dumps(data, indent=2, sort_keys=True) + "\n"
        verify(json.loads(serialized))
        args.output.write_text(serialized)
        print(json.dumps(data["summary"], indent=2, sort_keys=True))
        for rec in data["templates"]:
            print(rec["id"], rec["small_integer_example"], "outcomes=", rec["outcome_count"],
                  "flats=", rec["labeled_flat_count"])
        print("Wrote and verified:", args.output)


if __name__ == "__main__":
    main()
