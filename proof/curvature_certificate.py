#!/usr/bin/env python3
"""Exact rational certificate for entropy curvature of four-Bernoulli templates.

This program uses only Python's standard library.  All enclosures are rational;
there is no floating point arithmetic in the verification.  Template completeness
is a separate combinatorial obligation, handled by proof/classification.py.
"""
from __future__ import annotations
from collections import defaultdict
from dataclasses import dataclass
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations_with_replacement
from math import comb
import argparse
import json
from pathlib import Path


def trim(a):
    a = list(map(F, a))
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return tuple(a)


def add(a, b):
    return trim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
                 for i in range(max(len(a), len(b)))])


def mul(a, b):
    c = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i+j] += x*y
    return trim(c)


def scale(a, s):
    return trim([s*x for x in a])


def derivative(a):
    return trim([i*a[i] for i in range(1, len(a))] or [0])


def divide_exact(a, b):
    a, b = list(trim(a)), trim(b)
    if a == [F(0)]:
        return (F(0),)
    c = [F(0)] * (len(a)-len(b)+1)
    while len(a) >= len(b):
        j = len(a)-len(b)
        c[j] = a[-1]/b[-1]
        for i in range(len(b)):
            a[i+j] -= c[j]*b[i]
        a = list(trim(a))
        if a == [F(0)]:
            break
    assert all(x == 0 for x in a), 'Non-exact polynomial division'
    return trim(c)


def monomial_pq(k, ell):
    return trim([0]*k + [(-1)**i*comb(ell, i) for i in range(ell+1)])


@dataclass(frozen=True)
class I:
    lo: F
    hi: F

    def __post_init__(self):
        object.__setattr__(self, 'lo', F(self.lo))
        object.__setattr__(self, 'hi', F(self.hi))
        assert self.lo <= self.hi

    @staticmethod
    def lift(x):
        return x if isinstance(x, I) else I(x, x)

    def __add__(self, other):
        other = I.lift(other)
        return I(self.lo+other.lo, self.hi+other.hi)

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + -I.lift(other)

    def __rsub__(self, other):
        return I.lift(other) + -self

    def __mul__(self, other):
        other = I.lift(other)
        z = [self.lo*other.lo, self.lo*other.hi,
             self.hi*other.lo, self.hi*other.hi]
        return I(min(z), max(z))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = I.lift(other)
        assert other.lo > 0 or other.hi < 0, 'Division interval contains zero'
        return self*I(1/other.hi, 1/other.lo)


def evaluate(a, x):
    value = I(0, 0)
    for c in reversed(a):
        value = value*x + c
    return value


def log_series(y, terms=24):
    """Bounds for log(y), 1 <= y <= 2, by the atanh series."""
    assert 1 <= y <= 2
    z = (y-1)/(y+1)
    z2 = z*z
    power = z
    value = F(0)
    for j in range(terms):
        value += 2*power/(2*j+1)
        power *= z2
    remainder = 2*power/((2*terms+1)*(1-z2))
    return I(value, value+remainder)


LOG2 = log_series(F(2))
ROUND_DEN = 2**60


def dyadic_outer(v):
    low = (v.lo*ROUND_DEN).__floor__()
    high = (v.hi*ROUND_DEN).__ceil__()
    return I(F(low, ROUND_DEN), F(high, ROUND_DEN))


@lru_cache(maxsize=None)
def log_exact_bounds(x):
    x = F(x)
    assert x > 0
    y, k = x, 0
    while y < 1:
        y *= 2
        k -= 1
    while y > 2:
        y /= 2
        k += 1
    return dyadic_outer(log_series(y) + k*LOG2)


def log_interval(x):
    assert x.lo > 0
    return I(log_exact_bounds(x.lo).lo, log_exact_bounds(x.hi).hi)


def xlog_interval(x):
    assert 0 <= x.lo <= x.hi <= 1
    if x.lo == 0:
        # t log t decreases on (0,1/4], since log(4)>1.
        assert x.hi <= F(1, 4)
        if x.hi == 0:
            return I(0, 0)
        return I(x.hi*log_exact_bounds(x.hi).lo, 0)
    return x*log_interval(x)


def template_for(weights):
    groups = defaultdict(lambda: [0]*5)
    for mask in range(16):
        s = sum(weights[j] for j in range(4) if mask & (1 << j))
        groups[s][mask.bit_count()] += 1
    return tuple(sorted(tuple(v) for v in groups.values()))


def small_integer_templates():
    patterns = {}
    for weights in combinations_with_replacement(range(1, 9), 4):
        patterns.setdefault(template_for(weights), weights)
    assert len(patterns) == 23
    return patterns


def prepare(template):
    A, B, total = (F(0),), (F(0),), (F(0),)
    residuals = []
    for v in template:
        inds = [k for k in range(5) if v[k]]
        amin, bmin = min(inds), 4-max(inds)
        Q, R = (F(0),), (F(0),)
        for k in inds:
            Q = add(Q, scale(monomial_pq(k, 4-k), v[k]))
            R = add(R, scale(monomial_pq(k-amin, 4-bmin-k), v[k]))
        assert Q == mul(monomial_pq(amin, bmin), R)
        total = add(total, Q)
        A = add(A, scale(Q, amin))
        B = add(B, scale(Q, bmin))
        if R != (F(1),):
            residuals.append((Q, derivative(Q), derivative(derivative(Q)),
                              R, derivative(R), derivative(derivative(R))))
    assert total == (F(1),)
    p, q = (F(0), F(1)), (F(1), F(-1))
    Aprime, Bprime = derivative(A), derivative(B)
    P = add(add(scale(mul(q, Aprime), 2), scale(mul(q, divide_exact(A, p)), -1)),
            add(scale(mul(p, Bprime), -2), scale(mul(p, divide_exact(B, q)), -1)))
    return P, derivative(Aprime), derivative(Bprime), residuals


def curvature_bound(data, left, right):
    """Enclose T(p)=-p(1-p) H''(p), including its endpoint limit."""
    p = I(left, right)
    q = 1-p
    P, A2, B2, terms = data
    value = (evaluate(P, p) + q*evaluate(A2, p)*xlog_interval(p)
             + p*evaluate(B2, p)*xlog_interval(q))
    correction = I(0, 0)
    for Q, Q1, Q2, R, R1, R2 in terms:
        r, r1, r2 = evaluate(R, p), evaluate(R1, p), evaluate(R2, p)
        u, u1, u2 = evaluate(Q, p), evaluate(Q1, p), evaluate(Q2, p)
        correction += u2*log_interval(r) + 2*u1*r1/r + u*(r2/r-(r1/r)*(r1/r))
    return dyadic_outer(value + p*q*correction)


def certify_one(template):
    data = prepare(template)
    split = F(1, 1024)
    pending = [(F(0), split), (split, F(1, 2))]
    cells = []
    while pending:
        a, b = pending.pop()
        try:
            result = curvature_bound(data, a, b)
        except AssertionError:
            result = I(-1, 1)
        if result.lo > 0:
            cells.append((a, b, result.lo))
        else:
            assert b-a > F(1, 2**24), 'Refinement limit reached'
            mid = (a+b)/2
            pending.extend([(a, mid), (mid, b)])
    cells.sort()
    assert cells[0][0] == 0 and cells[-1][1] == F(1, 2)
    assert all(cells[i][1] == cells[i+1][0] for i in range(len(cells)-1))
    return cells


def verify_certificate(document):
    """Recheck fixed rational cells, without rerunning adaptive subdivision."""
    if not __debug__:
        raise RuntimeError('Run without -O: assertions are part of the verifier.')
    seen = set()
    for record in document['templates']:
        template = tuple(tuple(v) for v in record['template'])
        assert template not in seen
        seen.add(template)
        assert template_for(tuple(record['weights'])) == template
        assert sorted(template) == sorted(tuple(reversed(v)) for v in template)
        data = prepare(template)
        previous = F(0)
        lower_bounds = []
        for a_text, b_text, c_text in record['cells']:
            a, b, c = map(F, (a_text, b_text, c_text))
            assert a == previous and a < b <= F(1, 2)
            assert c > 0
            actual = curvature_bound(data, a, b)
            assert actual.lo >= c
            lower_bounds.append(c)
            previous = b
        assert previous == F(1, 2)
        assert min(lower_bounds) == F(record['lower_bound'])
    assert len(seen) == 23
    assert document['total_cells'] == sum(len(r['cells']) for r in document['templates'])
    return seen


def main():
    if not __debug__:
        raise SystemExit('Run without -O: assertions are part of the verifier.')
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path)
    parser.add_argument('--verify', type=Path)
    args = parser.parse_args()
    if args.verify:
        document = json.loads(args.verify.read_text())
        verify_certificate(document)
        print('Exact interval certificate verified for all 23 templates.')
        return
    records = []
    for idx, (template, weights) in enumerate(small_integer_templates().items(), 1):
        cells = certify_one(template)
        record = {'id': idx, 'weights': weights, 'template': template,
                  'cells': [[str(a), str(b), str(c)] for a, b, c in cells],
                  'lower_bound': str(min(c for a, b, c in cells))}
        records.append(record)
        print('VERIFIED', idx, weights, 'cells', len(cells),
              'T_lower_bound', record['lower_bound'], flush=True)
    data = {'claim': 'T(p)=-p(1-p)H_second(p)>0 for 0<=p<=1/2',
            'arithmetic': 'Exact fractions and rigorously enclosed logarithms',
            'templates': records, 'total_cells': sum(len(r['cells']) for r in records)}
    if args.output:
        args.output.write_text(json.dumps(data, indent=2)+'\n')
    print('ALL 23 TEMPLATES VERIFIED; total cells', data['total_cells'])


if __name__ == '__main__':
    main()
