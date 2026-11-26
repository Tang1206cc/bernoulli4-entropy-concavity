#!/usr/bin/env python3
"""Reconstruct the exact entropy-loss decomposition of all 23 templates.

This uses only integer arithmetic and fractions.Fraction.  It does not prove
that the 23 templates exhaust real positive weights; that independent finite
classification is the responsibility of the classification certificate.

The analytic inequalities used here are proved in notes/analytic_notes.txt.
"""
from collections import Counter, defaultdict
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json

LOG_2_BOUNDS = (Q(2, 3), Q(7, 10))
LOG_3_BOUNDS = (Q(1), Q(11, 10))

WEIGHTS = [
    (1,1,1,1), (1,1,1,2), (1,1,1,3), (1,1,1,4),
    (1,1,2,2), (1,1,2,3), (1,1,2,4), (1,1,2,5),
    (1,1,3,3), (1,1,3,4), (1,1,3,5), (1,1,3,6),
    (1,2,2,3), (1,2,3,3), (1,2,3,4), (1,2,3,5),
    (1,2,3,6), (1,2,3,7), (1,2,4,5), (1,2,4,7),
    (1,2,4,8), (1,3,3,5), (1,3,5,7),
]


def factor_log_coefficient(n):
    """Return (L2,L3) for n*log(n) = L2*log(2)+L3*log(3)."""
    value = n
    a = b = 0
    while value % 2 == 0:
        a += 1
        value //= 2
    while value % 3 == 0:
        b += 1
        value //= 3
    assert value == 1
    return n*a, n*b


def reconstruct(w):
    counts = defaultdict(lambda: [0]*5)
    for bits in product((0,1), repeat=4):
        counts[sum(x*y for x,y in zip(w,bits))][sum(bits)] += 1
    classes = Counter(tuple(row) for row in counts.values())
    for row, number in classes.items():
        assert classes[row[::-1]] == number
    assert sum(sum(row)*n for row,n in classes.items()) == 16
    assert sum(row[0]*n for row,n in classes.items()) == 1
    assert sum(row[1]*n for row,n in classes.items()) == 4
    assert sum(row[2]*n for row,n in classes.items()) == 6
    assert sum(row[3]*n for row,n in classes.items()) == 4
    assert sum(row[4]*n for row,n in classes.items()) == 1

    A = [0,0]
    B = [0,0]
    F = {(1,1):0, (1,2):0, (2,1):0, (1,3):0}
    T = 0
    for row, number in classes.items():
        if sum(row) == 1:
            continue  # An unmerged atom has zero entropy loss.
        assert row[0] == row[4] == 0
        a,b,c = row[1:4]
        if a and not b and not c:
            add = factor_log_coefficient(a)
            A = [x+number*y for x,y in zip(A,add)]
        elif c and not a and not b:
            continue  # Already included with its singleton complement.
        elif b and not a and not c:
            add = factor_log_coefficient(b)
            B = [x+number*y for x,y in zip(B,add)]
        elif a and b and not c:
            assert (a,b) in F
            F[a,b] += number
        elif c and b and not a:
            assert (c,b) in F
            continue  # Complement already included by F_(c,b).
        else:
            assert (a,b,c) == (1,0,1)
            T += number

    f11,f12,f21,f13 = (F[x] for x in [(1,1),(1,2),(2,1),(1,3)])
    # C=B + f11*(1+2log2) + f12*(4/3+4log3)
    #     + f21*(4/3+2log3) + f13*(3/2+12log2) + 2T.
    C0 = Q(f11) + Q(4,3)*(f12+f21) + Q(3,2)*f13 + 2*T
    C2 = B[0] + 2*f11 + 12*f13
    C3 = B[1] + 4*f12 + 2*f21
    upperC = C0 + LOG_2_BOUNDS[1]*C2 + LOG_3_BOUNDS[1]*C3

    return {
        "weights": list(w),
        "probabilities_in_Bernstein_monomials": [
            {"sum":s, "N_s_k":row} for s,row in sorted(counts.items())
        ],
        "A_log2_log3": A,
        "B_log2_log3": B,
        "F11_F12_F21_F13_multiplicities": [f11,f12,f21,f13],
        "T_multiplicity": T,
        "C_constant_log2_log3": [str(C0),C2,C3],
        "C_rational_upper_bound": str(upperC),
    }


def check_log_bounds():
    # Positive Taylor partial sums certify exp(7/10)>2 and exp(11/10)>3.
    for target, (lower, upper) in [(2, LOG_2_BOUNDS), (3, LOG_3_BOUNDS)]:
        # The remaining terms of the atanh series are strictly positive.
        assert lower == 2*Q(target-1, target+1)
        x, degree = upper, 5
        term = Q(1)
        total = term
        for k in range(1,degree+1):
            term *= x / k
            total += term
        assert total > target


def check_coefficient_formulas():
    """Exact spot-checks of the general symbolic coefficient identities.

    Positivity for every n>=3 is established analytically in the notes.
    These finite checks detect transcription mistakes in the closed forms.
    """
    for a,b in [(1,2),(2,1),(1,3)]:
        c,alpha = Q(a+b,2), Q(b-a,a+b)
        def g(n):
            return c*(alpha**(2*n-1)*(n+(n-1)*alpha)
                      -((n-1)+n*alpha)) / (2*n*(n-1)*(2*n-1))
        if (a,b) == (1,3):
            # c_2=(g_2-g_1)/4, and log(a+b)=2 log(2).
            assert (g(2)+Q(a*b,a+b))/4 == Q(15,128)
            assert c*alpha/2 == Q(1,2)
        for n in range(3,31):
            D = n*(n-1)*(n-2)*(2*n-1)*(2*n-3)
            if (a,b) == (1,2):
                expected = Q(9**n*(8*n*n-19*n+9)
                             -(96*n**3-144*n*n+21*n+9), 8*9**n*D)
            elif (a,b) == (2,1):
                expected = Q(9**n*(4*n*n-14*n+9)
                             +(48*n**3-36*n*n+6*n-9), 8*9**n*D)
            else:
                expected = Q(3*(4**n*(4*n*n-9*n+4)
                                -(12*n**3-14*n*n-6*n+4)), 8*4**n*D)
            assert expected == (g(n)-g(n-1))/4
            assert expected > 0


def check_sharp_bound(records):
    """Check the finite comparisons used in the sharp curvature proof."""
    assert sum(len(set(record['weights'])) == 1 for record in records) == 1
    sharp_midpoint_lower = 6*(LOG_2_BOUNDS[0]+LOG_3_BOUNDS[0])
    assert Q(99, 10) < sharp_midpoint_lower
    assert 6*(LOG_2_BOUNDS[1]+LOG_3_BOUNDS[1]) < 16
    for record in records:
        a2, a3 = record['A_log2_log3']
        b2, b3 = record['B_log2_log3']
        _, _, _, f13 = record['F11_F12_F21_F13_multiplicities']
        # D = 6A - 3B - f13*(45/8 + 24 log 2).
        d2 = 6*a2-3*b2-24*f13
        d3 = 6*a3-3*b3
        d_upper = -Q(45,8)*f13
        for coefficient, (lower, upper) in [(d2, LOG_2_BOUNDS), (d3, LOG_3_BOUNDS)]:
            d_upper += max(coefficient*lower, coefficient*upper)
        assert d_upper <= Q(42,5) < 16

        k0, k2, k3 = record['C_constant_log2_log3']
        if len(set(record['weights'])) == 1:
            assert (Q(k0), k2, k3) == (0, 6, 6)
        else:
            assert Q(record['C_rational_upper_bound']) <= Q(99,10)

        # Also differentiate the probability polynomials directly. With
        # s=2k-4, each size-k atom supplies P=1/16, P'=s/8,
        # and P''=(s*s-4)/4 at the midpoint. Sum P''=0, so the common
        # log(16) term cancels from -sum(P'' log P + (P')**2/P).
        midpoint = Q(0)
        midpoint_l2 = Q(0)
        midpoint_l3 = Q(0)
        second_total = Q(0)
        for fiber in record['probabilities_in_Bernstein_monomials']:
            counts = fiber['N_s_k']
            size = sum(counts)
            score = sum((2*k-4)*n for k,n in enumerate(counts))
            second = Q(sum(((2*k-4)**2-4)*n for k,n in enumerate(counts)),4)
            second_total += second
            nlog2, nlog3 = factor_log_coefficient(size)
            midpoint -= Q(score**2,4*size)
            midpoint_l2 -= second*Q(nlog2,size)
            midpoint_l3 -= second*Q(nlog3,size)
        assert second_total == 0
        assert (midpoint, midpoint_l2, midpoint_l3) == (Q(k0)-16, k2, k3)


def main():
    if not __debug__:
        raise SystemExit('Run without -O: assertions are part of the verifier.')
    check_log_bounds()
    check_coefficient_formulas()
    result = [reconstruct(w) for w in WEIGHTS]
    check_sharp_bound(result)
    dest = Path(__file__).with_name("analytic_templates.json")
    dest.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print("All 23 exact entropy-loss decompositions reconstructed.")
    print("Sharp curvature comparisons and all exact midpoint derivatives passed.")
    print("Sharp upper bound: -16 + 6 log(6); equality exactly at equal weights and p=1/2.")
    for row in result:
        print(tuple(row["weights"]),
              "A=",row["A_log2_log3"],
              "B=",row["B_log2_log3"],
              "F=",row["F11_F12_F21_F13_multiplicities"],
              "T=",row["T_multiplicity"],
              "C<=",row["C_rational_upper_bound"])


if __name__ == "__main__":
    main()
