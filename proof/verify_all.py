#!/usr/bin/env python3
"""Recheck the mathematical evidence accompanying the research note.

Run with Python 3.10 or later, without -O. No third-party packages required.
The analytic inequalities for all p and all series indices are proved in the
manuscript, not inferred from finitely many symbolic/numerical checks.
"""
import json
from pathlib import Path
from fractions import Fraction
import classification
import analytic_proof
import curvature_certificate
import manuscript_tables


def main():
    if not __debug__:
        raise SystemExit('Run without -O: assertions are part of the verifier.')
    root = Path(__file__).resolve().parent
    structure = json.loads((root/'classification.json').read_text())
    classification.verify(structure)
    expected = {tuple(tuple(v) for v in rec['count_vectors'])
                for rec in structure['templates']}
    assert len(expected) == 23
    print('1. Exact all-positive-real-weight classification: PASS (23 types).')

    analytic_proof.check_log_bounds()
    analytic_proof.check_coefficient_formulas()
    rebuilt = [analytic_proof.reconstruct(w) for w in analytic_proof.WEIGHTS]
    analytic_set = set()
    for record in rebuilt:
        template = tuple(sorted(tuple(v['N_s_k']) for v in
                                record['probabilities_in_Bernstein_monomials']))
        assert template not in analytic_set
        analytic_set.add(template)
    assert analytic_set == expected
    stored = json.loads((root/'analytic_templates.json').read_text())
    assert stored == rebuilt
    analytic_proof.check_sharp_bound(rebuilt)
    print('2. Exact entropy-loss identities, midpoint derivatives, and sharp comparisons: PASS.')

    interval_data = json.loads((root/'curvature_certificate.json').read_text())
    interval_set = curvature_certificate.verify_certificate(interval_data)
    assert interval_set == expected
    assert all(Fraction(r['lower_bound']) > Fraction(1,50)
               for r in interval_data['templates'])
    cell_count = sum(len(record['cells']) for record in interval_data['templates'])
    assert cell_count == interval_data['total_cells']
    print(f'3. Separate rational interval curvature check: PASS ({cell_count} cells).')
    print('4. Classification/analytic/interval template sets agree exactly: PASS.')
    manuscript_tables.verify(root.parent / 'paper', structure, rebuilt)
    print('5. Manuscript classification and budget tables match exact data: PASS.')
    print('The finite computations required by the manuscript have all passed.')
    print('Read the manuscript for the all-orders analytic lemmas and coverage proof.')


if __name__ == '__main__':
    main()
