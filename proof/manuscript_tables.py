#!/usr/bin/env python3
"""Generate and check the manuscript tables from the exact proof data.

The master verifier first validates the classification and analytic records,
then passes those same objects here. No table coefficient is entered by hand.
"""
from collections import Counter
from fractions import Fraction
from pathlib import Path
import argparse
import json

import analytic_proof


def template_key(record):
    return tuple(sorted(tuple(row['N_s_k']) for row in
                        record['probabilities_in_Bernstein_monomials']))


def fraction_tex(value):
    value = Fraction(value)
    if value.denominator == 1:
        return str(value.numerator)
    return rf'\frac{{{value.numerator}}}{{{value.denominator}}}'


def log_tex(coefficients):
    terms = []
    for coefficient, index in zip(coefficients, (2, 3)):
        assert isinstance(coefficient, int) and coefficient >= 0
        if coefficient:
            terms.append(('' if coefficient == 1 else str(coefficient))
                         + f'L_{index}')
    return '+'.join(terms) or '0'


def tuple_tex(values):
    return '(' + ','.join(map(str, values)) + ')'


def generate(structure, analytic_records):
    by_template = {template_key(record): record for record in analytic_records}
    assert len(by_template) == len(analytic_records) == 23
    budget_rows = []
    used = set()
    for entry in sorted(structure['templates'], key=lambda row: row['id']):
        key = tuple(sorted(tuple(v) for v in entry['count_vectors']))
        assert key in by_template and key not in used
        used.add(key)
        record = by_template[key]
        columns = [entry['id'], tuple_tex(record['weights']),
                   log_tex(record['A_log2_log3']),
                   log_tex(record['B_log2_log3']),
                   tuple_tex(record['F11_F12_F21_F13_multiplicities']),
                   str(record['T_multiplicity']),
                   fraction_tex(record['C_rational_upper_bound'])]
        budget_rows.append(columns[0] + ' & ' +
                           ' & '.join('$' + value + '$' for value in columns[1:])
                           + r' \\' + '\n')
    assert used == set(by_template)

    accepted = structure['positive_flats']
    rejected = structure['excluded_flats']
    row_spaces = Counter(len(entry['basis']) for entry in accepted + rejected)
    positive = Counter(len(entry['basis']) for entry in accepted)
    orbits = Counter(entry['rank'] for entry in structure['permutation_orbits'])
    classification_rows = []
    for rank in range(4):
        columns = [rank, row_spaces[rank], positive[rank], orbits[rank]]
        classification_rows.append('&'.join(map(str, columns)) + r'\\' + '\n')
    classification_rows.append('\\midrule\n')
    classification_rows.append('Total&' + '&'.join(map(str, (
        sum(row_spaces.values()), sum(positive.values()), sum(orbits.values()))))
        + r'\\' + '\n')
    return {'budget_rows.tex': ''.join(budget_rows),
            'classification_rows.tex': ''.join(classification_rows)}


def verify(paper_root, structure, analytic_records):
    if not __debug__:
        raise RuntimeError('Run without -O: assertions are part of the verifier.')
    manuscript = (paper_root / 'bernoulli4_manuscript.tex').read_text(encoding='utf-8')
    for filename, expected in generate(structure, analytic_records).items():
        assert (paper_root / filename).read_text(encoding='utf-8') == expected, filename
        assert ('\\inputtable ' + filename) in manuscript, filename


def main():
    if not __debug__:
        raise SystemExit('Run without -O: assertions are part of the verifier.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    proof_root = Path(__file__).resolve().parent
    paper_root = proof_root.parent / 'paper'
    structure = json.loads((proof_root / 'classification.json').read_text())
    records = [analytic_proof.reconstruct(w) for w in analytic_proof.WEIGHTS]
    if args.check:
        verify(paper_root, structure, records)
        print('Both manuscript tables match the exact regenerated data.')
    else:
        for filename, contents in generate(structure, records).items():
            (paper_root / filename).write_text(contents, encoding='utf-8')
            print('Generated paper/' + filename)


if __name__ == '__main__':
    main()
