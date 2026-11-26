"""Export the paper's exact collision witnesses and a complete Lean case tree.

Lean checks every leaf and implication in the generated tree. Generation
reuses the two release verifiers for exact rational linear algebra.
"""

from fractions import Fraction
from functools import lru_cache
import json
from math import lcm
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "proof"))
from classification import dot, hyperplanes, in_span, rref
from independent_classification_check import exact_solve, pivot_columns, positive_dual_witness


def combination(rows, target):
    """Return an integer multiple of target expressed in the given basis."""
    cols = pivot_columns(rows)
    matrix = [[row[j] for row in rows] for j in cols]
    weights = exact_solve(matrix, [target[j] for j in cols])
    assert weights is not None
    assert all(sum(c * row[j] for c, row in zip(weights, rows)) == target[j]
               for j in range(4))
    scale = lcm(*(Fraction(c).denominator for c in weights))
    return scale, tuple(int(scale * c) for c in weights)


def coefficients(indices, rows, target):
    scale, weights = combination(rows, target)
    return scale, "[" + ", ".join(
        f"({weight}, {index})" for weight, index in zip(weights, indices) if weight
    ) + "]"


def vector(values):
    return "![" + ", ".join(map(str, values)) + "]"


def main():
    data = json.loads((ROOT / "proof" / "classification.json").read_text())
    normals = hyperplanes()
    assert normals == tuple(map(tuple, data["hyperplane_normals"]))
    flat_witnesses = [tuple(flat["witness"]) for flat in data["positive_flats"]]
    closure_ids = {tuple(flat["hyperplane_indices"]): i
                   for i, flat in enumerate(data["positive_flats"])}
    terminal_ids = set()

    @lru_cache(maxsize=None)
    def dual(basis):
        if not basis:
            return None
        if len(basis) == 4:
            return (1, 0, 0, 0)
        return positive_dual_witness(basis)

    def subtree(step, basis, negatives):
        rows = [normals[i] for i in basis]
        space = rref(rows)
        impossible = dual(space)
        if impossible is not None:
            _, terms = coefficients(basis, rows, impossible)
            return "exclude", (terms,), ()
        for i in negatives:
            if in_span(normals[i], space):
                scale, terms = coefficients(basis, rows, normals[i])
                return "conflict", (i, scale, terms), ()
        if step == len(normals):
            closure = tuple(i for i, h in enumerate(normals) if in_span(h, space))
            representative = closure_ids[closure]
            assert all((dot(h, flat_witnesses[representative]) == 0) == (i in closure)
                       for i, h in enumerate(normals))
            terminal_ids.add(representative)
            return "accept", (representative,), ()
        if in_span(normals[step], space):
            scale, terms = coefficients(basis, rows, normals[step])
            return "imply", (step, scale, terms), (subtree(step + 1, basis, negatives),)
        yes = subtree(step + 1, (*basis, step), negatives)
        no = subtree(step + 1, basis, (*negatives, step))
        return "split", (step,), (yes, no)

    def render(tree, depth):
        tag, args, children = tree
        subtrees = "".join("\n" + render(child, depth + 2) for child in children)
        return " " * depth + f"(.{tag} " + " ".join(map(str, args)) + subtrees + ")"

    def count_nodes(tree):
        return 1 + sum(count_nodes(child) for child in tree[2])

    definitions = []
    def verified_chunks(tree, zeros=(), nonzeros=()):
        tag, args, children = tree
        if count_nodes(tree) <= 120:
            suffix = len(definitions)
            chunk = f"caseChunk{suffix}"
            checked = f"caseChunk{suffix}_checked"
            z, nz = list(zeros), list(nonzeros)
            definitions.append(
                f"def {chunk} : CaseTree :=\n{render(tree, 2)}\n\n"
                "set_option maxRecDepth 8192 in\n"
                "set_option maxHeartbeats 1500000 in\n"
                f"theorem {checked} : {chunk}.check {z} {nz} = true := by\n"
                "  decide +kernel"
            )
            return chunk, checked
        i = args[0]
        yes, hy = verified_chunks(children[0], (i, *zeros), nonzeros)
        if tag == "split":
            no, hn = verified_chunks(children[1], zeros, (i, *nonzeros))
            return f"(.split {i} {yes} {no})", f"(CaseTree.checked_split {hy} {hn})"
        assert tag == "imply"
        scale, terms = args[1:]
        expression = f"(.imply {i} {scale} {terms} {yes})"
        proof = (f"(CaseTree.checked_imply (i := {i}) (scale := {scale}) (terms := {terms}) "
                 f"(zeros := {list(zeros)}) (nonzeros := {list(nonzeros)}) "
                 f"(by decide +kernel) (by decide +kernel) {hy})")
        return expression, proof

    tree = subtree(0, (), ())
    expression, proof = verified_chunks(tree)
    assert terminal_ids == set(range(len(flat_witnesses)))
    out = ROOT / "lean" / "Bernoulli4"
    def lean_data(name, import_, body):
        (out / f"{name}.lean").write_text(
            f"module\n\npublic import {import_}\n\n@[expose] public section\n\n"
            "/-! Generated by scripts/generate_classification.py. -/\n\n"
            f"namespace Bernoulli4\n\n{body}\n\nend Bernoulli4\n")

    lean_data("Rows", "Mathlib.Data.Fin.VecNotation",
              "def normals : Array (Fin 4 → ℤ) := #[\n  "
              + ",\n  ".join(map(vector, normals)) + "]"
              + "\n\ndef normal (i : Fin 25) : Fin 4 → ℤ := normals[i.val]!"
              + "\n\ndef witnesses : Array (Fin 4 → ℤ) := #[\n  "
              + ",\n  ".join(map(vector, flat_witnesses)) + "]"
              + "\n\ndef witness (i : Fin 216) : Fin 4 → ℤ := witnesses[i.val]!")
    lean_data("CaseData", "Bernoulli4.CaseTree", "\n\n".join(definitions) +
              f"\n\ndef caseData : CaseTree :=\n  {expression}\n\n"
              "set_option maxRecDepth 8192 in\n"
              "theorem caseData_checked : caseData.check [] [] = true :=\n"
              f"  {proof}")
    template_count = len(data["templates"])
    profiles = [
        "[" + ", ".join(map(vector, record["count_vectors"])) + "]"
        for record in data["templates"]
    ]
    index = [int(flat["template_id"][1:]) - 1 for flat in data["positive_flats"]]
    lean_data("ProfileData", "Bernoulli4.Profiles",
              "def templateProfiles : Array (List Profile) := #[\n  "
              + ",\n  ".join(profiles) + "]"
              + f"\n\ndef template (i : Fin {template_count}) : Multiset Profile := "
              + "↑(templateProfiles[i.val]!)"
              + f"\n\ndef templateIndices : Array (Fin {template_count}) := #["
              + ", ".join(map(str, index)) + "]"
              + f"\n\ndef templateIndex (k : Fin {len(index)}) : Fin {template_count} := "
              + "templateIndices[k.val]!")
    print("Candidate witnesses:", len(terminal_ids))
    print("Decision tree nodes:", count_nodes(tree), "in", len(definitions), "checked chunks")


if __name__ == "__main__":
    main()
