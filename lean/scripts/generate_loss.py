"""Render the polynomial and logarithmic identity proofs for the 23 templates."""

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "lean" / "Bernoulli4" / "LossDecomposition.lean"


def vector(values):
    return "![" + ", ".join(map(str, values)) + "]"


def kernel_proof(shapes):
    q = "(1-p)"
    for index, shape in enumerate(shapes):
        active = tuple(i for i, count in enumerate(shape) if count)
        a = min(active)
        b = 4 - max(active)
        if len(active) == 1:
            z = str(shape[a])
        elif active == (1, 2):
            z = f"({shape[1]}*{q}+{shape[2]}*p)"
        elif active == (2, 3):
            z = f"({shape[3]}*p+{shape[2]}*{q})"
        elif active == (1, 3) and shape[1] == shape[3] == 1:
            z = f"(p^2+{q}^2)"
        else:
            raise ValueError(f"Unexpected profile: {shape}")
        factor = f"p^{a}*{q}^{b}*{z}"
        normalize = "\n    ring" if sum(shape) != 1 else ""
        yield f"""private theorem profile_term_{index} (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    Real.negMulLog ((profilePoly {vector(shape)}).eval p) =
      -({factor}) * ({a}*Real.log p+{b}*Real.log {q}+Real.log {z}) := by
  have h : (profilePoly {vector(shape)}).eval p = {factor} := by
    simp [profilePoly, atomPoly_eval, Fin.sum_univ_succ]{normalize}
  rw [h]
  have hp₀ : 0 < p := hp.1
  have hq₀ : 0 < 1 - p := sub_pos.mpr hp.2
  simpa using negMulLog_factor hp {a} {b} {z} (by positivity)
"""


def main():
    doc = json.loads((ROOT / "proof" / "classification.json").read_text())
    templates = [list(map(tuple, t["count_vectors"])) for t in doc["templates"]]
    shapes = sorted(set(shape for template in templates for shape in template))
    output = ["""module

public import Bernoulli4.ProfileData
public import Bernoulli4.Budget
public import Bernoulli4.MixedLoss
public import Bernoulli4.DiagonalLoss

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

/-! The 23 loss identities. Rebuild with scripts/generate_loss.py. -/

namespace Bernoulli4

open Set

noncomputable def binaryEntropy (p : ℝ) : ℝ :=
  Real.negMulLog p + Real.negMulLog (1-p)

noncomputable def budgetEntropy (b : Budget) (p : ℝ) : ℝ :=
  4 * binaryEntropy p - b.A * (p*(1-p))*(1-2*(p*(1-p))) -
    b.B * (p*(1-p))^2 -
    b.f₁₁ * mixedLoss 1 1 p - b.f₁₂ * mixedLoss 1 2 p -
    b.f₂₁ * mixedLoss 2 1 p - b.f₁₃ * mixedLoss 1 3 p -
    b.t * diagonalLoss p

private theorem negMulLog_factor {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (a b : ℕ)
    (z : ℝ) (hz : 0 < z) :
    Real.negMulLog (p^a*(1-p)^b*z) =
      -(p^a*(1-p)^b*z)*((a : ℝ)*Real.log p+(b : ℝ)*Real.log (1-p)+Real.log z) := by
  have hp₀ : p ≠ 0 := hp.1.ne'
  have hq₀ : 1-p ≠ 0 := (sub_pos.mpr hp.2).ne'
  simp only [Real.negMulLog_def]
  rw [Real.log_mul (mul_ne_zero (pow_ne_zero _ hp₀) (pow_ne_zero _ hq₀)) hz.ne',
    Real.log_mul (pow_ne_zero _ hp₀) (pow_ne_zero _ hq₀),
    Real.log_pow, Real.log_pow]

private theorem profileEntropy_list (l : List Profile) (p : ℝ) :
    profileEntropy (↑l) p =
      (l.map (fun v => Real.negMulLog ((profilePoly v).eval p))).sum := by
  simp [profileEntropy]

private theorem log_four : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
  norm_num
"""]
    output.extend(kernel_proof(shapes))
    for index, template in enumerate(templates):
        terms = ",\n      ".join(map(vector, template))
        laws = ", ".join(f"profile_term_{shapes.index(v)} p hp" for v in sorted(set(template)))
        output.append(f"""set_option maxHeartbeats 1000000 in
private theorem budget_identity_{index} (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    profileEntropy (template {index}) p = budgetEntropy (budget {index}) p := by
  change profileEntropy (↑([
      {terms}] : List Profile)) p = _
  rw [profileEntropy_list]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, {laws}]
  norm_num [budgetEntropy, budget, Budget.A, Budget.B, binaryEntropy, Real.negMulLog,
    mixedLoss_formula, diagonalLoss_formula, log_four, log_six_eq]; ring
""")
    cases = "\n".join(f"  · exact budget_identity_{i} p hp" for i in range(len(templates)))
    output.append(f"""theorem budget_identity (i : Fin 23) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    profileEntropy (template i) p = budgetEntropy (budget i) p := by
  fin_cases i
{cases}

end Bernoulli4
""")
    OUT.write_text("\n".join(output))


if __name__ == "__main__":
    main()
