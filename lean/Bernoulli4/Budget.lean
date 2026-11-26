module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.Fin.VecNotation

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! The strict inequalities used to compare all finite entropy templates. -/

namespace Bernoulli4

open Real

structure Budget where
  A₂ : ℕ
  A₃ : ℕ
  B₂ : ℕ
  B₃ : ℕ
  f₁₁ : ℕ
  f₁₂ : ℕ
  f₂₁ : ℕ
  f₁₃ : ℕ
  t : ℕ

noncomputable def Budget.A (c : Budget) : ℝ := c.A₂ * log 2 + c.A₃ * log 3
noncomputable def Budget.B (c : Budget) : ℝ := c.B₂ * log 2 + c.B₃ * log 3

noncomputable def Budget.K (c : Budget) : ℝ :=
  c.B + c.f₁₁ * (1 + 2 * log 2) + c.f₁₂ * (4/3 + 4 * log 3) +
    c.f₂₁ * (4/3 + 2 * log 3) + c.f₁₃ * (3/2 + 12 * log 2) + 2 * c.t

noncomputable def Budget.D (c : Budget) : ℝ :=
  6 * c.A - 3 * c.B - c.f₁₃ * (45/8 + 24 * log 2)

/-- The rows of the paper's budget table in the collision catalogue order. -/
def budget : Fin 23 → Budget := ![
  ⟨8, 0, 6, 6, 0, 0, 0, 0, 0⟩,
  ⟨0, 3, 0, 0, 0, 0, 0, 1, 0⟩,
  ⟨2, 0, 8, 0, 0, 0, 1, 0, 0⟩,
  ⟨0, 3, 0, 6, 0, 0, 0, 0, 1⟩,
  ⟨0, 3, 0, 6, 0, 0, 0, 0, 0⟩,
  ⟨2, 0, 0, 0, 1, 1, 0, 0, 0⟩,
  ⟨2, 0, 2, 0, 0, 1, 0, 0, 0⟩,
  ⟨4, 0, 8, 0, 0, 0, 0, 0, 0⟩,
  ⟨2, 0, 4, 0, 1, 0, 0, 0, 1⟩,
  ⟨0, 0, 4, 0, 0, 0, 1, 0, 0⟩,
  ⟨2, 0, 0, 0, 0, 1, 0, 0, 0⟩,
  ⟨2, 0, 4, 0, 1, 0, 0, 0, 0⟩,
  ⟨2, 0, 6, 0, 0, 0, 0, 0, 0⟩,
  ⟨0, 0, 2, 0, 2, 0, 0, 0, 0⟩,
  ⟨2, 0, 4, 0, 0, 0, 0, 0, 1⟩,
  ⟨2, 0, 4, 0, 0, 0, 0, 0, 0⟩,
  ⟨0, 0, 0, 0, 2, 0, 0, 0, 0⟩,
  ⟨0, 0, 2, 0, 1, 0, 0, 0, 0⟩,
  ⟨0, 0, 0, 0, 1, 0, 0, 0, 1⟩,
  ⟨0, 0, 0, 0, 1, 0, 0, 0, 0⟩,
  ⟨0, 0, 2, 0, 0, 0, 0, 0, 0⟩,
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 1⟩,
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩
]

theorem log_two_bounds : (2/3 : ℝ) < log 2 ∧ log 2 < (7/10 : ℝ) := by
  constructor
  · linarith [log_two_gt_d9]
  · linarith [log_two_lt_d9]

theorem log_three_bounds : (1 : ℝ) < log 3 ∧ log 3 < (11/10 : ℝ) := by
  constructor
  · linarith [log_three_gt_d9]
  · linarith [log_three_lt_d9]

theorem budget_D_lt (i : Fin 23) : (budget i).D < 16 := by
  obtain ⟨h₂l, h₂u⟩ := log_two_bounds
  obtain ⟨h₃l, h₃u⟩ := log_three_bounds
  fin_cases i <;> norm_num [budget, Budget.D, Budget.A, Budget.B] <;> linarith

theorem log_six_eq : log 6 = log 2 + log 3 := by
  rw [show (6 : ℝ) = 2 * 3 by norm_num, log_mul (by norm_num) (by norm_num)]

theorem budget_K_equal : (budget 0).K = 6 * log 6 := by
  norm_num [budget, Budget.K, Budget.B, log_six_eq]
  ring

theorem budget_K_lt (i : Fin 23) (hi : i ≠ 0) : (budget i).K < 6 * log 6 := by
  obtain ⟨h₂l, h₂u⟩ := log_two_bounds
  obtain ⟨h₃l, h₃u⟩ := log_three_bounds
  rw [log_six_eq]
  fin_cases i <;> first | exact (hi rfl).elim | (norm_num [budget, Budget.K, Budget.B]; linarith)

theorem sharp_curvature_negative : -16 + 6 * log 6 < 0 := by
  rw [log_six_eq]
  linarith [log_two_bounds.2, log_three_bounds.2]

end Bernoulli4
