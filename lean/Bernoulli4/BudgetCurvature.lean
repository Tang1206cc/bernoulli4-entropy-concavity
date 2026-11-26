module

public import Bernoulli4.LossDecomposition
public import Bernoulli4.MixedLossBounds

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

/-! Assemble the curvature estimate for a single checked budget. -/

namespace Bernoulli4

open Polynomial Set Filter
open scoped Topology

noncomputable def binarySlope (p : ℝ) : ℝ := Real.log (1-p) - Real.log p

private theorem hasDerivAt_binaryEntropy {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt binaryEntropy (binarySlope p) p := by
  have hq : 1-p ≠ 0 := (sub_pos.mpr hp.2).ne'
  have h₀ : HasDerivAt (fun t : ℝ => 1-t) (-1) p := by
    simpa using (hasDerivAt_id p).const_sub 1
  have h₁ := Real.hasDerivAt_negMulLog hp.1.ne'
  have h₂ := (Real.hasDerivAt_negMulLog hq).comp p h₀
  convert h₁.fun_add h₂ using 1
  · rfl
  · unfold binarySlope
    ring

private theorem hasDerivAt_binarySlope {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt binarySlope (-1/(p*(1-p))) p := by
  have hq : 1-p ≠ 0 := (sub_pos.mpr hp.2).ne'
  have h₀ : HasDerivAt (fun t : ℝ => 1-t) (-1) p := by
    simpa using (hasDerivAt_id p).const_sub 1
  convert (h₀.log hq).fun_sub (Real.hasDerivAt_log hp.1.ne') using 1
  · rfl
  · field_simp [hp.1.ne', hq]
    ring

noncomputable def rLossA : Polynomial ℝ := bernR * (1-C 2*bernR)
noncomputable def rLossB : Polynomial ℝ := bernR^2

private theorem lossA_eval (p : ℝ) :
    rLossA.eval p = (p*(1-p))*(1-2*(p*(1-p))) := by simp [rLossA, bernR]

private theorem lossB_eval (p : ℝ) :
    rLossB.eval p = (p*(1-p))^2 := by simp [rLossB, bernR]

private theorem lossA_second_eval (p : ℝ) :
    rLossA.derivative.derivative.eval p = -6*(1-4*(p*(1-p))) := by
  simp [rLossA, bernR, derivative_mul]
  ring

private theorem lossB_second_eval (p : ℝ) :
    rLossB.derivative.derivative.eval p = 2-12*(p*(1-p)) := by
  simp [rLossB, bernR, derivative_mul, derivative_pow]
  ring

noncomputable def budgetSlope (b : Budget) (p : ℝ) : ℝ :=
  4 * binarySlope p - b.A * rLossA.derivative.eval p -
    b.B * rLossB.derivative.eval p -
    b.f₁₁ * mixedLossJet 1 1 1 p - b.f₁₂ * mixedLossJet 1 2 1 p -
    b.f₂₁ * mixedLossJet 2 1 1 p - b.f₁₃ * mixedLossJet 1 3 1 p -
    b.t * diagonalSlope p

noncomputable def budgetCurvature (b : Budget) (p : ℝ) : ℝ :=
  -4 / (p*(1-p)) + 6 * b.A * (1-4*(p*(1-p))) -
    b.B * (2-12*(p*(1-p))) -
    b.f₁₁ * deriv (deriv (mixedLoss 1 1)) p -
    b.f₁₂ * deriv (deriv (mixedLoss 1 2)) p -
    b.f₂₁ * deriv (deriv (mixedLoss 2 1)) p -
    b.f₁₃ * deriv (deriv (mixedLoss 1 3)) p -
    b.t * deriv (deriv diagonalLoss) p

private theorem hasDerivAt_budgetEntropy (b : Budget) {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) : HasDerivAt (budgetEntropy b) (budgetSlope b p) p := by
  have h0 := (hasDerivAt_binaryEntropy hp).const_mul 4
  have hA := (rLossA.hasDerivAt p).const_mul b.A
  have hB := (rLossB.hasDerivAt p).const_mul b.B
  have h11 := (hasDerivAt_mixedLossJet (a:=1) (b:=1) (by norm_num) (by norm_num) 0 hp).const_mul
    (b.f₁₁ : ℝ)
  have h12 := (hasDerivAt_mixedLossJet (a:=1) (b:=2) (by norm_num) (by norm_num) 0 hp).const_mul
    (b.f₁₂ : ℝ)
  have h21 := (hasDerivAt_mixedLossJet (a:=2) (b:=1) (by norm_num) (by norm_num) 0 hp).const_mul
    (b.f₂₁ : ℝ)
  have h13 := (hasDerivAt_mixedLossJet (a:=1) (b:=3) (by norm_num) (by norm_num) 0 hp).const_mul
    (b.f₁₃ : ℝ)
  have hT := (hasDerivAt_diagonalLoss hp).const_mul (b.t : ℝ)
  have H := ((((((h0.fun_sub hA).fun_sub hB).fun_sub h11).fun_sub h12).fun_sub h21).fun_sub h13).fun_sub hT
  convert H using 1
  · funext x
    simp only [budgetEntropy, lossA_eval, lossB_eval, mixedLoss]
    ring
  · simp only [budgetSlope, Nat.zero_add]

private theorem hasDerivAt_budgetSlope (b : Budget) {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) : HasDerivAt (budgetSlope b) (budgetCurvature b p) p := by
  have h0 := (hasDerivAt_binarySlope hp).const_mul 4
  have hA := (rLossA.derivative.hasDerivAt p).const_mul b.A
  have hB := (rLossB.derivative.hasDerivAt p).const_mul b.B
  have h11 := (hasDerivAt_mixedLossJet (a:=1) (b:=1) (by norm_num) (by norm_num) 1 hp).const_mul
    (b.f₁₁ : ℝ)
  have h12 := (hasDerivAt_mixedLossJet (a:=1) (b:=2) (by norm_num) (by norm_num) 1 hp).const_mul
    (b.f₁₂ : ℝ)
  have h21 := (hasDerivAt_mixedLossJet (a:=2) (b:=1) (by norm_num) (by norm_num) 1 hp).const_mul
    (b.f₂₁ : ℝ)
  have h13 := (hasDerivAt_mixedLossJet (a:=1) (b:=3) (by norm_num) (by norm_num) 1 hp).const_mul
    (b.f₁₃ : ℝ)
  have hT := (hasDerivAt_diagonalSlope hp).const_mul (b.t : ℝ)
  have H := ((((((h0.fun_sub hA).fun_sub hB).fun_sub h11).fun_sub h12).fun_sub h21).fun_sub h13).fun_sub hT
  convert H using 1
  · rfl
  · unfold budgetCurvature
    simp only [deriv2_mixedLoss (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1) hp,
      deriv2_mixedLoss (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 2) hp,
      deriv2_mixedLoss (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 1) hp,
      deriv2_mixedLoss (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 3) hp,
      deriv2_diagonalLoss hp, lossA_second_eval, lossB_second_eval]
    ring

theorem deriv2_budgetEntropy (b : Budget) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    deriv (deriv (budgetEntropy b)) p = budgetCurvature b p := by
  have hloc : deriv (budgetEntropy b) =ᶠ[𝓝 p] budgetSlope b :=
    Filter.Eventually.mono
      (show ∀ᶠ x in 𝓝 p, x ∈ Ioo (0 : ℝ) 1 from Ioo_mem_nhds hp.1 hp.2)
      fun _ hx => (hasDerivAt_budgetEntropy b hx).deriv
  exact ((hasDerivAt_budgetSlope b hp).congr_of_eventuallyEq hloc).deriv

theorem budgetCurvature_midpoint (b : Budget) : budgetCurvature b (1/2 : ℝ) = -16 + b.K := by
  unfold budgetCurvature Budget.K
  rw [f11_curvature_midpoint, f12_curvature_midpoint, f21_curvature_midpoint,
    f13_curvature_midpoint, diagonalCurvature_midpoint]
  norm_num
  ring

theorem budgetCurvature_control (b : Budget) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    budgetCurvature b p - budgetCurvature b (1/2 : ℝ) ≤
      (1-4*(p*(1-p))) * (b.D-4/(p*(1-p))) := by
  let r := p*(1-p)
  have hr : 0 < r := mul_pos hp.1 (sub_pos.mpr hp.2)
  have hdiff : (2*p-1)^2 = 1 - 4*r := by dsimp [r]; ring
  have hbase : (-4 : ℝ)/r + 16 = (1-4*r)*(-4/r) := by field_simp [hr.ne']; ring
  rw [budgetCurvature_midpoint]
  unfold budgetCurvature Budget.K Budget.D
  change -4/r + 6*b.A*(1-4*r) - b.B*(2-12*r) - _ - _ - _ - _ - _ - _ ≤
    (1-4*r)*(6*b.A-3*b.B-b.f₁₃*(45/8+24*Real.log 2)-4/r)
  have h11 := mul_le_mul_of_nonneg_left (f11_curvature_bound hp) (Nat.cast_nonneg b.f₁₁)
  have h12 := mul_le_mul_of_nonneg_left (f12_curvature_bound hp) (Nat.cast_nonneg b.f₁₂)
  have h21 := mul_le_mul_of_nonneg_left (f21_curvature_bound hp) (Nat.cast_nonneg b.f₂₁)
  have h13 := mul_le_mul_of_nonneg_left (f13_curvature_bound hp) (Nat.cast_nonneg b.f₁₃)
  have hT := mul_le_mul_of_nonneg_left (diagonalCurvature_ge hp) (Nat.cast_nonneg b.t)
  rw [hdiff] at h13
  linear_combination h11 + h12 + h21 + h13 + hT + hbase

theorem budgetCurvature_lt_midpoint (i : Fin 23) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hne : p ≠ 1 / 2) : budgetCurvature (budget i) p < budgetCurvature (budget i) (1/2) := by
  have hr : 0 < p*(1-p) := mul_pos hp.1 (sub_pos.mpr hp.2)
  have hsq : 0 < (2*p-1)^2 := sq_pos_of_ne_zero (fun h => hne (by linarith))
  have hu : 0 < 1-4*(p*(1-p)) := by nlinarith only [hsq]
  have hr' : (16 : ℝ) ≤ 4/(p*(1-p)) := (le_div_iff₀ hr).mpr (by nlinarith only [hsq])
  have hE : (budget i).D - 4/(p*(1-p)) < 0 := sub_neg.mpr ((budget_D_lt i).trans_le hr')
  have H := (budgetCurvature_control (budget i) hp).trans_lt (mul_neg_of_pos_of_neg hu hE)
  exact sub_neg.mp H

end Bernoulli4
