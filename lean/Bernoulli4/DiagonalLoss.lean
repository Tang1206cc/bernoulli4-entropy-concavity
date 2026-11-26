module

public import Bernoulli4.LogPolynomial

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

/-! The loss from merging a singleton with its complementary triple. -/

namespace Bernoulli4

open Polynomial Set Filter
open scoped Topology

noncomputable def bernR : Polynomial ℝ := X * (1-X)
noncomputable def diagonalMass : Polynomial ℝ := X^2 + (1-X)^2

noncomputable def diagP : Polynomial ℝ := C 2 * X^3 * (1-X)
noncomputable def diagQ : Polynomial ℝ := C 2 * X * (1-X)^3

noncomputable def diagonalLoss (p : ℝ) : ℝ :=
  -(bernR.eval p * Real.negMulLog (diagonalMass.eval p)) -
    logPolyDeriv diagP 1 0 0 p - logPolyDeriv diagQ (-1) 1 0 p

noncomputable def diagonalSlope (p : ℝ) : ℝ :=
  -(bernR.derivative.eval p * Real.negMulLog (diagonalMass.eval p) +
    bernR.eval p * entropyTermSlope diagonalMass p) -
    logPolyDeriv diagP 1 0 1 p - logPolyDeriv diagQ (-1) 1 1 p

noncomputable def diagonalCurvature (p : ℝ) : ℝ :=
  -(bernR.derivative.derivative.eval p * Real.negMulLog (diagonalMass.eval p) +
    2 * bernR.derivative.eval p * entropyTermSlope diagonalMass p +
    bernR.eval p * entropyTermCurvature diagonalMass p) -
    logPolyDeriv diagP 1 0 2 p - logPolyDeriv diagQ (-1) 1 2 p

theorem diagonalLoss_formula (p : ℝ) :
    diagonalLoss p = p*(1-p) *
      ((p^2+(1-p)^2)*Real.log (p^2+(1-p)^2) -
        2*p^2*Real.log p - 2*(1-p)^2*Real.log (1-p)) := by
  simp [diagonalLoss, bernR, diagonalMass, diagP, diagQ, logPolyDeriv_zero, Real.negMulLog]
  rw [show -p + 1 = 1-p by ring]
  ring

private theorem diagonalMass_pos {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    0 < diagonalMass.eval p := by
  simp [diagonalMass]
  have h := hp.1
  positivity

private theorem q_ne_zero {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) : -1 * p + 1 ≠ 0 := by
  have h := hp.2
  linarith

theorem hasDerivAt_diagonalLoss {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt diagonalLoss (diagonalSlope p) p := by
  have hp' : 1 * p + 0 ≠ 0 := by simpa using hp.1.ne'
  have h := (bernR.hasDerivAt p).fun_mul (hasDerivAt_entropyTerm (diagonalMass_pos hp).ne')
  have hc := (h.neg.fun_sub (hasDerivAt_logPolyDeriv diagP 1 0 0 hp')).fun_sub
    (hasDerivAt_logPolyDeriv diagQ (-1) 1 0 (q_ne_zero hp))
  convert hc using 1
  · rfl
  · rfl

theorem hasDerivAt_diagonalSlope {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt diagonalSlope (diagonalCurvature p) p := by
  have hp' : 1 * p + 0 ≠ 0 := by simpa using hp.1.ne'
  have h₁ := (bernR.derivative.hasDerivAt p).fun_mul
    (hasDerivAt_entropyTerm (diagonalMass_pos hp).ne')
  have h₂ := (bernR.hasDerivAt p).fun_mul
    (hasDerivAt_entropyTermSlope (diagonalMass_pos hp).ne')
  have hc := ((h₁.fun_add h₂).neg.fun_sub (hasDerivAt_logPolyDeriv diagP 1 0 1 hp')).fun_sub
    (hasDerivAt_logPolyDeriv diagQ (-1) 1 1 (q_ne_zero hp))
  convert hc using 1
  · rfl
  · simp only [diagonalCurvature]
    ring

theorem deriv2_diagonalLoss {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    deriv (deriv diagonalLoss) p = diagonalCurvature p := by
  have hloc : deriv diagonalLoss =ᶠ[𝓝 p] diagonalSlope :=
    Filter.Eventually.mono
      (show ∀ᶠ x in 𝓝 p, x ∈ Ioo (0 : ℝ) 1 from Ioo_mem_nhds hp.1 hp.2)
      fun _ hx => (hasDerivAt_diagonalLoss hx).deriv
  exact ((hasDerivAt_diagonalSlope hp).congr_of_eventuallyEq hloc).deriv

noncomputable def skewLog (p : ℝ) : ℝ :=
  -2 * Real.negMulLog p + 2 * Real.negMulLog (1-p)

private theorem continuous_skewLog : Continuous skewLog := by
  unfold skewLog
  fun_prop

private noncomputable def skewSlope (p : ℝ) : ℝ := 2 * Real.log p + 2 * Real.log (1-p) + 4

private theorem hasDerivAt_skewLog {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt skewLog (skewSlope p) p := by
  have hq : 1-p ≠ 0 := (sub_pos.mpr hp.2).ne'
  have h₀ : HasDerivAt (fun t : ℝ => 1-t) (-1) p := by
    simpa using (hasDerivAt_id p).const_sub 1
  have h₁ := (Real.hasDerivAt_negMulLog hp.1.ne').const_mul (-2)
  have h₂ := ((Real.hasDerivAt_negMulLog hq).comp p h₀).const_mul 2
  convert h₁.fun_add h₂ using 1
  · rfl
  · simp only [skewSlope]
    ring

private theorem hasDerivAt_skewSlope {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt skewSlope (2/p - 2/(1-p)) p := by
  have hq : 1-p ≠ 0 := (sub_pos.mpr hp.2).ne'
  have h₀ : HasDerivAt (fun t : ℝ => 1-t) (-1) p := by
    simpa using (hasDerivAt_id p).const_sub 1
  have h₁ := (Real.hasDerivAt_log hp.1.ne').const_mul 2
  have h₂ := (h₀.log hq).const_mul 2
  convert (h₁.fun_add h₂).add_const 4 using 1
  · rfl
  · ring

private theorem deriv2_skewLog {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    deriv (deriv skewLog) p = 2/p - 2/(1-p) := by
  have hloc : deriv skewLog =ᶠ[𝓝 p] skewSlope :=
    Filter.Eventually.mono
      (show ∀ᶠ x in 𝓝 p, x ∈ Ioo (0 : ℝ) 1 from Ioo_mem_nhds hp.1 hp.2)
      fun _ hx => (hasDerivAt_skewLog hx).deriv
  exact ((hasDerivAt_skewSlope hp).congr_of_eventuallyEq hloc).deriv

private theorem skewLog_nonneg {p : ℝ} (hp : p ∈ Icc (1/2 : ℝ) 1) :
    0 ≤ skewLog p := by
  have hconc : StrictConcaveOn ℝ (Icc (1/2 : ℝ) 1) skewLog := by
    apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _) continuous_skewLog.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    change deriv (deriv skewLog) x < 0
    rw [deriv2_skewLog ⟨by linarith [hx.1], hx.2⟩]
    apply sub_neg.mpr
    exact (div_lt_div_iff₀ (by linarith [hx.1]) (sub_pos.mpr hx.2)).mpr (by linarith [hx.1])
  have hx₀ : (1/2 : ℝ) ∈ Icc (1/2 : ℝ) 1 := by norm_num
  have hx₁ : (1 : ℝ) ∈ Icc (1/2 : ℝ) 1 := by norm_num
  have ha : 0 ≤ 2 - 2*p := by linarith [hp.2]
  have hb : 0 ≤ 2*p - 1 := by linarith [hp.1]
  have hc : (2 - 2*p) + (2*p - 1) = 1 := by ring
  have h := hconc.concaveOn.2 hx₀ hx₁ ha hb hc
  have left : skewLog (1/2 : ℝ) = 0 := by
    unfold skewLog
    rw [show (1 : ℝ) - 1/2 = 1/2 by norm_num]
    ring
  have right : skewLog 1 = 0 := by simp [skewLog]
  rw [left, right] at h
  simp only [smul_eq_mul, mul_zero, zero_add] at h
  convert h using 2
  ring

private theorem skewLog_sign {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    0 ≤ (2*p-1) * skewLog p := by
  by_cases h : (1/2 : ℝ) ≤ p
  · exact mul_nonneg (by linarith) (skewLog_nonneg ⟨h, hp.2.le⟩)
  · have h' : skewLog (1-p) = -skewLog p := by
      unfold skewLog
      rw [show (1 : ℝ) - (1-p) = p by ring]
      ring
    have hh := skewLog_nonneg (p := 1-p) ⟨by linarith, by linarith [hp.1]⟩
    rw [h'] at hh
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)

private theorem diagonalCurvature_formula {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    diagonalCurvature p =
      -2 * (1 - (2*p-1)^2) / (1 + (2*p-1)^2) +
      6 * ((2*p-1)*skewLog p - (2*p-1)^2 * Real.log (p^2+(1-p)^2)) := by
  have hp₀ : p ≠ 0 := hp.1.ne'
  have hq : 1-p ≠ 0 := (sub_pos.mpr hp.2).ne'
  have hs : p^2 + (1-p)^2 ≠ 0 := by have := hp.1; positivity
  have ht : 1 + (2*p-1)^2 ≠ 0 := by positivity
  simp [diagonalCurvature, bernR, diagonalMass, diagP, diagQ, entropyTermSlope,
    entropyTermCurvature, Real.negMulLog, skewLog, logPolyDeriv, logJet, LogJet.next,
    LogJet.value, affinePoly, derivative_mul, derivative_pow]
  rw [show -p + 1 = 1-p by ring]
  field_simp [hp₀, hq, hs, ht]
  ring

theorem diagonalCurvature_ge {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    -2 ≤ deriv (deriv diagonalLoss) p := by
  rw [deriv2_diagonalLoss hp, diagonalCurvature_formula hp]
  have hS : p^2 + (1-p)^2 ≤ 1 := by
    nlinarith [mul_nonneg hp.1.le (sub_nonneg.mpr hp.2.le)]
  have hlog := Real.log_nonpos (by positivity : 0 ≤ p^2+(1-p)^2) hS
  have hA : -2 ≤ -2 * (1 - (2*p-1)^2) / (1 + (2*p-1)^2) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (2*p-1)]
  have hB := sub_nonneg.mpr ((mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (2*p-1)) hlog).trans
    (skewLog_sign hp))
  linarith

theorem diagonalCurvature_midpoint :
    deriv (deriv diagonalLoss) (1/2 : ℝ) = -2 := by
  have h : (1/2 : ℝ) ∈ Ioo 0 1 := by norm_num
  rw [deriv2_diagonalLoss h, diagonalCurvature_formula h]
  norm_num

end Bernoulli4
