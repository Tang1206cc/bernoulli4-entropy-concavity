module

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

private theorem profile_term_0 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    Real.negMulLog ((profilePoly ![0, 0, 0, 0, 1]).eval p) =
      -(p^4*(1-p)^0*1) * (4*Real.log p+0*Real.log (1-p)+Real.log 1) := by
  have h : (profilePoly ![0, 0, 0, 0, 1]).eval p = p^4*(1-p)^0*1 := by
    simp [profilePoly, atomPoly_eval, Fin.sum_univ_succ]
  rw [h]
  have hp₀ : 0 < p := hp.1
  have hq₀ : 0 < 1 - p := sub_pos.mpr hp.2
  simpa using negMulLog_factor hp 4 0 1 (by positivity)

private theorem profile_term_1 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    Real.negMulLog ((profilePoly ![0, 0, 0, 1, 0]).eval p) =
      -(p^3*(1-p)^1*1) * (3*Real.log p+1*Real.log (1-p)+Real.log 1) := by
  have h : (profilePoly ![0, 0, 0, 1, 0]).eval p = p^3*(1-p)^1*1 := by
    simp [profilePoly, atomPoly_eval, Fin.sum_univ_succ]
  rw [h]
  have hp₀ : 0 < p := hp.1
  have hq₀ : 0 < 1 - p := sub_pos.mpr hp.2
  simpa using negMulLog_factor hp 3 1 1 (by positivity)

private theorem profile_term_2 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    Real.negMulLog ((profilePoly ![0, 0, 0, 2, 0]).eval p) =
      -(p^3*(1-p)^1*2) * (3*Real.log p+1*Real.log (1-p)+Real.log 2) := by
  have h : (profilePoly ![0, 0, 0, 2, 0]).eval p = p^3*(1-p)^1*2 := by
    simp [profilePoly, atomPoly_eval, Fin.sum_univ_succ]
    ring
  rw [h]
  have hp₀ : 0 < p := hp.1
  have hq₀ : 0 < 1 - p := sub_pos.mpr hp.2
  simpa using negMulLog_factor hp 3 1 2 (by positivity)

private theorem profile_term_3 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    Real.negMulLog ((profilePoly ![0, 0, 0, 3, 0]).eval p) =
      -(p^3*(1-p)^1*3) * (3*Real.log p+1*Real.log (1-p)+Real.log 3) := by
  have h : (profilePoly ![0, 0, 0, 3, 0]).eval p = p^3*(1-p)^1*3 := by
    simp [profilePoly, atomPoly_eval, Fin.sum_univ_succ]
    ring
  rw [h]
  have hp₀ : 0 < p := hp.1
  have hq₀ : 0 < 1 - p := sub_pos.mpr hp.2
  simpa using negMulLog_factor hp 3 1 3 (by positivity)

private theorem profile_term_4 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    Real.negMulLog ((profilePoly ![0, 0, 0, 4, 0]).eval p) =
      -(p^3*(1-p)^1*4) * (3*Real.log p+1*Real.log (1-p)+Real.log 4) := by
  have h : (profilePoly ![0, 0, 0, 4, 0]).eval p = p^3*(1-p)^1*4 := by
    simp [profilePoly, atomPoly_eval, Fin.sum_univ_succ]
    ring
  rw [h]
  have hp₀ : 0 < p := hp.1
  have hq₀ : 0 < 1 - p := sub_pos.mpr hp.2
  simpa using negMulLog_factor hp 3 1 4 (by positivity)

private theorem profile_term_5 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    Real.negMulLog ((profilePoly ![0, 0, 1, 0, 0]).eval p) =
      -(p^2*(1-p)^2*1) * (2*Real.log p+2*Real.log (1-p)+Real.log 1) := by
  have h : (profilePoly ![0, 0, 1, 0, 0]).eval p = p^2*(1-p)^2*1 := by
    simp [profilePoly, atomPoly_eval, Fin.sum_univ_succ]
  rw [h]
  have hp₀ : 0 < p := hp.1
  have hq₀ : 0 < 1 - p := sub_pos.mpr hp.2
  simpa using negMulLog_factor hp 2 2 1 (by positivity)

private theorem profile_term_6 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    Real.negMulLog ((profilePoly ![0, 0, 1, 1, 0]).eval p) =
      -(p^2*(1-p)^1*(1*p+1*(1-p))) * (2*Real.log p+1*Real.log (1-p)+Real.log (1*p+1*(1-p))) := by
  have h : (profilePoly ![0, 0, 1, 1, 0]).eval p = p^2*(1-p)^1*(1*p+1*(1-p)) := by
    simp [profilePoly, atomPoly_eval, Fin.sum_univ_succ]
    ring
  rw [h]
  have hp₀ : 0 < p := hp.1
  have hq₀ : 0 < 1 - p := sub_pos.mpr hp.2
  simpa using negMulLog_factor hp 2 1 (1*p+1*(1-p)) (by positivity)

private theorem profile_term_7 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    Real.negMulLog ((profilePoly ![0, 0, 1, 2, 0]).eval p) =
      -(p^2*(1-p)^1*(2*p+1*(1-p))) * (2*Real.log p+1*Real.log (1-p)+Real.log (2*p+1*(1-p))) := by
  have h : (profilePoly ![0, 0, 1, 2, 0]).eval p = p^2*(1-p)^1*(2*p+1*(1-p)) := by
    simp [profilePoly, atomPoly_eval, Fin.sum_univ_succ]
    ring
  rw [h]
  have hp₀ : 0 < p := hp.1
  have hq₀ : 0 < 1 - p := sub_pos.mpr hp.2
  simpa using negMulLog_factor hp 2 1 (2*p+1*(1-p)) (by positivity)

private theorem profile_term_8 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    Real.negMulLog ((profilePoly ![0, 0, 2, 0, 0]).eval p) =
      -(p^2*(1-p)^2*2) * (2*Real.log p+2*Real.log (1-p)+Real.log 2) := by
  have h : (profilePoly ![0, 0, 2, 0, 0]).eval p = p^2*(1-p)^2*2 := by
    simp [profilePoly, atomPoly_eval, Fin.sum_univ_succ]
    ring
  rw [h]
  have hp₀ : 0 < p := hp.1
  have hq₀ : 0 < 1 - p := sub_pos.mpr hp.2
  simpa using negMulLog_factor hp 2 2 2 (by positivity)

private theorem profile_term_9 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    Real.negMulLog ((profilePoly ![0, 0, 2, 1, 0]).eval p) =
      -(p^2*(1-p)^1*(1*p+2*(1-p))) * (2*Real.log p+1*Real.log (1-p)+Real.log (1*p+2*(1-p))) := by
  have h : (profilePoly ![0, 0, 2, 1, 0]).eval p = p^2*(1-p)^1*(1*p+2*(1-p)) := by
    simp [profilePoly, atomPoly_eval, Fin.sum_univ_succ]
    ring
  rw [h]
  have hp₀ : 0 < p := hp.1
  have hq₀ : 0 < 1 - p := sub_pos.mpr hp.2
  simpa using negMulLog_factor hp 2 1 (1*p+2*(1-p)) (by positivity)

private theorem profile_term_10 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    Real.negMulLog ((profilePoly ![0, 0, 3, 0, 0]).eval p) =
      -(p^2*(1-p)^2*3) * (2*Real.log p+2*Real.log (1-p)+Real.log 3) := by
  have h : (profilePoly ![0, 0, 3, 0, 0]).eval p = p^2*(1-p)^2*3 := by
    simp [profilePoly, atomPoly_eval, Fin.sum_univ_succ]
    ring
  rw [h]
  have hp₀ : 0 < p := hp.1
  have hq₀ : 0 < 1 - p := sub_pos.mpr hp.2
  simpa using negMulLog_factor hp 2 2 3 (by positivity)

private theorem profile_term_11 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    Real.negMulLog ((profilePoly ![0, 0, 3, 1, 0]).eval p) =
      -(p^2*(1-p)^1*(1*p+3*(1-p))) * (2*Real.log p+1*Real.log (1-p)+Real.log (1*p+3*(1-p))) := by
  have h : (profilePoly ![0, 0, 3, 1, 0]).eval p = p^2*(1-p)^1*(1*p+3*(1-p)) := by
    simp [profilePoly, atomPoly_eval, Fin.sum_univ_succ]
    ring
  rw [h]
  have hp₀ : 0 < p := hp.1
  have hq₀ : 0 < 1 - p := sub_pos.mpr hp.2
  simpa using negMulLog_factor hp 2 1 (1*p+3*(1-p)) (by positivity)

private theorem profile_term_12 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    Real.negMulLog ((profilePoly ![0, 0, 4, 0, 0]).eval p) =
      -(p^2*(1-p)^2*4) * (2*Real.log p+2*Real.log (1-p)+Real.log 4) := by
  have h : (profilePoly ![0, 0, 4, 0, 0]).eval p = p^2*(1-p)^2*4 := by
    simp [profilePoly, atomPoly_eval, Fin.sum_univ_succ]
    ring
  rw [h]
  have hp₀ : 0 < p := hp.1
  have hq₀ : 0 < 1 - p := sub_pos.mpr hp.2
  simpa using negMulLog_factor hp 2 2 4 (by positivity)

private theorem profile_term_13 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    Real.negMulLog ((profilePoly ![0, 0, 6, 0, 0]).eval p) =
      -(p^2*(1-p)^2*6) * (2*Real.log p+2*Real.log (1-p)+Real.log 6) := by
  have h : (profilePoly ![0, 0, 6, 0, 0]).eval p = p^2*(1-p)^2*6 := by
    simp [profilePoly, atomPoly_eval, Fin.sum_univ_succ]
    ring
  rw [h]
  have hp₀ : 0 < p := hp.1
  have hq₀ : 0 < 1 - p := sub_pos.mpr hp.2
  simpa using negMulLog_factor hp 2 2 6 (by positivity)

private theorem profile_term_14 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    Real.negMulLog ((profilePoly ![0, 1, 0, 0, 0]).eval p) =
      -(p^1*(1-p)^3*1) * (1*Real.log p+3*Real.log (1-p)+Real.log 1) := by
  have h : (profilePoly ![0, 1, 0, 0, 0]).eval p = p^1*(1-p)^3*1 := by
    simp [profilePoly, atomPoly_eval, Fin.sum_univ_succ]
  rw [h]
  have hp₀ : 0 < p := hp.1
  have hq₀ : 0 < 1 - p := sub_pos.mpr hp.2
  simpa using negMulLog_factor hp 1 3 1 (by positivity)

private theorem profile_term_15 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    Real.negMulLog ((profilePoly ![0, 1, 0, 1, 0]).eval p) =
      -(p^1*(1-p)^1*(p^2+(1-p)^2)) * (1*Real.log p+1*Real.log (1-p)+Real.log (p^2+(1-p)^2)) := by
  have h : (profilePoly ![0, 1, 0, 1, 0]).eval p = p^1*(1-p)^1*(p^2+(1-p)^2) := by
    simp [profilePoly, atomPoly_eval, Fin.sum_univ_succ]
    ring
  rw [h]
  have hp₀ : 0 < p := hp.1
  have hq₀ : 0 < 1 - p := sub_pos.mpr hp.2
  simpa using negMulLog_factor hp 1 1 (p^2+(1-p)^2) (by positivity)

private theorem profile_term_16 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    Real.negMulLog ((profilePoly ![0, 1, 1, 0, 0]).eval p) =
      -(p^1*(1-p)^2*(1*(1-p)+1*p)) * (1*Real.log p+2*Real.log (1-p)+Real.log (1*(1-p)+1*p)) := by
  have h : (profilePoly ![0, 1, 1, 0, 0]).eval p = p^1*(1-p)^2*(1*(1-p)+1*p) := by
    simp [profilePoly, atomPoly_eval, Fin.sum_univ_succ]
    ring
  rw [h]
  have hp₀ : 0 < p := hp.1
  have hq₀ : 0 < 1 - p := sub_pos.mpr hp.2
  simpa using negMulLog_factor hp 1 2 (1*(1-p)+1*p) (by positivity)

private theorem profile_term_17 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    Real.negMulLog ((profilePoly ![0, 1, 2, 0, 0]).eval p) =
      -(p^1*(1-p)^2*(1*(1-p)+2*p)) * (1*Real.log p+2*Real.log (1-p)+Real.log (1*(1-p)+2*p)) := by
  have h : (profilePoly ![0, 1, 2, 0, 0]).eval p = p^1*(1-p)^2*(1*(1-p)+2*p) := by
    simp [profilePoly, atomPoly_eval, Fin.sum_univ_succ]
    ring
  rw [h]
  have hp₀ : 0 < p := hp.1
  have hq₀ : 0 < 1 - p := sub_pos.mpr hp.2
  simpa using negMulLog_factor hp 1 2 (1*(1-p)+2*p) (by positivity)

private theorem profile_term_18 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    Real.negMulLog ((profilePoly ![0, 1, 3, 0, 0]).eval p) =
      -(p^1*(1-p)^2*(1*(1-p)+3*p)) * (1*Real.log p+2*Real.log (1-p)+Real.log (1*(1-p)+3*p)) := by
  have h : (profilePoly ![0, 1, 3, 0, 0]).eval p = p^1*(1-p)^2*(1*(1-p)+3*p) := by
    simp [profilePoly, atomPoly_eval, Fin.sum_univ_succ]
    ring
  rw [h]
  have hp₀ : 0 < p := hp.1
  have hq₀ : 0 < 1 - p := sub_pos.mpr hp.2
  simpa using negMulLog_factor hp 1 2 (1*(1-p)+3*p) (by positivity)

private theorem profile_term_19 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    Real.negMulLog ((profilePoly ![0, 2, 0, 0, 0]).eval p) =
      -(p^1*(1-p)^3*2) * (1*Real.log p+3*Real.log (1-p)+Real.log 2) := by
  have h : (profilePoly ![0, 2, 0, 0, 0]).eval p = p^1*(1-p)^3*2 := by
    simp [profilePoly, atomPoly_eval, Fin.sum_univ_succ]
    ring
  rw [h]
  have hp₀ : 0 < p := hp.1
  have hq₀ : 0 < 1 - p := sub_pos.mpr hp.2
  simpa using negMulLog_factor hp 1 3 2 (by positivity)

private theorem profile_term_20 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    Real.negMulLog ((profilePoly ![0, 2, 1, 0, 0]).eval p) =
      -(p^1*(1-p)^2*(2*(1-p)+1*p)) * (1*Real.log p+2*Real.log (1-p)+Real.log (2*(1-p)+1*p)) := by
  have h : (profilePoly ![0, 2, 1, 0, 0]).eval p = p^1*(1-p)^2*(2*(1-p)+1*p) := by
    simp [profilePoly, atomPoly_eval, Fin.sum_univ_succ]
    ring
  rw [h]
  have hp₀ : 0 < p := hp.1
  have hq₀ : 0 < 1 - p := sub_pos.mpr hp.2
  simpa using negMulLog_factor hp 1 2 (2*(1-p)+1*p) (by positivity)

private theorem profile_term_21 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    Real.negMulLog ((profilePoly ![0, 3, 0, 0, 0]).eval p) =
      -(p^1*(1-p)^3*3) * (1*Real.log p+3*Real.log (1-p)+Real.log 3) := by
  have h : (profilePoly ![0, 3, 0, 0, 0]).eval p = p^1*(1-p)^3*3 := by
    simp [profilePoly, atomPoly_eval, Fin.sum_univ_succ]
    ring
  rw [h]
  have hp₀ : 0 < p := hp.1
  have hq₀ : 0 < 1 - p := sub_pos.mpr hp.2
  simpa using negMulLog_factor hp 1 3 3 (by positivity)

private theorem profile_term_22 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    Real.negMulLog ((profilePoly ![0, 4, 0, 0, 0]).eval p) =
      -(p^1*(1-p)^3*4) * (1*Real.log p+3*Real.log (1-p)+Real.log 4) := by
  have h : (profilePoly ![0, 4, 0, 0, 0]).eval p = p^1*(1-p)^3*4 := by
    simp [profilePoly, atomPoly_eval, Fin.sum_univ_succ]
    ring
  rw [h]
  have hp₀ : 0 < p := hp.1
  have hq₀ : 0 < 1 - p := sub_pos.mpr hp.2
  simpa using negMulLog_factor hp 1 3 4 (by positivity)

private theorem profile_term_23 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    Real.negMulLog ((profilePoly ![1, 0, 0, 0, 0]).eval p) =
      -(p^0*(1-p)^4*1) * (0*Real.log p+4*Real.log (1-p)+Real.log 1) := by
  have h : (profilePoly ![1, 0, 0, 0, 0]).eval p = p^0*(1-p)^4*1 := by
    simp [profilePoly, atomPoly_eval, Fin.sum_univ_succ]
  rw [h]
  have hp₀ : 0 < p := hp.1
  have hq₀ : 0 < 1 - p := sub_pos.mpr hp.2
  simpa using negMulLog_factor hp 0 4 1 (by positivity)

set_option maxHeartbeats 1000000 in
private theorem budget_identity_0 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    profileEntropy (template 0) p = budgetEntropy (budget 0) p := by
  change profileEntropy (↑([
      ![0, 0, 0, 0, 1],
      ![0, 0, 0, 4, 0],
      ![0, 0, 6, 0, 0],
      ![0, 4, 0, 0, 0],
      ![1, 0, 0, 0, 0]] : List Profile)) p = _
  rw [profileEntropy_list]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, profile_term_0 p hp, profile_term_4 p hp, profile_term_13 p hp, profile_term_22 p hp, profile_term_23 p hp]
  norm_num [budgetEntropy, budget, Budget.A, Budget.B, binaryEntropy, Real.negMulLog,
    mixedLoss_formula, diagonalLoss_formula, log_four, log_six_eq]; ring

set_option maxHeartbeats 1000000 in
private theorem budget_identity_1 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    profileEntropy (template 1) p = budgetEntropy (budget 1) p := by
  change profileEntropy (↑([
      ![0, 0, 0, 0, 1],
      ![0, 0, 0, 3, 0],
      ![0, 0, 3, 1, 0],
      ![0, 1, 3, 0, 0],
      ![0, 3, 0, 0, 0],
      ![1, 0, 0, 0, 0]] : List Profile)) p = _
  rw [profileEntropy_list]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, profile_term_0 p hp, profile_term_3 p hp, profile_term_11 p hp, profile_term_18 p hp, profile_term_21 p hp, profile_term_23 p hp]
  norm_num [budgetEntropy, budget, Budget.A, Budget.B, binaryEntropy, Real.negMulLog,
    mixedLoss_formula, diagonalLoss_formula, log_four, log_six_eq]; ring

set_option maxHeartbeats 1000000 in
private theorem budget_identity_2 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    profileEntropy (template 2) p = budgetEntropy (budget 2) p := by
  change profileEntropy (↑([
      ![0, 0, 0, 0, 1],
      ![0, 0, 0, 2, 0],
      ![0, 0, 1, 2, 0],
      ![0, 0, 4, 0, 0],
      ![0, 2, 0, 0, 0],
      ![0, 2, 1, 0, 0],
      ![1, 0, 0, 0, 0]] : List Profile)) p = _
  rw [profileEntropy_list]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, profile_term_0 p hp, profile_term_2 p hp, profile_term_7 p hp, profile_term_12 p hp, profile_term_19 p hp, profile_term_20 p hp, profile_term_23 p hp]
  norm_num [budgetEntropy, budget, Budget.A, Budget.B, binaryEntropy, Real.negMulLog,
    mixedLoss_formula, diagonalLoss_formula, log_four, log_six_eq]; ring

set_option maxHeartbeats 1000000 in
private theorem budget_identity_3 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    profileEntropy (template 3) p = budgetEntropy (budget 3) p := by
  change profileEntropy (↑([
      ![0, 0, 0, 0, 1],
      ![0, 0, 0, 3, 0],
      ![0, 0, 3, 0, 0],
      ![0, 0, 3, 0, 0],
      ![0, 1, 0, 1, 0],
      ![0, 3, 0, 0, 0],
      ![1, 0, 0, 0, 0]] : List Profile)) p = _
  rw [profileEntropy_list]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, profile_term_0 p hp, profile_term_3 p hp, profile_term_10 p hp, profile_term_15 p hp, profile_term_21 p hp, profile_term_23 p hp]
  norm_num [budgetEntropy, budget, Budget.A, Budget.B, binaryEntropy, Real.negMulLog,
    mixedLoss_formula, diagonalLoss_formula, log_four, log_six_eq]; ring

set_option maxHeartbeats 1000000 in
private theorem budget_identity_4 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    profileEntropy (template 4) p = budgetEntropy (budget 4) p := by
  change profileEntropy (↑([
      ![0, 0, 0, 0, 1],
      ![0, 0, 0, 1, 0],
      ![0, 0, 0, 3, 0],
      ![0, 0, 3, 0, 0],
      ![0, 0, 3, 0, 0],
      ![0, 1, 0, 0, 0],
      ![0, 3, 0, 0, 0],
      ![1, 0, 0, 0, 0]] : List Profile)) p = _
  rw [profileEntropy_list]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, profile_term_0 p hp, profile_term_1 p hp, profile_term_3 p hp, profile_term_10 p hp, profile_term_14 p hp, profile_term_21 p hp, profile_term_23 p hp]
  norm_num [budgetEntropy, budget, Budget.A, Budget.B, binaryEntropy, Real.negMulLog,
    mixedLoss_formula, diagonalLoss_formula, log_four, log_six_eq]; ring

set_option maxHeartbeats 1000000 in
private theorem budget_identity_5 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    profileEntropy (template 5) p = budgetEntropy (budget 5) p := by
  change profileEntropy (↑([
      ![0, 0, 0, 0, 1],
      ![0, 0, 0, 2, 0],
      ![0, 0, 1, 1, 0],
      ![0, 0, 2, 1, 0],
      ![0, 1, 1, 0, 0],
      ![0, 1, 2, 0, 0],
      ![0, 2, 0, 0, 0],
      ![1, 0, 0, 0, 0]] : List Profile)) p = _
  rw [profileEntropy_list]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, profile_term_0 p hp, profile_term_2 p hp, profile_term_6 p hp, profile_term_9 p hp, profile_term_16 p hp, profile_term_17 p hp, profile_term_19 p hp, profile_term_23 p hp]
  norm_num [budgetEntropy, budget, Budget.A, Budget.B, binaryEntropy, Real.negMulLog,
    mixedLoss_formula, diagonalLoss_formula, log_four, log_six_eq]; ring

set_option maxHeartbeats 1000000 in
private theorem budget_identity_6 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    profileEntropy (template 6) p = budgetEntropy (budget 6) p := by
  change profileEntropy (↑([
      ![0, 0, 0, 0, 1],
      ![0, 0, 0, 1, 0],
      ![0, 0, 0, 2, 0],
      ![0, 0, 2, 0, 0],
      ![0, 0, 2, 1, 0],
      ![0, 1, 0, 0, 0],
      ![0, 1, 2, 0, 0],
      ![0, 2, 0, 0, 0],
      ![1, 0, 0, 0, 0]] : List Profile)) p = _
  rw [profileEntropy_list]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, profile_term_0 p hp, profile_term_1 p hp, profile_term_2 p hp, profile_term_8 p hp, profile_term_9 p hp, profile_term_14 p hp, profile_term_17 p hp, profile_term_19 p hp, profile_term_23 p hp]
  norm_num [budgetEntropy, budget, Budget.A, Budget.B, binaryEntropy, Real.negMulLog,
    mixedLoss_formula, diagonalLoss_formula, log_four, log_six_eq]; ring

set_option maxHeartbeats 1000000 in
private theorem budget_identity_7 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    profileEntropy (template 7) p = budgetEntropy (budget 7) p := by
  change profileEntropy (↑([
      ![0, 0, 0, 0, 1],
      ![0, 0, 0, 2, 0],
      ![0, 0, 0, 2, 0],
      ![0, 0, 1, 0, 0],
      ![0, 0, 1, 0, 0],
      ![0, 0, 4, 0, 0],
      ![0, 2, 0, 0, 0],
      ![0, 2, 0, 0, 0],
      ![1, 0, 0, 0, 0]] : List Profile)) p = _
  rw [profileEntropy_list]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, profile_term_0 p hp, profile_term_2 p hp, profile_term_5 p hp, profile_term_12 p hp, profile_term_19 p hp, profile_term_23 p hp]
  norm_num [budgetEntropy, budget, Budget.A, Budget.B, binaryEntropy, Real.negMulLog,
    mixedLoss_formula, diagonalLoss_formula, log_four, log_six_eq]; ring

set_option maxHeartbeats 1000000 in
private theorem budget_identity_8 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    profileEntropy (template 8) p = budgetEntropy (budget 8) p := by
  change profileEntropy (↑([
      ![0, 0, 0, 0, 1],
      ![0, 0, 0, 2, 0],
      ![0, 0, 1, 1, 0],
      ![0, 0, 2, 0, 0],
      ![0, 0, 2, 0, 0],
      ![0, 1, 0, 1, 0],
      ![0, 1, 1, 0, 0],
      ![0, 2, 0, 0, 0],
      ![1, 0, 0, 0, 0]] : List Profile)) p = _
  rw [profileEntropy_list]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, profile_term_0 p hp, profile_term_2 p hp, profile_term_6 p hp, profile_term_8 p hp, profile_term_15 p hp, profile_term_16 p hp, profile_term_19 p hp, profile_term_23 p hp]
  norm_num [budgetEntropy, budget, Budget.A, Budget.B, binaryEntropy, Real.negMulLog,
    mixedLoss_formula, diagonalLoss_formula, log_four, log_six_eq]; ring

set_option maxHeartbeats 1000000 in
private theorem budget_identity_9 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    profileEntropy (template 9) p = budgetEntropy (budget 9) p := by
  change profileEntropy (↑([
      ![0, 0, 0, 0, 1],
      ![0, 0, 0, 1, 0],
      ![0, 0, 0, 1, 0],
      ![0, 0, 1, 2, 0],
      ![0, 0, 2, 0, 0],
      ![0, 0, 2, 0, 0],
      ![0, 1, 0, 0, 0],
      ![0, 1, 0, 0, 0],
      ![0, 2, 1, 0, 0],
      ![1, 0, 0, 0, 0]] : List Profile)) p = _
  rw [profileEntropy_list]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, profile_term_0 p hp, profile_term_1 p hp, profile_term_7 p hp, profile_term_8 p hp, profile_term_14 p hp, profile_term_20 p hp, profile_term_23 p hp]
  norm_num [budgetEntropy, budget, Budget.A, Budget.B, binaryEntropy, Real.negMulLog,
    mixedLoss_formula, diagonalLoss_formula, log_four, log_six_eq]; ring

set_option maxHeartbeats 1000000 in
private theorem budget_identity_10 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    profileEntropy (template 10) p = budgetEntropy (budget 10) p := by
  change profileEntropy (↑([
      ![0, 0, 0, 0, 1],
      ![0, 0, 0, 1, 0],
      ![0, 0, 0, 2, 0],
      ![0, 0, 1, 0, 0],
      ![0, 0, 1, 0, 0],
      ![0, 0, 2, 1, 0],
      ![0, 1, 0, 0, 0],
      ![0, 1, 2, 0, 0],
      ![0, 2, 0, 0, 0],
      ![1, 0, 0, 0, 0]] : List Profile)) p = _
  rw [profileEntropy_list]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, profile_term_0 p hp, profile_term_1 p hp, profile_term_2 p hp, profile_term_5 p hp, profile_term_9 p hp, profile_term_14 p hp, profile_term_17 p hp, profile_term_19 p hp, profile_term_23 p hp]
  norm_num [budgetEntropy, budget, Budget.A, Budget.B, binaryEntropy, Real.negMulLog,
    mixedLoss_formula, diagonalLoss_formula, log_four, log_six_eq]; ring

set_option maxHeartbeats 1000000 in
private theorem budget_identity_11 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    profileEntropy (template 11) p = budgetEntropy (budget 11) p := by
  change profileEntropy (↑([
      ![0, 0, 0, 0, 1],
      ![0, 0, 0, 1, 0],
      ![0, 0, 0, 2, 0],
      ![0, 0, 1, 1, 0],
      ![0, 0, 2, 0, 0],
      ![0, 0, 2, 0, 0],
      ![0, 1, 0, 0, 0],
      ![0, 1, 1, 0, 0],
      ![0, 2, 0, 0, 0],
      ![1, 0, 0, 0, 0]] : List Profile)) p = _
  rw [profileEntropy_list]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, profile_term_0 p hp, profile_term_1 p hp, profile_term_2 p hp, profile_term_6 p hp, profile_term_8 p hp, profile_term_14 p hp, profile_term_16 p hp, profile_term_19 p hp, profile_term_23 p hp]
  norm_num [budgetEntropy, budget, Budget.A, Budget.B, binaryEntropy, Real.negMulLog,
    mixedLoss_formula, diagonalLoss_formula, log_four, log_six_eq]; ring

set_option maxHeartbeats 1000000 in
private theorem budget_identity_12 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    profileEntropy (template 12) p = budgetEntropy (budget 12) p := by
  change profileEntropy (↑([
      ![0, 0, 0, 0, 1],
      ![0, 0, 0, 1, 0],
      ![0, 0, 0, 1, 0],
      ![0, 0, 0, 2, 0],
      ![0, 0, 2, 0, 0],
      ![0, 0, 2, 0, 0],
      ![0, 0, 2, 0, 0],
      ![0, 1, 0, 0, 0],
      ![0, 1, 0, 0, 0],
      ![0, 2, 0, 0, 0],
      ![1, 0, 0, 0, 0]] : List Profile)) p = _
  rw [profileEntropy_list]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, profile_term_0 p hp, profile_term_1 p hp, profile_term_2 p hp, profile_term_8 p hp, profile_term_14 p hp, profile_term_19 p hp, profile_term_23 p hp]
  norm_num [budgetEntropy, budget, Budget.A, Budget.B, binaryEntropy, Real.negMulLog,
    mixedLoss_formula, diagonalLoss_formula, log_four, log_six_eq]; ring

set_option maxHeartbeats 1000000 in
private theorem budget_identity_13 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    profileEntropy (template 13) p = budgetEntropy (budget 13) p := by
  change profileEntropy (↑([
      ![0, 0, 0, 0, 1],
      ![0, 0, 0, 1, 0],
      ![0, 0, 0, 1, 0],
      ![0, 0, 1, 1, 0],
      ![0, 0, 1, 1, 0],
      ![0, 0, 2, 0, 0],
      ![0, 1, 0, 0, 0],
      ![0, 1, 0, 0, 0],
      ![0, 1, 1, 0, 0],
      ![0, 1, 1, 0, 0],
      ![1, 0, 0, 0, 0]] : List Profile)) p = _
  rw [profileEntropy_list]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, profile_term_0 p hp, profile_term_1 p hp, profile_term_6 p hp, profile_term_8 p hp, profile_term_14 p hp, profile_term_16 p hp, profile_term_23 p hp]
  norm_num [budgetEntropy, budget, Budget.A, Budget.B, binaryEntropy, Real.negMulLog,
    mixedLoss_formula, diagonalLoss_formula, log_four, log_six_eq]; ring

set_option maxHeartbeats 1000000 in
private theorem budget_identity_14 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    profileEntropy (template 14) p = budgetEntropy (budget 14) p := by
  change profileEntropy (↑([
      ![0, 0, 0, 0, 1],
      ![0, 0, 0, 1, 0],
      ![0, 0, 0, 2, 0],
      ![0, 0, 1, 0, 0],
      ![0, 0, 1, 0, 0],
      ![0, 0, 2, 0, 0],
      ![0, 0, 2, 0, 0],
      ![0, 1, 0, 0, 0],
      ![0, 1, 0, 1, 0],
      ![0, 2, 0, 0, 0],
      ![1, 0, 0, 0, 0]] : List Profile)) p = _
  rw [profileEntropy_list]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, profile_term_0 p hp, profile_term_1 p hp, profile_term_2 p hp, profile_term_5 p hp, profile_term_8 p hp, profile_term_14 p hp, profile_term_15 p hp, profile_term_19 p hp, profile_term_23 p hp]
  norm_num [budgetEntropy, budget, Budget.A, Budget.B, binaryEntropy, Real.negMulLog,
    mixedLoss_formula, diagonalLoss_formula, log_four, log_six_eq]; ring

set_option maxHeartbeats 1000000 in
private theorem budget_identity_15 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    profileEntropy (template 15) p = budgetEntropy (budget 15) p := by
  change profileEntropy (↑([
      ![0, 0, 0, 0, 1],
      ![0, 0, 0, 1, 0],
      ![0, 0, 0, 1, 0],
      ![0, 0, 0, 2, 0],
      ![0, 0, 1, 0, 0],
      ![0, 0, 1, 0, 0],
      ![0, 0, 2, 0, 0],
      ![0, 0, 2, 0, 0],
      ![0, 1, 0, 0, 0],
      ![0, 1, 0, 0, 0],
      ![0, 2, 0, 0, 0],
      ![1, 0, 0, 0, 0]] : List Profile)) p = _
  rw [profileEntropy_list]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, profile_term_0 p hp, profile_term_1 p hp, profile_term_2 p hp, profile_term_5 p hp, profile_term_8 p hp, profile_term_14 p hp, profile_term_19 p hp, profile_term_23 p hp]
  norm_num [budgetEntropy, budget, Budget.A, Budget.B, binaryEntropy, Real.negMulLog,
    mixedLoss_formula, diagonalLoss_formula, log_four, log_six_eq]; ring

set_option maxHeartbeats 1000000 in
private theorem budget_identity_16 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    profileEntropy (template 16) p = budgetEntropy (budget 16) p := by
  change profileEntropy (↑([
      ![0, 0, 0, 0, 1],
      ![0, 0, 0, 1, 0],
      ![0, 0, 0, 1, 0],
      ![0, 0, 1, 0, 0],
      ![0, 0, 1, 0, 0],
      ![0, 0, 1, 1, 0],
      ![0, 0, 1, 1, 0],
      ![0, 1, 0, 0, 0],
      ![0, 1, 0, 0, 0],
      ![0, 1, 1, 0, 0],
      ![0, 1, 1, 0, 0],
      ![1, 0, 0, 0, 0]] : List Profile)) p = _
  rw [profileEntropy_list]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, profile_term_0 p hp, profile_term_1 p hp, profile_term_5 p hp, profile_term_6 p hp, profile_term_14 p hp, profile_term_16 p hp, profile_term_23 p hp]
  norm_num [budgetEntropy, budget, Budget.A, Budget.B, binaryEntropy, Real.negMulLog,
    mixedLoss_formula, diagonalLoss_formula, log_four, log_six_eq]; ring

set_option maxHeartbeats 1000000 in
private theorem budget_identity_17 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    profileEntropy (template 17) p = budgetEntropy (budget 17) p := by
  change profileEntropy (↑([
      ![0, 0, 0, 0, 1],
      ![0, 0, 0, 1, 0],
      ![0, 0, 0, 1, 0],
      ![0, 0, 0, 1, 0],
      ![0, 0, 1, 0, 0],
      ![0, 0, 1, 0, 0],
      ![0, 0, 1, 1, 0],
      ![0, 0, 2, 0, 0],
      ![0, 1, 0, 0, 0],
      ![0, 1, 0, 0, 0],
      ![0, 1, 0, 0, 0],
      ![0, 1, 1, 0, 0],
      ![1, 0, 0, 0, 0]] : List Profile)) p = _
  rw [profileEntropy_list]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, profile_term_0 p hp, profile_term_1 p hp, profile_term_5 p hp, profile_term_6 p hp, profile_term_8 p hp, profile_term_14 p hp, profile_term_16 p hp, profile_term_23 p hp]
  norm_num [budgetEntropy, budget, Budget.A, Budget.B, binaryEntropy, Real.negMulLog,
    mixedLoss_formula, diagonalLoss_formula, log_four, log_six_eq]; ring

set_option maxHeartbeats 1000000 in
private theorem budget_identity_18 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    profileEntropy (template 18) p = budgetEntropy (budget 18) p := by
  change profileEntropy (↑([
      ![0, 0, 0, 0, 1],
      ![0, 0, 0, 1, 0],
      ![0, 0, 0, 1, 0],
      ![0, 0, 1, 0, 0],
      ![0, 0, 1, 0, 0],
      ![0, 0, 1, 0, 0],
      ![0, 0, 1, 0, 0],
      ![0, 0, 1, 1, 0],
      ![0, 1, 0, 0, 0],
      ![0, 1, 0, 0, 0],
      ![0, 1, 0, 1, 0],
      ![0, 1, 1, 0, 0],
      ![1, 0, 0, 0, 0]] : List Profile)) p = _
  rw [profileEntropy_list]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, profile_term_0 p hp, profile_term_1 p hp, profile_term_5 p hp, profile_term_6 p hp, profile_term_14 p hp, profile_term_15 p hp, profile_term_16 p hp, profile_term_23 p hp]
  norm_num [budgetEntropy, budget, Budget.A, Budget.B, binaryEntropy, Real.negMulLog,
    mixedLoss_formula, diagonalLoss_formula, log_four, log_six_eq]; ring

set_option maxHeartbeats 1000000 in
private theorem budget_identity_19 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    profileEntropy (template 19) p = budgetEntropy (budget 19) p := by
  change profileEntropy (↑([
      ![0, 0, 0, 0, 1],
      ![0, 0, 0, 1, 0],
      ![0, 0, 0, 1, 0],
      ![0, 0, 0, 1, 0],
      ![0, 0, 1, 0, 0],
      ![0, 0, 1, 0, 0],
      ![0, 0, 1, 0, 0],
      ![0, 0, 1, 0, 0],
      ![0, 0, 1, 1, 0],
      ![0, 1, 0, 0, 0],
      ![0, 1, 0, 0, 0],
      ![0, 1, 0, 0, 0],
      ![0, 1, 1, 0, 0],
      ![1, 0, 0, 0, 0]] : List Profile)) p = _
  rw [profileEntropy_list]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, profile_term_0 p hp, profile_term_1 p hp, profile_term_5 p hp, profile_term_6 p hp, profile_term_14 p hp, profile_term_16 p hp, profile_term_23 p hp]
  norm_num [budgetEntropy, budget, Budget.A, Budget.B, binaryEntropy, Real.negMulLog,
    mixedLoss_formula, diagonalLoss_formula, log_four, log_six_eq]; ring

set_option maxHeartbeats 1000000 in
private theorem budget_identity_20 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    profileEntropy (template 20) p = budgetEntropy (budget 20) p := by
  change profileEntropy (↑([
      ![0, 0, 0, 0, 1],
      ![0, 0, 0, 1, 0],
      ![0, 0, 0, 1, 0],
      ![0, 0, 0, 1, 0],
      ![0, 0, 0, 1, 0],
      ![0, 0, 1, 0, 0],
      ![0, 0, 1, 0, 0],
      ![0, 0, 1, 0, 0],
      ![0, 0, 1, 0, 0],
      ![0, 0, 2, 0, 0],
      ![0, 1, 0, 0, 0],
      ![0, 1, 0, 0, 0],
      ![0, 1, 0, 0, 0],
      ![0, 1, 0, 0, 0],
      ![1, 0, 0, 0, 0]] : List Profile)) p = _
  rw [profileEntropy_list]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, profile_term_0 p hp, profile_term_1 p hp, profile_term_5 p hp, profile_term_8 p hp, profile_term_14 p hp, profile_term_23 p hp]
  norm_num [budgetEntropy, budget, Budget.A, Budget.B, binaryEntropy, Real.negMulLog,
    mixedLoss_formula, diagonalLoss_formula, log_four, log_six_eq]; ring

set_option maxHeartbeats 1000000 in
private theorem budget_identity_21 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    profileEntropy (template 21) p = budgetEntropy (budget 21) p := by
  change profileEntropy (↑([
      ![0, 0, 0, 0, 1],
      ![0, 0, 0, 1, 0],
      ![0, 0, 0, 1, 0],
      ![0, 0, 0, 1, 0],
      ![0, 0, 1, 0, 0],
      ![0, 0, 1, 0, 0],
      ![0, 0, 1, 0, 0],
      ![0, 0, 1, 0, 0],
      ![0, 0, 1, 0, 0],
      ![0, 0, 1, 0, 0],
      ![0, 1, 0, 0, 0],
      ![0, 1, 0, 0, 0],
      ![0, 1, 0, 0, 0],
      ![0, 1, 0, 1, 0],
      ![1, 0, 0, 0, 0]] : List Profile)) p = _
  rw [profileEntropy_list]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, profile_term_0 p hp, profile_term_1 p hp, profile_term_5 p hp, profile_term_14 p hp, profile_term_15 p hp, profile_term_23 p hp]
  norm_num [budgetEntropy, budget, Budget.A, Budget.B, binaryEntropy, Real.negMulLog,
    mixedLoss_formula, diagonalLoss_formula, log_four, log_six_eq]; ring

set_option maxHeartbeats 1000000 in
private theorem budget_identity_22 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    profileEntropy (template 22) p = budgetEntropy (budget 22) p := by
  change profileEntropy (↑([
      ![0, 0, 0, 0, 1],
      ![0, 0, 0, 1, 0],
      ![0, 0, 0, 1, 0],
      ![0, 0, 0, 1, 0],
      ![0, 0, 0, 1, 0],
      ![0, 0, 1, 0, 0],
      ![0, 0, 1, 0, 0],
      ![0, 0, 1, 0, 0],
      ![0, 0, 1, 0, 0],
      ![0, 0, 1, 0, 0],
      ![0, 0, 1, 0, 0],
      ![0, 1, 0, 0, 0],
      ![0, 1, 0, 0, 0],
      ![0, 1, 0, 0, 0],
      ![0, 1, 0, 0, 0],
      ![1, 0, 0, 0, 0]] : List Profile)) p = _
  rw [profileEntropy_list]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, profile_term_0 p hp, profile_term_1 p hp, profile_term_5 p hp, profile_term_14 p hp, profile_term_23 p hp]
  norm_num [budgetEntropy, budget, Budget.A, Budget.B, binaryEntropy, Real.negMulLog,
    mixedLoss_formula, diagonalLoss_formula, log_four, log_six_eq]; ring

theorem budget_identity (i : Fin 23) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    profileEntropy (template i) p = budgetEntropy (budget i) p := by
  fin_cases i
  · exact budget_identity_0 p hp
  · exact budget_identity_1 p hp
  · exact budget_identity_2 p hp
  · exact budget_identity_3 p hp
  · exact budget_identity_4 p hp
  · exact budget_identity_5 p hp
  · exact budget_identity_6 p hp
  · exact budget_identity_7 p hp
  · exact budget_identity_8 p hp
  · exact budget_identity_9 p hp
  · exact budget_identity_10 p hp
  · exact budget_identity_11 p hp
  · exact budget_identity_12 p hp
  · exact budget_identity_13 p hp
  · exact budget_identity_14 p hp
  · exact budget_identity_15 p hp
  · exact budget_identity_16 p hp
  · exact budget_identity_17 p hp
  · exact budget_identity_18 p hp
  · exact budget_identity_19 p hp
  · exact budget_identity_20 p hp
  · exact budget_identity_21 p hp
  · exact budget_identity_22 p hp

end Bernoulli4
