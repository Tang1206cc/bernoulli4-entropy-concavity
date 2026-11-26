module

public import Bernoulli4.MixedLossJets
public import Bernoulli4.Budget

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

/-! Explicit algebraic witnesses for the four mixed-loss bounds. -/

namespace Bernoulli4

open Polynomial Set

private theorem to_positive_ratio {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ∃ t : ℝ, 0 < t ∧ p = t/(1+t) := by
  let t := p/(1-p)
  have ht : 0 < t := div_pos hp.1 (sub_pos.mpr hp.2)
  refine ⟨t, ht, ?_⟩
  apply (eq_div_iff (by positivity : 1+t ≠ 0)).mpr
  dsimp [t]
  field_simp [sub_ne_zero.mpr (ne_of_gt hp.2)]
  ring

set_option maxHeartbeats 4000000 in
private theorem f11_six_ratio (t : ℝ) (ht : 0 < t) :
    mixedLossJet 1 1 6 (t/(1+t)) =
      (12*t^8 + 60*t^7 + 108*t^6 + 84*t^5 + 48*t^4 + 84*t^3 + 108*t^2 + 60*t + 12) / (t^4) := by
  have h₁ : 1+t ≠ 0 := by positivity
  have h₂ : 1 - t/(1+t) = 1/(1+t) := by field_simp; ring
  unfold mixedLossJet
  rw [f11_piece0, f11_piece1, f11_piece2, f11_piece3]
  simp only [h₂]
  field_simp [show t ≠ 0 by positivity]
  ring

private theorem f11_six_pos (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    0 ≤ mixedLossJet 1 1 6 p := by
  obtain ⟨t, ht, rfl⟩ := to_positive_ratio hp
  rw [f11_six_ratio t ht]
  positivity

theorem f11_curvature_midpoint :
    deriv (deriv (mixedLoss 1 1)) (1/2 : ℝ) = -1-2*Real.log 2 := by
  rw [deriv2_mixedLoss (by norm_num) (by norm_num) (by norm_num)]
  exact f11_mid2

private theorem f11_curvature_growth {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    -1-2*Real.log 2 + (40)/2*(p-1/2)^2 ≤
      deriv (deriv (mixedLoss 1 1)) p := by
  let h := hasDerivAt_mixedLossJet (a := 1) (b := 1) (by norm_num) (by norm_num)
  have hg := curvature_quadratic_growth (c := (1/2 : ℝ)) (by norm_num) hp
    (fun _ hx => h 2 hx) (fun _ hx => h 3 hx) (fun _ hx => h 4 hx) (fun _ hx => h 5 hx)
    f11_six_pos f11_mid3 f11_mid5
  rw [f11_mid2, f11_mid4] at hg
  rw [deriv2_mixedLoss (by norm_num) (by norm_num) hp]
  exact hg

theorem f11_curvature_bound {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    -1-2*Real.log 2 ≤ deriv (deriv (mixedLoss 1 1)) p := by
  have h₄ : 0 ≤ (40 : ℝ) := by
    linarith [log_three_bounds.1, log_three_bounds.2]
  have hg : 0 ≤ (40)/2*(p-1/2)^2 := by positivity
  linarith [f11_curvature_growth hp]

set_option maxHeartbeats 4000000 in
private theorem f12_six_ratio (t : ℝ) (ht : 0 < t) :
    mixedLossJet 1 2 6 (t/(1+t)) =
      (192*(t + 1)^8*(4*t^10 + 40*t^9 + 159*t^8 + 311*t^7 + 257*t^6 + 159*t^5 + 257*t^4 + 311*t^3 + 159*t^2 + 40*t + 4)) / (t^4*(t + 2)^5*(2*t + 1)^5) := by
  have h₁ : 1+t ≠ 0 := by positivity
  have h₂ : 1 - t/(1+t) = 1/(1+t) := by field_simp; ring
  have h₃ : t/(1+t)+1 = (2*t+1)/(1+t) := by field_simp; ring
  have h₄ : 2-t/(1+t) = (t+2)/(1+t) := by field_simp; ring
  have h₅ : (2 : ℝ)*t+1 ≠ 0 := by positivity
  have h₆ : t+2 ≠ 0 := by positivity
  unfold mixedLossJet
  rw [f12_piece0, f12_piece1, f12_piece2, f12_piece3]
  simp only [h₂, h₃, h₄]
  field_simp [ht.ne', h₁, h₅, h₆]
  ring

private theorem f12_six_pos (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    0 ≤ mixedLossJet 1 2 6 p := by
  obtain ⟨t, ht, rfl⟩ := to_positive_ratio hp
  rw [f12_six_ratio t ht]
  positivity

theorem f12_curvature_midpoint :
    deriv (deriv (mixedLoss 1 2)) (1/2 : ℝ) = -4/3-4*Real.log 3 := by
  rw [deriv2_mixedLoss (by norm_num) (by norm_num) (by norm_num)]
  exact f12_mid2

private theorem f12_curvature_growth {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    -4/3-4*Real.log 3 + (1216/27+48*Real.log 3)/2*(p-1/2)^2 ≤
      deriv (deriv (mixedLoss 1 2)) p := by
  let h := hasDerivAt_mixedLossJet (a := 1) (b := 2) (by norm_num) (by norm_num)
  have hg := curvature_quadratic_growth (c := (1/2 : ℝ)) (by norm_num) hp
    (fun _ hx => h 2 hx) (fun _ hx => h 3 hx) (fun _ hx => h 4 hx) (fun _ hx => h 5 hx)
    f12_six_pos f12_mid3 f12_mid5
  rw [f12_mid2, f12_mid4] at hg
  rw [deriv2_mixedLoss (by norm_num) (by norm_num) hp]
  exact hg

theorem f12_curvature_bound {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    -4/3-4*Real.log 3 ≤ deriv (deriv (mixedLoss 1 2)) p := by
  have h₄ : 0 ≤ (1216/27+48*Real.log 3 : ℝ) := by
    linarith [log_three_bounds.1, log_three_bounds.2]
  have hg : 0 ≤ (1216/27+48*Real.log 3)/2*(p-1/2)^2 := by positivity
  linarith [f12_curvature_growth hp]

set_option maxHeartbeats 4000000 in
private theorem f21_six_ratio (t : ℝ) (ht : 0 < t) :
    mixedLossJet 2 1 6 (t/(1+t)) =
      (24*(t + 1)^8*(16*t^10 + 136*t^9 + 408*t^8 + 452*t^7 + 260*t^6 + 129*t^5 + 260*t^4 + 452*t^3 + 408*t^2 + 136*t + 16)) / (t^4*(t + 2)^5*(2*t + 1)^5) := by
  have h₁ : 1+t ≠ 0 := by positivity
  have h₂ : 1 - t/(1+t) = 1/(1+t) := by field_simp; ring
  have h₃ : t/(1+t)+1 = (2*t+1)/(1+t) := by field_simp; ring
  have h₄ : 2-t/(1+t) = (t+2)/(1+t) := by field_simp; ring
  have h₅ : (2 : ℝ)*t+1 ≠ 0 := by positivity
  have h₆ : t+2 ≠ 0 := by positivity
  unfold mixedLossJet
  rw [f21_piece0, f21_piece1, f21_piece2, f21_piece3]
  simp only [h₂, h₃, h₄]
  field_simp [ht.ne', h₁, h₅, h₆]
  ring

private theorem f21_six_pos (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    0 ≤ mixedLossJet 2 1 6 p := by
  obtain ⟨t, ht, rfl⟩ := to_positive_ratio hp
  rw [f21_six_ratio t ht]
  positivity

theorem f21_curvature_midpoint :
    deriv (deriv (mixedLoss 2 1)) (1/2 : ℝ) = -4/3-2*Real.log 3 := by
  rw [deriv2_mixedLoss (by norm_num) (by norm_num) (by norm_num)]
  exact f21_mid2

private theorem f21_curvature_growth {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    -4/3-2*Real.log 3 + (1600/27-48*Real.log 3)/2*(p-1/2)^2 ≤
      deriv (deriv (mixedLoss 2 1)) p := by
  let h := hasDerivAt_mixedLossJet (a := 2) (b := 1) (by norm_num) (by norm_num)
  have hg := curvature_quadratic_growth (c := (1/2 : ℝ)) (by norm_num) hp
    (fun _ hx => h 2 hx) (fun _ hx => h 3 hx) (fun _ hx => h 4 hx) (fun _ hx => h 5 hx)
    f21_six_pos f21_mid3 f21_mid5
  rw [f21_mid2, f21_mid4] at hg
  rw [deriv2_mixedLoss (by norm_num) (by norm_num) hp]
  exact hg

theorem f21_curvature_bound {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    -4/3-2*Real.log 3 ≤ deriv (deriv (mixedLoss 2 1)) p := by
  have h₄ : 0 ≤ (1600/27-48*Real.log 3 : ℝ) := by
    linarith [log_three_bounds.1, log_three_bounds.2]
  have hg : 0 ≤ (1600/27-48*Real.log 3)/2*(p-1/2)^2 := by positivity
  linarith [f21_curvature_growth hp]

set_option maxHeartbeats 4000000 in
private theorem f13_six_ratio (t : ℝ) (ht : 0 < t) :
    mixedLossJet 1 3 6 (t/(1+t)) =
      (972*(t + 1)^8*(9*t^10 + 129*t^9 + 722*t^8 + 1918*t^7 + 1205*t^6 + 226*t^5 + 1205*t^4 + 1918*t^3 + 722*t^2 + 129*t + 9)) / (t^4*(t + 3)^5*(3*t + 1)^5) := by
  have h₁ : 1+t ≠ 0 := by positivity
  have h₂ : 1 - t/(1+t) = 1/(1+t) := by field_simp; ring
  have h₃ : 2*(t/(1+t))+1 = (3*t+1)/(1+t) := by field_simp; ring
  have h₄ : 3-2*(t/(1+t)) = (t+3)/(1+t) := by field_simp; ring
  have h₅ : (3 : ℝ)*t+1 ≠ 0 := by positivity
  have h₆ : t+3 ≠ 0 := by positivity
  unfold mixedLossJet
  rw [f13_piece0, f13_piece1, f13_piece2, f13_piece3]
  simp only [h₂, h₃, h₄]
  field_simp [ht.ne', h₁, h₅, h₆]
  ring

private theorem f13_six_pos (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    0 ≤ mixedLossJet 1 3 6 p := by
  obtain ⟨t, ht, rfl⟩ := to_positive_ratio hp
  rw [f13_six_ratio t ht]
  positivity

theorem f13_curvature_midpoint :
    deriv (deriv (mixedLoss 1 3)) (1/2 : ℝ) = -3/2-12*Real.log 2 := by
  rw [deriv2_mixedLoss (by norm_num) (by norm_num) (by norm_num)]
  exact f13_mid2

private theorem f13_curvature_growth {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    -3/2-12*Real.log 2 + (45+192*Real.log 2)/2*(p-1/2)^2 ≤
      deriv (deriv (mixedLoss 1 3)) p := by
  let h := hasDerivAt_mixedLossJet (a := 1) (b := 3) (by norm_num) (by norm_num)
  have hg := curvature_quadratic_growth (c := (1/2 : ℝ)) (by norm_num) hp
    (fun _ hx => h 2 hx) (fun _ hx => h 3 hx) (fun _ hx => h 4 hx) (fun _ hx => h 5 hx)
    f13_six_pos f13_mid3 f13_mid5
  rw [f13_mid2, f13_mid4] at hg
  rw [deriv2_mixedLoss (by norm_num) (by norm_num) hp]
  exact hg

theorem f13_curvature_bound {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    -3/2 - 12*Real.log 2 + (45/8 + 24*Real.log 2)*(2*p-1)^2 ≤
      deriv (deriv (mixedLoss 1 3)) p := by
  convert f13_curvature_growth hp using 1
  ring

end Bernoulli4
