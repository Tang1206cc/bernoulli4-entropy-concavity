module

public import Bernoulli4.BudgetCurvature
public import Bernoulli4.Classification
public import Bernoulli4.EqualWeight
public import Bernoulli4.ProfileAudit

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! The sharp curvature theorem for every positive real weight vector. -/

namespace Bernoulli4

open Set Filter
open scoped Topology BigOperators

private def singleMask : Fin 4 → Outcome := ![1, 2, 4, 8]

private theorem selected_single (i : Fin 4) : selected (singleMask i) = {i} := by
  revert i
  decide +kernel

private theorem weighted_single (w : Fin 4 → ℝ) (i : Fin 4) :
    weightedSum w (singleMask i) = w i := by
  simp [weightedSum, selected_single]

theorem entropy_template {w : Fin 4 → ℝ} (hw : ∀ i, 0 < w i) :
    ∃ i : Fin 23,
      (∀ p ∈ Ioo (0 : ℝ) 1, entropy w p = budgetEntropy (budget i) p) ∧
      ((∀ j k, w j = w k) ↔ i = 0) := by
  obtain ⟨k, hcol⟩ := collision_representative hw
  have he := entropy_eq_of_collisions hcol
  rw [entropy_intProfile, witness_profile k] at he
  refine ⟨templateIndex k, ?_, ?_⟩
  · intro p hp
    rw [he, budget_identity _ p hp]
  · have hsingle (i j : Fin 4) : w i = w j ↔ witness k i = witness k j := by
      have h := hcol (singleMask i) (singleMask j)
      simp only [weighted_single] at h
      exact_mod_cast h
    exact (show (∀ i j, w i = w j) ↔ ∀ i j, witness k i = witness k j from
      ⟨fun h i j => (hsingle i j).mp (h i j), fun h i j => (hsingle i j).mpr (h i j)⟩).trans
        (witness_all_equal k)

private theorem curvature_of_template {w : Fin 4 → ℝ} {i : Fin 23}
    (he : ∀ p ∈ Ioo (0 : ℝ) 1, entropy w p = budgetEntropy (budget i) p)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    deriv (deriv (entropy w)) p = budgetCurvature (budget i) p := by
  have hloc : entropy w =ᶠ[𝓝 p] budgetEntropy (budget i) :=
    Filter.Eventually.mono
      (show ∀ᶠ x in 𝓝 p, x ∈ Ioo (0 : ℝ) 1 from Ioo_mem_nhds hp.1 hp.2)
      he
  exact hloc.deriv.deriv_eq.trans (deriv2_budgetEntropy (budget i) hp)

/-- At fixed positive weights, the entropy's curvature has a unique maximum at the midpoint. -/
theorem curvature_lt_midpoint {w : Fin 4 → ℝ} (hw : ∀ i, 0 < w i)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (hne : p ≠ 1/2) :
    deriv (deriv (entropy w)) p < deriv (deriv (entropy w)) (1/2 : ℝ) := by
  obtain ⟨i, he, _⟩ := entropy_template hw
  have hc : (1/2 : ℝ) ∈ Ioo 0 1 := by norm_num
  rw [curvature_of_template he hp, curvature_of_template he hc]
  exact budgetCurvature_lt_midpoint i hp hne

/-- The sharp upper bound on the second derivative of the four-weight Shannon entropy. -/
theorem sharp_curvature_bound {w : Fin 4 → ℝ} (hw : ∀ i, 0 < w i)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    deriv (deriv (entropy w)) p ≤ -16 + 6 * Real.log 6 := by
  obtain ⟨i, he, _⟩ := entropy_template hw
  have hc : (1/2 : ℝ) ∈ Ioo 0 1 := by norm_num
  have hmid : deriv (deriv (entropy w)) (1/2 : ℝ) ≤ -16 + 6 * Real.log 6 := by
    rw [curvature_of_template he hc, budgetCurvature_midpoint]
    by_cases hi : i = 0
    · rw [hi, budget_K_equal]
    · linarith [budget_K_lt i hi]
  by_cases hp' : p = 1/2
  · simpa [hp'] using hmid
  · exact (curvature_lt_midpoint hw hp hp').le.trans hmid

/-- Equality holds exactly for equal weights and the common parameter one half. -/
theorem sharp_curvature_equality_iff {w : Fin 4 → ℝ} (hw : ∀ i, 0 < w i)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    (deriv (deriv (entropy w)) p = -16 + 6 * Real.log 6) ↔
      ((∀ i j, w i = w j) ∧ p = 1/2) := by
  have hc : (1/2 : ℝ) ∈ Ioo 0 1 := by norm_num
  constructor
  · intro h
    have hmid : p = 1/2 := by
      by_contra hne
      exact ((curvature_lt_midpoint hw hp hne).trans_le (sharp_curvature_bound hw hc)).ne h
    subst p
    obtain ⟨i, he, hi⟩ := entropy_template hw
    rw [curvature_of_template he hc, budgetCurvature_midpoint] at h
    have hi0 : i = 0 := by
      by_contra hne
      linarith [budget_K_lt i hne]
    exact ⟨hi.mpr hi0, rfl⟩
  · rintro ⟨hw_eq, rfl⟩
    have heq : w = fun _ => w 0 := funext fun i => hw_eq i 0
    rw [heq]
    exact equalWeight_midpoint_curvature (hw 0)

/-- Strict concavity includes the endpoints by continuity. -/
theorem entropy_strictConcave {w : Fin 4 → ℝ} (hw : ∀ i, 0 < w i) :
    StrictConcaveOn ℝ (Icc (0 : ℝ) 1) (entropy w) := by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc 0 1) (continuous_entropy w).continuousOn
  intro p hp
  rw [interior_Icc] at hp
  exact (sharp_curvature_bound hw hp).trans_lt sharp_curvature_negative

end Bernoulli4
