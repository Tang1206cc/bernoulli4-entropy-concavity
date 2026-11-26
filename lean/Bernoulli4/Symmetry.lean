module

public import Bernoulli4.SharpCurvature

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! Symmetry and the unique maximizer of the entropy. -/

namespace Bernoulli4

open Set

open scoped BigOperators

private def complement (m : Outcome) : Outcome :=
  ⟨15 - m.val, by omega⟩

private theorem complement_complement (m : Outcome) : complement (complement m) = m := by
  revert m
  decide +kernel

private theorem selected_complement (m : Outcome) :
    selected (complement m) = Finset.univ \ selected m := by
  revert m
  decide +kernel

private theorem cardinality_complement (m : Outcome) :
    (cardinality (complement m)).val = 4 - (cardinality m).val := by
  revert m
  decide +kernel

private def totalWeight (w : Fin 4 → ℝ) : ℝ :=
  ∑ i, w i

private theorem weightedSum_complement (w : Fin 4 → ℝ) (m : Outcome) :
    weightedSum w (complement m) = totalWeight w - weightedSum w m := by
  unfold weightedSum totalWeight
  rw [selected_complement, eq_sub_iff_add_eq]
  exact Finset.sum_sdiff (Finset.subset_univ (selected m))

private theorem complement_mem_support (w : Fin 4 → ℝ) {s : ℝ} (hs : s ∈ support w) :
    totalWeight w - s ∈ support w := by
  classical
  obtain ⟨m, _, hm⟩ := Finset.mem_image.mp hs
  exact Finset.mem_image.mpr ⟨complement m, Finset.mem_univ _,
    (weightedSum_complement w m).trans (congrArg (fun t => totalWeight w - t) hm)⟩

private theorem atom_eval_complement (m : Outcome) (p : ℝ) :
    (atomPoly (cardinality m)).eval (1-p) =
      (atomPoly (cardinality (complement m))).eval p := by
  simp only [atomPoly_eval, cardinality_complement, sub_sub_cancel]
  have hk : 4 - (4 - (cardinality m).val) = (cardinality m).val := by
    have hb := (cardinality m).isLt
    omega
  rw [hk, mul_comm]

private theorem mass_eval_complement (w : Fin 4 → ℝ) (s p : ℝ) :
    (massPoly w s).eval (1-p) = (massPoly w (totalWeight w - s)).eval p := by
  classical
  simp only [massPoly, Polynomial.eval_finsetSum]
  refine Finset.sum_bij (fun m _ => complement m) ?_ ?_ ?_ ?_
  · intro m hm
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      rw [weightedSum_complement, (Finset.mem_filter.mp hm).2]⟩
  · intro m _ n _ h
    simpa only [complement_complement] using congrArg complement h
  · intro n hn
    refine ⟨complement n, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
      complement_complement n⟩
    rw [weightedSum_complement, (Finset.mem_filter.mp hn).2, sub_sub_cancel]
  · intro m _
    exact atom_eval_complement m p

/-- Complementing each of the four bits reflects the weighted value and preserves entropy. -/
theorem entropy_symm (w : Fin 4 → ℝ) (p : ℝ) : entropy w (1-p) = entropy w p := by
  classical
  unfold entropy
  refine Finset.sum_bij (fun s _ => totalWeight w - s) ?_ ?_ ?_ ?_
  · intro s hs
    exact complement_mem_support w hs
  · intro s _ t _ h
    linarith only [h]
  · intro t ht
    exact ⟨totalWeight w - t, complement_mem_support w ht, sub_sub_cancel _ _⟩
  · intro s _
    exact congrArg Real.negMulLog (mass_eval_complement w s p)

/-- The entropy is uniquely maximized at the common parameter one half. -/
theorem entropy_lt_midpoint {w : Fin 4 → ℝ} (hw : ∀ i, 0 < w i)
    {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hne : p ≠ 1/2) :
    entropy w p < entropy w (1/2 : ℝ) := by
  have hp' : 1-p ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hp.2], by linarith [hp.1]⟩
  have hpp : p ≠ 1-p := fun h => hne (by linarith)
  have h := (entropy_strictConcave hw).2 hp hp' hpp
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (0 : ℝ) < 1/2)
    (by norm_num : (1/2 : ℝ) + 1/2 = 1)
  rw [entropy_symm w p] at h
  simp only [smul_eq_mul] at h
  have hm : (1/2 : ℝ)*p + (1/2 : ℝ)*(1-p) = 1/2 := by ring
  rw [hm] at h
  linarith only [h]

end Bernoulli4
