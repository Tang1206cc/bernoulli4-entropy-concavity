module

public import Bernoulli4.Entropy
public import Bernoulli4.Rows

import Mathlib.Tactic.NormNum

@[expose] public section

/-! A computable multiset of cardinality counts for integer representatives. -/

namespace Bernoulli4

open scoped BigOperators

abbrev Profile := Fin 5 → ℕ

def intWeightedSum (w : Fin 4 → ℤ) (m : Outcome) : ℤ :=
  ∑ i ∈ selected m, w i

theorem weightedSum_cast (w : Fin 4 → ℤ) (m : Outcome) :
    weightedSum (fun j => (w j : ℝ)) m = (intWeightedSum w m : ℝ) := by
  simp [weightedSum, intWeightedSum, Int.cast_sum]

def intSupport (w : Fin 4 → ℤ) : Finset ℤ :=
  Finset.univ.image (intWeightedSum w)

def profileAt (w : Fin 4 → ℤ) (s : ℤ) : Profile :=
  fun k => ((Finset.univ.filter (fun m => intWeightedSum w m = s)).filter
    (fun m => cardinality m = k)).card

def profiles (w : Fin 4 → ℤ) : Multiset Profile :=
  (intSupport w).val.map (profileAt w)

noncomputable def profilePoly (v : Profile) : Polynomial ℝ :=
  ∑ k : Fin 5, Polynomial.C (v k : ℝ) * atomPoly k

noncomputable def profileEntropy (profiles : Multiset Profile) (p : ℝ) : ℝ :=
  (profiles.map (fun v => Real.negMulLog ((profilePoly v).eval p))).sum

theorem support_int (w : Fin 4 → ℤ) :
    support (fun j => (w j : ℝ)) = (intSupport w).image (fun (s : ℤ) => (s : ℝ)) := by
  classical
  unfold support intSupport
  rw [Finset.image_image]
  congr 1
  funext m
  exact weightedSum_cast w m

theorem massPoly_int (w : Fin 4 → ℤ) (s : ℤ) :
    massPoly (fun j => (w j : ℝ)) (s : ℝ) = profilePoly (profileAt w s) := by
  classical
  have hf : (Finset.univ.filter (fun m => weightedSum (fun j => (w j : ℝ)) m = (s : ℝ))) =
      Finset.univ.filter (fun m => intWeightedSum w m = s) := by
    ext m
    simp [weightedSum_cast]
  unfold massPoly profilePoly
  rw [hf, ← Finset.sum_fiberwise (Finset.univ.filter (fun m => intWeightedSum w m = s))
    cardinality (fun m => atomPoly (cardinality m))]
  apply Finset.sum_congr rfl
  intro k _
  have h : ∀ m ∈ (Finset.univ.filter (fun j => intWeightedSum w j = s)).filter
      (fun j => cardinality j = k), atomPoly (cardinality m) = atomPoly k :=
    fun m hm => congrArg atomPoly (Finset.mem_filter.mp hm).2
  rw [Finset.sum_congr rfl h, Finset.sum_const]
  simp [profileAt, nsmul_eq_mul]

theorem entropy_intProfile (w : Fin 4 → ℤ) :
    entropy (fun j => (w j : ℝ)) = profileEntropy (profiles w) := by
  classical
  funext p
  unfold entropy
  rw [support_int, Finset.sum_image (Int.cast_injective (α := ℝ)).injOn]
  simp_rw [massPoly_int]
  unfold profileEntropy profiles
  rw [Multiset.map_map]
  rfl

end Bernoulli4
