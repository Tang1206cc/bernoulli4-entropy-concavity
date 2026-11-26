module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Topology.Algebra.Polynomial

@[expose] public section

/-! The Shannon entropy of the weighted sum of four Bernoulli variables. -/

namespace Bernoulli4

open scoped BigOperators

/-- The sixteen outcomes, encoded as four-bit masks. -/
abbrev Outcome := Fin 16

/-- The coordinates whose Bernoulli value is one. -/
def selected (m : Outcome) : Finset (Fin 4) :=
  Finset.univ.filter fun i => m.val.testBit i.val

/-- The number of ones in the outcome. -/
def cardinality (m : Outcome) : Fin 5 :=
  ⟨(selected m).card, Nat.lt_succ_of_le (by
    simpa using (Finset.card_le_univ (selected m)))⟩

/-- The weighted value of one outcome. -/
def weightedSum (w : Fin 4 → ℝ) (m : Outcome) : ℝ :=
  ∑ i ∈ selected m, w i

/-- The exact mass of an outcome with `k` ones as a polynomial in `p`. -/
noncomputable def atomPoly (k : Fin 5) : Polynomial ℝ :=
  Polynomial.X ^ k.val * (1 - Polynomial.X) ^ (4 - k.val)

theorem atomPoly_eval (k : Fin 5) (p : ℝ) :
    (atomPoly k).eval p = p ^ k.val * (1 - p) ^ (4 - k.val) := by
  simp [atomPoly]

/-- The finite support consists of distinct weighted values. -/
noncomputable def support (w : Fin 4 → ℝ) : Finset ℝ := by
  classical
  exact Finset.univ.image (weightedSum w)

/-- Every outcome with weighted value `s` contributes its mass to one atom. -/
noncomputable def massPoly (w : Fin 4 → ℝ) (s : ℝ) : Polynomial ℝ := by
  classical
  exact ∑ m ∈ Finset.univ.filter (fun m => weightedSum w m = s), atomPoly (cardinality m)

/-- Shannon entropy with natural logarithms and the continuous value at zero. -/
noncomputable def entropy (w : Fin 4 → ℝ) (p : ℝ) : ℝ :=
  ∑ s ∈ support w, Real.negMulLog ((massPoly w s).eval p)

theorem continuous_entropy (w : Fin 4 → ℝ) : Continuous (entropy w) := by
  unfold entropy
  exact continuous_finsetSum _ fun s _ =>
    Real.continuous_negMulLog.comp (massPoly w s).continuous

theorem mass_pos {w : Fin 4 → ℝ} {s p : ℝ} (hs : s ∈ support w)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) : 0 < (massPoly w s).eval p := by
  classical
  obtain ⟨m, _, hm⟩ := Finset.mem_image.mp hs
  simp only [massPoly, Polynomial.eval_finsetSum, atomPoly_eval]
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (pow_nonneg hp.1.le _) (pow_nonneg (sub_nonneg.mpr hp.2.le) _)
  · exact ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩,
      mul_pos (pow_pos hp.1 _) (pow_pos (sub_pos.mpr hp.2) _)⟩

end Bernoulli4
