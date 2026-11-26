module

public import Bernoulli4.CaseData


@[expose] public section

/-! Every positive real weight vector has a certified representative with the same collisions. -/

namespace Bernoulli4

open scoped BigOperators

def differenceRow (m n : Outcome) : Row :=
  fun i => (if m.val.testBit i.val then 1 else 0) - (if n.val.testBit i.val then 1 else 0)

private def rowShape (r : Row) : Prop :=
  (∀ i, r i = 0) ∨
    ((∀ i, 0 ≤ r i) ∧ (∃ i, 0 < r i)) ∨
    ((∀ i, r i ≤ 0) ∧ (∃ i, r i < 0)) ∨
    (∃ i : NormalIndex, (∀ j, r j = normal i j) ∨ (∀ j, r j = -normal i j))

private instance (r : Row) : Decidable (rowShape r) := by
  unfold rowShape
  infer_instance

set_option maxHeartbeats 2000000 in
private theorem covered_pair : ∀ m n : Outcome, rowShape (differenceRow m n) := by
  decide +kernel

private theorem val_difference (w : Fin 4 → ℝ) (m n : Outcome) :
    rowValue (differenceRow m n) w = weightedSum w m - weightedSum w n := by
  classical
  simp only [rowValue, differenceRow, weightedSum, selected, Finset.sum_filter,
    ← Finset.sum_sub_distrib, Int.cast_sub, sub_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  split <;> split <;> simp_all

private theorem rowValue_neg (w : Fin 4 → ℝ) (r : Row) :
    rowValue (fun j => -r j) w = -rowValue r w := by
  simp [rowValue, neg_mul, Finset.sum_neg_distrib]

private theorem rowValue_cast (r v : Row) :
    rowValue r (fun j => (v j : ℝ)) = (intRowValue r v : ℝ) := by
  simp [rowValue, intRowValue, Int.cast_sum]

private theorem witness_pos (k : Fin 216) (i : Fin 4) : 0 < witness k i := by
  revert k i
  decide +kernel

/-- The labeled equality relation of any real positive weights occurs among the finite witnesses. -/
theorem collision_representative {w : Fin 4 → ℝ} (hw : ∀ j, 0 < w j) :
    ∃ k : Fin 216, ∀ m n : Outcome,
      weightedSum w m = weightedSum w n ↔
        weightedSum (fun j => (witness k j : ℝ)) m =
          weightedSum (fun j => (witness k j : ℝ)) n := by
  obtain ⟨k, hk⟩ := CaseTree.sound caseData hw [] [] caseData_checked (by simp) (by simp)
  let v : Fin 4 → ℝ := fun j => (witness k j : ℝ)
  have hv : ∀ j, 0 < v j := fun j => Int.cast_pos.mpr (witness_pos k j)
  refine ⟨k, fun m n => ?_⟩
  change weightedSum w m = weightedSum w n ↔ weightedSum v m = weightedSum v n
  have to_form (u : Fin 4 → ℝ) :
      weightedSum u m = weightedSum u n ↔ rowValue (differenceRow m n) u = 0 := by
    rw [val_difference]
    exact sub_eq_zero.symm
  rw [to_form w, to_form v]
  rcases covered_pair m n with h | h | h | ⟨i, h | h⟩
  · simp [show differenceRow m n = fun _ => 0 from funext h, rowValue]
  · have hwpos := rowValue_pos hw h.1 h.2
    have hvpos := rowValue_pos hv h.1 h.2
    simp [hwpos.ne', hvpos.ne']
  · have hpos (z : Fin 4 → ℝ) (hz : ∀ j, 0 < z j) :
        0 < rowValue (fun j => -differenceRow m n j) z :=
      rowValue_pos hz (fun j => neg_nonneg.mpr (h.1 j)) (by
        obtain ⟨j, hj⟩ := h.2
        exact ⟨j, neg_pos.mpr hj⟩)
    have hwneg := hpos w hw
    have hvneg := hpos v hv
    rw [rowValue_neg] at hwneg hvneg
    simp [(neg_pos.mp hwneg).ne, (neg_pos.mp hvneg).ne]
  · rw [show differenceRow m n = normal i from funext h]
    simpa only [v, rowValue_cast, Int.cast_eq_zero] using hk i
  · rw [show differenceRow m n = fun j => -normal i j from funext h,
      rowValue_neg w (normal i), rowValue_neg v (normal i)]
    simpa only [neg_eq_zero, v, rowValue_cast, Int.cast_eq_zero] using hk i

/-- Entropy of a weighted sum depends only on the labeled collision relation. -/
theorem entropy_eq_of_collisions {w v : Fin 4 → ℝ}
    (h : ∀ m n : Outcome,
      weightedSum w m = weightedSum w n ↔ weightedSum v m = weightedSum v n) :
    entropy w = entropy v := by
  classical
  have chooseRep (s : ℝ) (hs : s ∈ support w) :
      ∃ m : Outcome, weightedSum w m = s := by
    obtain ⟨m, _, hm⟩ := Finset.mem_image.mp hs
    exact ⟨m, hm⟩
  let rep (s : ℝ) (hs : s ∈ support w) := Classical.choose (chooseRep s hs)
  have rep_eq (s : ℝ) (hs : s ∈ support w) : weightedSum w (rep s hs) = s :=
    Classical.choose_spec (chooseRep s hs)
  funext p
  unfold entropy
  refine Finset.sum_bij (fun s hs => weightedSum v (rep s hs)) ?_ ?_ ?_ ?_
  · intro s hs
    exact Finset.mem_image.mpr ⟨rep s hs, Finset.mem_univ _, rfl⟩
  · intro a ha b hb hab
    simpa only [rep_eq] using (h (rep a ha) (rep b hb)).mpr hab
  · intro b hb
    obtain ⟨m, _, hm⟩ := Finset.mem_image.mp hb
    let a := weightedSum w m
    have ha : a ∈ support w := Finset.mem_image.mpr ⟨m, Finset.mem_univ _, rfl⟩
    exact ⟨a, ha, ((h (rep a ha) m).mp (rep_eq a ha)).trans hm⟩
  · intro a ha
    congr 2
    unfold massPoly
    apply Finset.sum_congr
    · ext m
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← h m (rep a ha), rep_eq a ha]
    · intro _ _
      rfl

/-- A finite representative gives exactly the same entropy as a given positive real vector. -/
theorem entropy_representative {w : Fin 4 → ℝ} (hw : ∀ j, 0 < w j) :
    ∃ k : Fin 216, entropy w = entropy (fun j => (witness k j : ℝ)) := by
  obtain ⟨k, hk⟩ := collision_representative hw
  exact ⟨k, entropy_eq_of_collisions hk⟩

end Bernoulli4
