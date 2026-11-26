module

public import Bernoulli4.Entropy
public import Bernoulli4.Rows

import Mathlib.Tactic.Ring

@[expose] public section

/-! An exact certificate for coverage of the mixed-sign equalities. -/

namespace Bernoulli4

open scoped BigOperators

abbrev Row := Fin 4 → ℤ
abbrev NormalIndex := Fin 25
abbrev Coefficients := List (ℤ × NormalIndex)

def rowValue (r : Row) (w : Fin 4 → ℝ) : ℝ :=
  ∑ j, (r j : ℝ) * w j

def intRowValue (r w : Row) : ℤ :=
  ∑ j, r j * w j

def combinedRow : Coefficients → Row
  | [] => fun _ => 0
  | (z, i) :: terms => fun j => z * normal i j + combinedRow terms j

private theorem rowValue_add (r s : Row) (w : Fin 4 → ℝ) :
    rowValue (fun j => r j + s j) w = rowValue r w + rowValue s w := by
  simp [rowValue, add_mul, Finset.sum_add_distrib]

private theorem rowValue_scale (z : ℤ) (r : Row) (w : Fin 4 → ℝ) :
    rowValue (fun j => z * r j) w = (z : ℝ) * rowValue r w := by
  simp only [rowValue, Int.cast_mul, Finset.mul_sum, mul_assoc]

theorem rowValue_pos {r : Row} {w : Fin 4 → ℝ} (hw : ∀ j, 0 < w j)
    (hn : ∀ j, 0 ≤ r j) (hp : ∃ j, 0 < r j) : 0 < rowValue r w := by
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (by exact_mod_cast hn j) (hw j).le
  · obtain ⟨j, hj⟩ := hp
    exact ⟨j, Finset.mem_univ _, mul_pos (Int.cast_pos.mpr hj) (hw j)⟩

private theorem combinedRow_zero {w : Fin 4 → ℝ} {terms : Coefficients}
    (h : ∀ t ∈ terms, rowValue (normal t.2) w = 0) : rowValue (combinedRow terms) w = 0 := by
  induction terms with
  | nil => simp [combinedRow, rowValue]
  | cons t terms ih =>
    rcases t with ⟨z, i⟩
    have hi : rowValue (normal i) w = 0 := h (z, i) (by simp)
    rw [combinedRow, rowValue_add, rowValue_scale, hi, mul_zero, zero_add]
    exact ih fun t ht => h t (List.mem_cons_of_mem _ ht)

inductive CaseTree where
  | split (i : NormalIndex) (zero nonzero : CaseTree)
  | imply (i : NormalIndex) (scale : ℤ) (terms : Coefficients) (rest : CaseTree)
  | exclude (terms : Coefficients)
  | conflict (i : NormalIndex) (scale : ℤ) (terms : Coefficients)
  | accept (index : Fin 216)

def known (zeros : List NormalIndex) (terms : Coefficients) : Bool :=
  terms.all fun t => decide (t.2 ∈ zeros)

def gives (i : NormalIndex) (scale : ℤ) (terms : Coefficients) : Bool :=
  decide (scale ≠ 0 ∧ ∀ j, combinedRow terms j = scale * normal i j)

def accepts (k : Fin 216) (zeros nonzeros : List NormalIndex) : Bool :=
  (List.finRange 25).all fun i =>
    if intRowValue (normal i) (witness k) = 0 then decide (i ∈ zeros) else decide (i ∈ nonzeros)

def CaseTree.check (tree : CaseTree) (zeros nonzeros : List NormalIndex) : Bool :=
  match tree with
  | .split i yes no => yes.check (i :: zeros) nonzeros && no.check zeros (i :: nonzeros)
  | .imply i scale terms rest =>
    known zeros terms && gives i scale terms && rest.check (i :: zeros) nonzeros
  | .exclude terms =>
    known zeros terms &&
      decide ((∀ j, 0 ≤ combinedRow terms j) ∧ (∃ j, 0 < combinedRow terms j))
  | .conflict i scale terms =>
    known zeros terms && gives i scale terms && decide (i ∈ nonzeros)
  | .accept k => accepts k zeros nonzeros

theorem CaseTree.checked_split {i : NormalIndex} {yes no : CaseTree}
    {zeros nonzeros : List NormalIndex}
    (hy : yes.check (i :: zeros) nonzeros = true) (hn : no.check zeros (i :: nonzeros) = true) :
    (CaseTree.split i yes no).check zeros nonzeros = true :=
  Bool.and_eq_true_iff.mpr ⟨hy, hn⟩

theorem CaseTree.checked_imply {i : NormalIndex} {scale : ℤ} {terms : Coefficients}
    {rest : CaseTree} {zeros nonzeros : List NormalIndex}
    (hk : known zeros terms = true) (hg : gives i scale terms = true)
    (hr : rest.check (i :: zeros) nonzeros = true) :
    (CaseTree.imply i scale terms rest).check zeros nonzeros = true :=
  Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨hk, hg⟩, hr⟩

private theorem zero_of_known {w : Fin 4 → ℝ} {zeros : List NormalIndex}
    (hz : ∀ i ∈ zeros, rowValue (normal i) w = 0) {terms : Coefficients}
    (hk : known zeros terms = true) : rowValue (combinedRow terms) w = 0 := by
  apply combinedRow_zero
  intro t ht
  rw [known, List.all_eq_true] at hk
  exact hz _ (of_decide_eq_true (hk t ht))

private theorem zero_of_gives {w : Fin 4 → ℝ} {i : NormalIndex} {scale : ℤ}
    {terms : Coefficients} (hg : gives i scale terms = true)
    (hzero : rowValue (combinedRow terms) w = 0) : rowValue (normal i) w = 0 := by
  have hcert : scale ≠ 0 ∧ ∀ j, combinedRow terms j = scale * normal i j :=
    of_decide_eq_true hg
  obtain ⟨hn, he⟩ := hcert
  rw [show combinedRow terms = fun j => scale * normal i j from funext he,
    rowValue_scale] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (Int.cast_ne_zero.mpr hn)

attribute [local irreducible] normal witness rowValue intRowValue combinedRow

set_option maxHeartbeats 400000
set_option maxRecDepth 4096

theorem CaseTree.sound (tree : CaseTree) {w : Fin 4 → ℝ} (hw : ∀ j, 0 < w j) :
    ∀ zeros nonzeros : List NormalIndex,
      tree.check zeros nonzeros = true →
      (∀ i ∈ zeros, rowValue (normal i) w = 0) →
      (∀ i ∈ nonzeros, rowValue (normal i) w ≠ 0) →
      ∃ k : Fin 216, ∀ i : NormalIndex,
        rowValue (normal i) w = 0 ↔ intRowValue (normal i) (witness k) = 0 := by
  induction tree with
  | split i yes no ihYes ihNo =>
    intro zeros nonzeros hcheck hz hn
    change (yes.check (i :: zeros) nonzeros && no.check zeros (i :: nonzeros)) = true at hcheck
    obtain ⟨hy, hf⟩ := Bool.and_eq_true_iff.mp hcheck
    by_cases hi : rowValue (normal i) w = 0
    · apply ihYes (i :: zeros) nonzeros hy _ hn
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hi
      · exact hz j hj
    · apply ihNo zeros (i :: nonzeros) hf hz
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hi
      · exact hn j hj
  | imply i scale terms rest ih =>
    intro zeros nonzeros hcheck hz hn
    change (known zeros terms && gives i scale terms && rest.check (i :: zeros) nonzeros) =
        true at hcheck
    obtain ⟨hknown, hrest⟩ := Bool.and_eq_true_iff.mp hcheck
    obtain ⟨hk, hg⟩ := Bool.and_eq_true_iff.mp hknown
    have hi := zero_of_gives hg (zero_of_known hz hk)
    apply ih (i :: zeros) nonzeros hrest _ hn
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hi
    · exact hz j hj
  | exclude terms =>
    intro zeros nonzeros hcheck hz _
    change (known zeros terms &&
      decide ((∀ j, 0 ≤ combinedRow terms j) ∧ (∃ j, 0 < combinedRow terms j))) =
        true at hcheck
    obtain ⟨hk, hrow⟩ := Bool.and_eq_true_iff.mp hcheck
    have hr : (∀ j, 0 ≤ combinedRow terms j) ∧ (∃ j, 0 < combinedRow terms j) :=
      of_decide_eq_true hrow
    exact False.elim ((rowValue_pos hw hr.1 hr.2).ne' (zero_of_known hz hk))
  | conflict i scale terms =>
    intro zeros nonzeros hcheck hz hn
    change (known zeros terms && gives i scale terms && decide (i ∈ nonzeros)) =
        true at hcheck
    obtain ⟨hknown, hi⟩ := Bool.and_eq_true_iff.mp hcheck
    obtain ⟨hk, hg⟩ := Bool.and_eq_true_iff.mp hknown
    exact False.elim (hn i (of_decide_eq_true hi) (zero_of_gives hg (zero_of_known hz hk)))
  | accept k =>
    intro zeros nonzeros hcheck hz hn
    change accepts k zeros nonzeros = true at hcheck
    rw [accepts, List.all_eq_true] at hcheck
    refine ⟨k, fun i => ?_⟩
    have hi := hcheck i (List.mem_finRange i)
    by_cases h : intRowValue (normal i) (witness k) = 0
    · rw [ite_eq_left h] at hi
      exact iff_of_true (hz i (of_decide_eq_true hi)) h
    · rw [ite_eq_right h] at hi
      exact iff_of_false (hn i (of_decide_eq_true hi)) h

end Bernoulli4
