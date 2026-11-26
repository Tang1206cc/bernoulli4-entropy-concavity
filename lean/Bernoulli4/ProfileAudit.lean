module

public import Bernoulli4.ProfileData

import Mathlib.Tactic.FinCases

@[expose] public section

/-! The kernel verifies every representative's entropy template. -/

namespace Bernoulli4

private def witnessAt (group : Fin 18) (offset : Fin 12) : Fin 216 :=
  ⟨group.val * 12 + offset.val, by omega⟩

private def profileMatches (k : Fin 216) : Prop :=
  profiles (witness k) = template (templateIndex k)

private instance (k : Fin 216) : Decidable (profileMatches k) := by
  unfold profileMatches
  infer_instance

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
private theorem profile_group_0 : ∀ j : Fin 12, profileMatches (witnessAt 0 j) := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
private theorem profile_group_1 : ∀ j : Fin 12, profileMatches (witnessAt 1 j) := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
private theorem profile_group_2 : ∀ j : Fin 12, profileMatches (witnessAt 2 j) := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
private theorem profile_group_3 : ∀ j : Fin 12, profileMatches (witnessAt 3 j) := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
private theorem profile_group_4 : ∀ j : Fin 12, profileMatches (witnessAt 4 j) := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
private theorem profile_group_5 : ∀ j : Fin 12, profileMatches (witnessAt 5 j) := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
private theorem profile_group_6 : ∀ j : Fin 12, profileMatches (witnessAt 6 j) := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
private theorem profile_group_7 : ∀ j : Fin 12, profileMatches (witnessAt 7 j) := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
private theorem profile_group_8 : ∀ j : Fin 12, profileMatches (witnessAt 8 j) := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
private theorem profile_group_9 : ∀ j : Fin 12, profileMatches (witnessAt 9 j) := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
private theorem profile_group_10 : ∀ j : Fin 12, profileMatches (witnessAt 10 j) := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
private theorem profile_group_11 : ∀ j : Fin 12, profileMatches (witnessAt 11 j) := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
private theorem profile_group_12 : ∀ j : Fin 12, profileMatches (witnessAt 12 j) := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
private theorem profile_group_13 : ∀ j : Fin 12, profileMatches (witnessAt 13 j) := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
private theorem profile_group_14 : ∀ j : Fin 12, profileMatches (witnessAt 14 j) := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
private theorem profile_group_15 : ∀ j : Fin 12, profileMatches (witnessAt 15 j) := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
private theorem profile_group_16 : ∀ j : Fin 12, profileMatches (witnessAt 16 j) := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
private theorem profile_group_17 : ∀ j : Fin 12, profileMatches (witnessAt 17 j) := by
  decide +kernel

theorem witness_profile (k : Fin 216) :
    profiles (witness k) = template (templateIndex k) := by
  have h (i : Fin 18) (j : Fin 12) : profileMatches (witnessAt i j) := by
    fin_cases i
    · exact profile_group_0 j
    · exact profile_group_1 j
    · exact profile_group_2 j
    · exact profile_group_3 j
    · exact profile_group_4 j
    · exact profile_group_5 j
    · exact profile_group_6 j
    · exact profile_group_7 j
    · exact profile_group_8 j
    · exact profile_group_9 j
    · exact profile_group_10 j
    · exact profile_group_11 j
    · exact profile_group_12 j
    · exact profile_group_13 j
    · exact profile_group_14 j
    · exact profile_group_15 j
    · exact profile_group_16 j
    · exact profile_group_17 j
  let i : Fin 18 := ⟨k.val / 12, by omega⟩
  let j : Fin 12 := ⟨k.val % 12, Nat.mod_lt _ (by decide)⟩
  have heq : witnessAt i j = k := by
    apply Fin.ext
    dsimp [witnessAt, i, j]
    omega
  exact heq ▸ h i j

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem template_injective : ∀ i j : Fin 23, template i = template j → i = j := by
  decide +kernel

set_option maxRecDepth 16384 in
theorem templateIndex_surjective : ∀ i : Fin 23, ∃ k : Fin 216, templateIndex k = i := by
  decide +kernel

set_option maxRecDepth 16384 in
theorem witness_all_equal : ∀ k : Fin 216,
    (∀ i j : Fin 4, witness k i = witness k j) ↔ templateIndex k = 0 := by
  decide +kernel

end Bernoulli4
