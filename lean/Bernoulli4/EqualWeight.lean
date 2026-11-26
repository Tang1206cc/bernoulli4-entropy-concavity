module

public import Bernoulli4.Curvature
public import Mathlib.Data.Fin.VecNotation

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! The bound is attained at the midpoint by any positive equal weights. -/

namespace Bernoulli4

open scoped BigOperators
open Set

private def fiber (k : Fin 5) : Finset Outcome :=
  Finset.univ.filter fun m => cardinality m = k

private theorem fiber_card (k : Fin 5) : (fiber k).card = Nat.choose 4 k.val := by
  revert k
  decide +kernel

private theorem fiber_nonempty (k : Fin 5) : (fiber k).Nonempty := by
  revert k
  decide +kernel

private theorem constant_weightedSum (a : ℝ) (m : Outcome) :
    weightedSum (fun _ => a) m = (cardinality m).val * a := by
  simp [weightedSum, cardinality, nsmul_eq_mul]

private theorem support_const (a : ℝ) :
    support (fun _ => a) = Finset.univ.image (fun k : Fin 5 => (k.val : ℝ) * a) := by
  classical
  ext s
  simp only [support, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨cardinality m, (constant_weightedSum a m).symm⟩
  · rintro ⟨k, rfl⟩
    obtain ⟨m, hm⟩ := fiber_nonempty k
    have hmk := (Finset.mem_filter.mp hm).2
    exact ⟨m, by rw [constant_weightedSum, hmk]⟩

private theorem const_fiber {a : ℝ} (ha : 0 < a) (k : Fin 5) :
    (Finset.univ.filter fun m => weightedSum (fun _ => a) m = (k.val : ℝ) * a) =
      fiber k := by
  ext m
  simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and, constant_weightedSum]
  constructor
  · intro hm
    apply Fin.ext
    exact_mod_cast mul_right_cancel₀ ha.ne' hm
  · intro hm
    rw [hm]

private noncomputable def binomialPoly (k : Fin 5) : Polynomial ℝ :=
  Polynomial.C (Nat.choose 4 k.val : ℝ) * atomPoly k

private theorem const_massPoly {a : ℝ} (ha : 0 < a) (k : Fin 5) :
    massPoly (fun _ => a) ((k.val : ℝ) * a) = binomialPoly k := by
  classical
  unfold massPoly
  rw [const_fiber ha]
  calc
    ∑ i ∈ fiber k, atomPoly (cardinality i) = ∑ _ ∈ fiber k, atomPoly k :=
      Finset.sum_congr rfl fun _ hi => by rw [(Finset.mem_filter.mp hi).2]
    _ = binomialPoly k := by
      simp [Finset.sum_const, fiber_card, binomialPoly, nsmul_eq_mul]

private theorem support_map_injective {a : ℝ} (ha : 0 < a) :
    Function.Injective (fun k : Fin 5 => (k.val : ℝ) * a) := by
  intro j k h
  apply Fin.ext
  exact_mod_cast mul_right_cancel₀ ha.ne' h

private theorem midpoint_binomial_values (k : Fin 5) :
    (binomialPoly k).eval (1 / 2 : ℝ) = ![(1/16 : ℝ), 1/4, 3/8, 1/4, 1/16] k ∧
    (binomialPoly k).derivative.eval (1 / 2 : ℝ) = ![(-1/2 : ℝ), -1, 0, 1, 1/2] k ∧
    (binomialPoly k).derivative.derivative.eval (1 / 2 : ℝ) = ![(3 : ℝ), 0, -6, 0, 3] k := by
  fin_cases k <;>
    norm_num [binomialPoly, atomPoly, Polynomial.derivative_mul,
      Polynomial.derivative_pow, Polynomial.derivative_sub, Nat.choose]

/-- Sharpness of the uniform curvature bound at equal weights and `p = 1/2`. -/
theorem equalWeight_midpoint_curvature {a : ℝ} (ha : 0 < a) :
    deriv (deriv (entropy (fun _ => a))) (1 / 2 : ℝ) = -16 + 6 * Real.log 6 := by
  classical
  rw [deriv2_entropy (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1), support_const a]
  rw [Finset.sum_image (support_map_injective ha).injOn]
  simp_rw [const_massPoly ha]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change entropyTermCurvature (binomialPoly 0) (1 / 2 : ℝ) +
    (entropyTermCurvature (binomialPoly 1) (1 / 2 : ℝ) +
      (entropyTermCurvature (binomialPoly 2) (1 / 2 : ℝ) +
        (entropyTermCurvature (binomialPoly 3) (1 / 2 : ℝ) +
          entropyTermCurvature (binomialPoly 4) (1 / 2 : ℝ)))) = _
  unfold entropyTermCurvature
  rw [(midpoint_binomial_values 0).1, (midpoint_binomial_values 0).2.1,
    (midpoint_binomial_values 0).2.2, (midpoint_binomial_values 1).1,
    (midpoint_binomial_values 1).2.1, (midpoint_binomial_values 1).2.2,
    (midpoint_binomial_values 2).1, (midpoint_binomial_values 2).2.1,
    (midpoint_binomial_values 2).2.2, (midpoint_binomial_values 3).1,
    (midpoint_binomial_values 3).2.1, (midpoint_binomial_values 3).2.2,
    (midpoint_binomial_values 4).1, (midpoint_binomial_values 4).2.1,
    (midpoint_binomial_values 4).2.2]
  simp
  rw [Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (8 : ℝ) ≠ 0)]
  norm_num
  rw [show (16 : ℝ) = 8 * 2 by norm_num,
    Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
    show (6 : ℝ) = 2 * 3 by norm_num,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)]
  ring

end Bernoulli4
