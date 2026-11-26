module

public import Bernoulli4.Curvature
public import Mathlib.Analysis.Calculus.Deriv.Inv

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

@[expose] public section

/-! Explicit derivative certificates for polynomial multiples of affine logarithms. -/

namespace Bernoulli4

open Polynomial

/-- A pair of polynomials represents a logarithmic term and its rational remainder. -/
abbrev LogJet := Polynomial ℝ × Polynomial ℝ

noncomputable def affinePoly (a b : ℝ) : Polynomial ℝ :=
  C a * X + C b

noncomputable def LogJet.value (j : LogJet) (a b : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  j.1.eval x * Real.log (a * x + b) + j.2.eval x / (a * x + b) ^ n

/-- Differentiate the two polynomial components, increasing the denominator power by one. -/
noncomputable def LogJet.next (j : LogJet) (a b : ℝ) (n : ℕ) : LogJet :=
  let L := affinePoly a b
  (j.1.derivative,
    C a * j.1 * L ^ n + j.2.derivative * L - C ((n : ℝ) * a) * j.2)

theorem affinePoly_eval (a b x : ℝ) : (affinePoly a b).eval x = a * x + b := by
  simp [affinePoly]

theorem LogJet.hasDerivAt_value (j : LogJet) (a b : ℝ) (n : ℕ) {x : ℝ}
    (hx : a * x + b ≠ 0) :
    HasDerivAt (j.value a b n) ((j.next a b n).value a b (n + 1) x) x := by
  have hL : HasDerivAt (fun t : ℝ => a * t + b) a x := by
    simpa using ((hasDerivAt_id x).const_mul a).add_const b
  have h₁ := (j.1.hasDerivAt x).mul (hL.log hx)
  have h₂ := (j.2.hasDerivAt x).div (hL.pow n) (pow_ne_zero n hx)
  convert h₁.add h₂ using 1
  · rfl
  · simp only [LogJet.value, LogJet.next, eval_sub, eval_add, eval_mul, eval_C, eval_pow,
      affinePoly_eval, Pi.pow_apply]
    cases n with
    | zero =>
      simp
      field_simp [hx]
      ring
    | succ n =>
      simp only [Nat.succ_sub_one, Nat.cast_succ, pow_succ]
      field_simp [hx]
      ring

/-- Algebraic data for the `n`th derivative of `P(x) * log (a*x+b)`. -/
noncomputable def logJet (P : Polynomial ℝ) (a b : ℝ) : ℕ → LogJet
  | 0 => (P, 0)
  | n + 1 => (logJet P a b n).next a b n

noncomputable def logPolyDeriv (P : Polynomial ℝ) (a b : ℝ) (n : ℕ) : ℝ → ℝ :=
  (logJet P a b n).value a b n

theorem logPolyDeriv_zero (P : Polynomial ℝ) (a b x : ℝ) :
    logPolyDeriv P a b 0 x = P.eval x * Real.log (a * x + b) := by
  simp [logPolyDeriv, logJet, LogJet.value]

theorem hasDerivAt_logPolyDeriv (P : Polynomial ℝ) (a b : ℝ) (n : ℕ) {x : ℝ}
    (hx : a * x + b ≠ 0) :
    HasDerivAt (logPolyDeriv P a b n) (logPolyDeriv P a b (n + 1) x) x :=
  (logJet P a b n).hasDerivAt_value a b n hx

end Bernoulli4
