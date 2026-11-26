module

public import Bernoulli4.LogPolynomial
public import Bernoulli4.QuadraticGrowth

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

/-! Curvature estimates for the mixed singleton–doubleton losses. -/

namespace Bernoulli4

open Polynomial Set Filter
open scoped Topology

/-- The mixed loss and its successive derivatives, expressed as sums of log-polynomial terms. -/
noncomputable def mixedLossJet (a b : ℝ) (n : ℕ) (p : ℝ) : ℝ :=
  logPolyDeriv (X * (1-X)^2 * affinePoly (b-a) a) (b-a) a n p +
  logPolyDeriv (X^2 * (1-X) * affinePoly (a-b) b) (a-b) b n p -
  logPolyDeriv (C b * X^2 * (1-X)^2 + C a * X^3 * (1-X)) 1 0 n p -
  logPolyDeriv (C a * X * (1-X)^3 + C b * X^2 * (1-X)^2) (-1) 1 n p

noncomputable def mixedLoss (a b : ℝ) : ℝ → ℝ :=
  mixedLossJet a b 0

theorem mixedLoss_formula (a b p : ℝ) :
    mixedLoss a b p =
      p * (1-p)^2 * ((a*(1-p)+b*p)*Real.log (a*(1-p)+b*p) -
        a*(1-p)*Real.log (1-p) - b*p*Real.log p) +
      p^2 * (1-p) * ((a*p+b*(1-p))*Real.log (a*p+b*(1-p)) -
        a*p*Real.log p - b*(1-p)*Real.log (1-p)) := by
  simp only [mixedLoss, mixedLossJet, logPolyDeriv_zero, eval_mul, eval_pow, eval_X,
    eval_sub, eval_one, eval_add, eval_C, affinePoly_eval, one_mul, add_zero]
  rw [show (b - a) * p + a = a * (1 - p) + b * p by ring,
    show (a - b) * p + b = a * p + b * (1 - p) by ring,
    show -1 * p + 1 = 1 - p by ring]
  ring

theorem hasDerivAt_mixedLossJet {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (mixedLossJet a b n) (mixedLossJet a b (n + 1) p) p := by
  have hp_pos : 0 < p := hp.1
  have hq_pos : 0 < 1 - p := sub_pos.mpr hp.2
  have haff₁ : 0 < (b-a) * p + a := by
    rw [show (b-a) * p + a = a*(1-p) + b*p by ring]
    exact add_pos (mul_pos ha hq_pos) (mul_pos hb hp_pos)
  have haff₂ : 0 < (a-b) * p + b := by
    rw [show (a-b) * p + b = a*p + b*(1-p) by ring]
    exact add_pos (mul_pos ha hp_pos) (mul_pos hb hq_pos)
  have hp' : 1 * p + 0 ≠ 0 := by simpa using hp_pos.ne'
  have hq : -1 * p + 1 ≠ 0 := by
    rw [show -1 * p + 1 = 1 - p by ring]
    exact hq_pos.ne'
  unfold mixedLossJet
  exact (((hasDerivAt_logPolyDeriv _ _ _ n haff₁.ne').fun_add
    (hasDerivAt_logPolyDeriv _ _ _ n haff₂.ne')).fun_sub
    (hasDerivAt_logPolyDeriv _ _ _ n hp')).fun_sub
    (hasDerivAt_logPolyDeriv _ _ _ n hq)

theorem deriv2_mixedLoss {a b p : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hp : p ∈ Ioo (0 : ℝ) 1) :
    deriv (deriv (mixedLoss a b)) p = mixedLossJet a b 2 p := by
  have hlocal : deriv (mixedLoss a b) =ᶠ[𝓝 p] mixedLossJet a b 1 :=
    Filter.Eventually.mono
      (show ∀ᶠ x in 𝓝 p, x ∈ Ioo (0 : ℝ) 1 from Ioo_mem_nhds hp.1 hp.2)
      fun _ hx => (hasDerivAt_mixedLossJet ha hb 0 hx).deriv
  exact ((hasDerivAt_mixedLossJet ha hb 1 hp).congr_of_eventuallyEq hlocal).deriv

end Bernoulli4
