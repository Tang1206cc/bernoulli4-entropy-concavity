module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul

import Mathlib.Tactic.Ring

@[expose] public section

/-! A sixth-derivative criterion for a quadratic lower bound on curvature. -/

namespace Bernoulli4

open Filter Set
open scoped Topology

private theorem min_of_second_nonneg {f g h : ℝ → ℝ} {p c : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hfg : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f (g x) x)
    (hgh : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt g (h x) x)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ h x) (hcrit : g c = 0) :
    f c ≤ f p := by
  have hsecond (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt (deriv f) (h x) x := by
    apply (hgh x hx).congr_of_eventuallyEq
    exact Filter.Eventually.mono
      (show ∀ᶠ y in 𝓝 x, y ∈ Ioo (0 : ℝ) 1 from Ioo_mem_nhds hx.1 hx.2)
      fun y hy => (hfg y hy).deriv
  have hconv : ConvexOn ℝ (Ioo (0 : ℝ) 1) f :=
    convexOn_of_deriv2_nonneg' (convex_Ioo 0 1)
      (fun x hx => (hfg x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (hsecond x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => by
        change 0 ≤ deriv (deriv f) x
        rw [(hsecond x hx).deriv]
        exact hpos x hx)
  have hlocal : c ∈ interior (Ioo (0 : ℝ) 1) := by
    rwa [isOpen_Ioo.interior_eq]
  have hright : derivWithin f (Ioi c) c = 0 := by
    rw [(hfg c hc).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi c), hcrit]
  exact hconv.isMinOn_of_rightDeriv_eq_zero hlocal hright hp

/-- At a common zero of the third and fifth derivatives, a nonnegative sixth derivative
gives a quadratic lower bound for the second derivative, with coefficient (f^{(4)}(c)/2). -/
theorem curvature_quadratic_growth {f₂ f₃ f₄ f₅ f₆ : ℝ → ℝ} {p c : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hp : p ∈ Ioo (0 : ℝ) 1)
    (h₂₃ : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f₂ (f₃ x) x)
    (h₃₄ : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f₃ (f₄ x) x)
    (h₄₅ : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f₄ (f₅ x) x)
    (h₅₆ : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f₅ (f₆ x) x)
    (h₆ : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ f₆ x) (h₃ : f₃ c = 0) (h₅ : f₅ c = 0) :
    f₂ c + (f₄ c / 2) * (p - c) ^ 2 ≤ f₂ p := by
  let q : ℝ → ℝ := fun x => f₂ x - (f₄ c / 2) * (x - c) ^ 2
  let q' : ℝ → ℝ := fun x => f₃ x - f₄ c * (x - c)
  have g₁ (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt q (q' x) x := by
    have hid := (hasDerivAt_id x).sub_const c
    have hsub := (h₂₃ x hx).fun_sub (((hid.pow 2).const_mul (f₄ c / 2)))
    apply hsub.congr_deriv
    simp [q']
    ring
  have g₂ (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt q' (f₄ x - f₄ c) x := by
    simpa [q'] using (h₃₄ x hx).fun_sub (((hasDerivAt_id x).sub_const c).const_mul (f₄ c))
  have hq := min_of_second_nonneg hc hp g₁ g₂
    (fun x hx => sub_nonneg.mpr (min_of_second_nonneg hc hx h₄₅ h₅₆ h₆ h₅))
    (by simpa [q'] using h₃)
  have hh : f₂ c ≤ f₂ p - (f₄ c / 2) * (p - c) ^ 2 := by simpa [q] using hq
  exact le_sub_iff_add_le.mp hh

end Bernoulli4
