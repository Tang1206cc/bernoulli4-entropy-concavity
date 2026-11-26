module

public import Bernoulli4.Entropy
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul

import Mathlib.Tactic.Ring

@[expose] public section

/-! The second derivative is computed by differentiating the probability polynomials. -/

namespace Bernoulli4

open scoped BigOperators Topology
open Filter Set

noncomputable def entropyTermSlope (Q : Polynomial ℝ) (p : ℝ) : ℝ :=
  (-Real.log (Q.eval p) - 1) * Q.derivative.eval p

noncomputable def entropyTermCurvature (Q : Polynomial ℝ) (p : ℝ) : ℝ :=
  (-Real.log (Q.eval p) - 1) * Q.derivative.derivative.eval p -
    Q.derivative.eval p ^ 2 / Q.eval p

theorem hasDerivAt_entropyTerm {Q : Polynomial ℝ} {p : ℝ} (hQ : Q.eval p ≠ 0) :
    HasDerivAt (fun x => Real.negMulLog (Q.eval x)) (entropyTermSlope Q p) p := by
  simpa only [entropyTermSlope, Function.comp_def] using
    (Real.hasDerivAt_negMulLog hQ).comp p (Q.hasDerivAt p)

theorem hasDerivAt_entropyTermSlope {Q : Polynomial ℝ} {p : ℝ} (hQ : Q.eval p ≠ 0) :
    HasDerivAt (entropyTermSlope Q) (entropyTermCurvature Q p) p := by
  have hlog := (Q.hasDerivAt p).log hQ
  have hleft := hlog.neg.sub_const 1
  convert hleft.mul (Q.derivative.hasDerivAt p) using 1
  · rfl
  · simp only [entropyTermCurvature, Pi.neg_apply]
    ring

theorem deriv_entropy {w : Fin 4 → ℝ} {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    deriv (entropy w) p = ∑ s ∈ support w, entropyTermSlope (massPoly w s) p := by
  exact (HasDerivAt.fun_sum (fun _ hs => hasDerivAt_entropyTerm (mass_pos hs hp).ne')).deriv

theorem deriv2_entropy {w : Fin 4 → ℝ} {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    deriv (deriv (entropy w)) p =
      ∑ s ∈ support w, entropyTermCurvature (massPoly w s) p := by
  have hloc : deriv (entropy w) =ᶠ[𝓝 p] fun x =>
      ∑ s ∈ support w, entropyTermSlope (massPoly w s) x :=
    Filter.Eventually.mono
      (show ∀ᶠ x in 𝓝 p, x ∈ Ioo (0 : ℝ) 1 from Ioo_mem_nhds hp.1 hp.2)
      fun _ hx => deriv_entropy hx
  exact ((HasDerivAt.fun_sum (fun _ hs =>
    hasDerivAt_entropyTermSlope (mass_pos hs hp).ne')).congr_of_eventuallyEq hloc).deriv

end Bernoulli4
