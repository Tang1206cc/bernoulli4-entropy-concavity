module

public import Bernoulli4.MixedLoss

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! Exact midpoint derivatives and sixth-derivative polynomial numerators. -/

namespace Bernoulli4

open Polynomial Set

private theorem log_half : Real.log (1/2 : ℝ) = -Real.log 2 := by
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]

private theorem log_three_halves : Real.log (3/2 : ℝ) = Real.log 3 - Real.log 2 := by
  exact Real.log_div (by norm_num) (by norm_num)

macro "normalize_log_jet" : tactic =>
  `(tactic| norm_num [mixedLossJet, logPolyDeriv, logJet, LogJet.next, LogJet.value,
    affinePoly, derivative_mul, derivative_pow])

set_option maxHeartbeats 2000000 in
theorem f11_mid2 :
    mixedLossJet 1 1 2 (1/2) = -1-2*Real.log 2 := by
  normalize_log_jet
  simp only [log_half]
  ring

set_option maxHeartbeats 2000000 in
theorem f11_mid3 :
    mixedLossJet 1 1 3 (1/2) = 0 := by
  normalize_log_jet
  simp only [log_half]
  ring

set_option maxHeartbeats 2000000 in
theorem f11_mid4 :
    mixedLossJet 1 1 4 (1/2) = 40 := by
  normalize_log_jet

set_option maxHeartbeats 2000000 in
theorem f11_mid5 :
    mixedLossJet 1 1 5 (1/2) = 0 := by
  normalize_log_jet

set_option maxHeartbeats 2000000 in
theorem f11_piece0 (p : ℝ) :
    logPolyDeriv (X * (1-X)^2 * affinePoly (1-1) 1) (1-1) 1 6 p =
      (0) / (1)^6 := by
  normalize_log_jet

set_option maxHeartbeats 2000000 in
theorem f11_piece1 (p : ℝ) :
    logPolyDeriv (X^2 * (1-X) * affinePoly (1-1) 1) (1-1) 1 6 p =
      (0) / (1)^6 := by
  normalize_log_jet

set_option maxHeartbeats 2000000 in
theorem f11_piece2 (p : ℝ) :
    logPolyDeriv (C 1 * X^2 * (1-X)^2 + C 1 * X^3 * (1-X)) (1) 0 6 p =
      (-12*p^3 - 12*p^2) / (p)^6 := by
  normalize_log_jet
  ring

set_option maxHeartbeats 2000000 in
theorem f11_piece3 (p : ℝ) :
    logPolyDeriv (C 1 * X * (1-X)^3 + C 1 * X^2 * (1-X)^2) (-1) 1 6 p =
      (12*p^3 - 48*p^2 + 60*p - 24) / (1 - p)^6 := by
  normalize_log_jet
  ring

set_option maxHeartbeats 2000000 in
theorem f12_mid2 :
    mixedLossJet 1 2 2 (1/2) = -4/3-4*Real.log 3 := by
  normalize_log_jet
  simp only [log_half, log_three_halves]
  ring

set_option maxHeartbeats 2000000 in
theorem f12_mid3 :
    mixedLossJet 1 2 3 (1/2) = 0 := by
  normalize_log_jet
  simp only [log_half, log_three_halves]
  ring

set_option maxHeartbeats 2000000 in
theorem f12_mid4 :
    mixedLossJet 1 2 4 (1/2) = 1216/27+48*Real.log 3 := by
  normalize_log_jet
  simp only [log_half, log_three_halves]
  ring

set_option maxHeartbeats 2000000 in
theorem f12_mid5 :
    mixedLossJet 1 2 5 (1/2) = 0 := by
  normalize_log_jet

set_option maxHeartbeats 2000000 in
theorem f12_piece0 (p : ℝ) :
    logPolyDeriv (X * (1-X)^2 * affinePoly (2-1) 1) (2-1) 1 6 p =
      (-24*p^4 - 156*p^3 - 420*p^2 - 564*p - 276) / (p + 1)^6 := by
  normalize_log_jet
  ring

set_option maxHeartbeats 2000000 in
theorem f12_piece1 (p : ℝ) :
    logPolyDeriv (X^2 * (1-X) * affinePoly (1-2) 2) (1-2) 2 6 p =
      (-24*p^4 + 252*p^3 - 1032*p^2 + 1968*p - 1440) / (2 - p)^6 := by
  normalize_log_jet
  ring

set_option maxHeartbeats 2000000 in
theorem f12_piece2 (p : ℝ) :
    logPolyDeriv (C 2 * X^2 * (1-X)^2 + C 1 * X^3 * (1-X)) (1) 0 6 p =
      (-24*p^4 - 36*p^3 - 24*p^2) / (p)^6 := by
  normalize_log_jet
  ring

set_option maxHeartbeats 2000000 in
theorem f12_piece3 (p : ℝ) :
    logPolyDeriv (C 1 * X * (1-X)^3 + C 2 * X^2 * (1-X)^2) (-1) 1 6 p =
      (-24*p^4 + 132*p^3 - 276*p^2 + 252*p - 84) / (1 - p)^6 := by
  normalize_log_jet
  ring

set_option maxHeartbeats 2000000 in
theorem f21_mid2 :
    mixedLossJet 2 1 2 (1/2) = -4/3-2*Real.log 3 := by
  normalize_log_jet
  simp only [log_half, log_three_halves]
  ring

set_option maxHeartbeats 2000000 in
theorem f21_mid3 :
    mixedLossJet 2 1 3 (1/2) = 0 := by
  normalize_log_jet
  simp only [log_half, log_three_halves]
  ring

set_option maxHeartbeats 2000000 in
theorem f21_mid4 :
    mixedLossJet 2 1 4 (1/2) = 1600/27-48*Real.log 3 := by
  normalize_log_jet
  simp only [log_half, log_three_halves]
  ring

set_option maxHeartbeats 2000000 in
theorem f21_mid5 :
    mixedLossJet 2 1 5 (1/2) = 0 := by
  normalize_log_jet

set_option maxHeartbeats 2000000 in
theorem f21_piece0 (p : ℝ) :
    logPolyDeriv (X * (1-X)^2 * affinePoly (1-2) 2) (1-2) 2 6 p =
      (24*p^4 - 240*p^3 + 924*p^2 - 1632*p + 1104) / (2 - p)^6 := by
  normalize_log_jet
  ring

set_option maxHeartbeats 2000000 in
theorem f21_piece1 (p : ℝ) :
    logPolyDeriv (X^2 * (1-X) * affinePoly (2-1) 1) (2-1) 1 6 p =
      (24*p^4 + 144*p^3 + 348*p^2 + 408*p + 180) / (p + 1)^6 := by
  normalize_log_jet
  ring

set_option maxHeartbeats 2000000 in
theorem f21_piece2 (p : ℝ) :
    logPolyDeriv (C 1 * X^2 * (1-X)^2 + C 2 * X^3 * (1-X)) (1) 0 6 p =
      (24*p^4 - 12*p^2) / (p)^6 := by
  normalize_log_jet
  ring

set_option maxHeartbeats 2000000 in
theorem f21_piece3 (p : ℝ) :
    logPolyDeriv (C 2 * X * (1-X)^3 + C 1 * X^2 * (1-X)^2) (-1) 1 6 p =
      (24*p^4 - 96*p^3 + 132*p^2 - 72*p + 12) / (1 - p)^6 := by
  normalize_log_jet
  ring

set_option maxHeartbeats 2000000 in
theorem f13_mid2 :
    mixedLossJet 1 3 2 (1/2) = -3/2-12*Real.log 2 := by
  normalize_log_jet
  simp only [log_half]
  ring

set_option maxHeartbeats 2000000 in
theorem f13_mid3 :
    mixedLossJet 1 3 3 (1/2) = 0 := by
  normalize_log_jet
  simp only [log_half]
  ring

set_option maxHeartbeats 2000000 in
theorem f13_mid4 :
    mixedLossJet 1 3 4 (1/2) = 45+192*Real.log 2 := by
  normalize_log_jet
  simp only [log_half]
  ring

set_option maxHeartbeats 2000000 in
theorem f13_mid5 :
    mixedLossJet 1 3 5 (1/2) = 0 := by
  normalize_log_jet

set_option maxHeartbeats 2000000 in
theorem f13_piece0 (p : ℝ) :
    logPolyDeriv (X * (1-X)^2 * affinePoly (3-1) 1) (3-1) 1 6 p =
      (-3072*p^4 - 11520*p^3 - 18432*p^2 - 14784*p - 4032) / (2*p + 1)^6 := by
  normalize_log_jet
  ring

set_option maxHeartbeats 2000000 in
theorem f13_piece1 (p : ℝ) :
    logPolyDeriv (X^2 * (1-X) * affinePoly (1-3) 3) (1-3) 3 6 p =
      (-3072*p^4 + 23808*p^3 - 71424*p^2 + 98496*p - 51840) / (3 - 2*p)^6 := by
  normalize_log_jet
  ring

set_option maxHeartbeats 2000000 in
theorem f13_piece2 (p : ℝ) :
    logPolyDeriv (C 3 * X^2 * (1-X)^2 + C 1 * X^3 * (1-X)) (1) 0 6 p =
      (-48*p^4 - 60*p^3 - 36*p^2) / (p)^6 := by
  normalize_log_jet
  ring

set_option maxHeartbeats 2000000 in
theorem f13_piece3 (p : ℝ) :
    logPolyDeriv (C 1 * X * (1-X)^3 + C 3 * X^2 * (1-X)^2) (-1) 1 6 p =
      (-48*p^4 + 252*p^3 - 504*p^2 + 444*p - 144) / (1 - p)^6 := by
  normalize_log_jet
  ring

end Bernoulli4
