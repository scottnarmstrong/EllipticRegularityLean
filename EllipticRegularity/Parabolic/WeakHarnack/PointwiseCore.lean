/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.Chain.SmoothSolution
public import EllipticRegularity.Parabolic.Caccioppoli.Matrix

/-! # Pointwise algebra for nonlinear testing in the parabolic weak Harnack inequality

The renormalized integrand splits as a time part `-(F(v) ∂ₜφ)` and a gradient part
`F'(v) A∇v·∇φ + F''(v) (A∇v·∇v) φ`.  This file bounds the gradient part, for a concave-type
profile (`F'' ≤ 0`), by a good term `F''/2 · η² |∇v|²` plus a cutoff term
`2 K Λ |∇η|²`, where `F'² ≤ K (-F'')`.  Consuming it with `0 ≤ ∫ renormalizedIntegrand`
(manuscript, proof of Proposition 5.13) gives the energy estimates and the log inequality.
-/

@[expose] public section

namespace PDE.Parabolic.WeakHarnack

open PDE

/-- The gradient part of the renormalized integrand, with `F1 = F'(v)`, `F2 = F''(v)`,
`g = ∇v`, `φ` the value and `pφ` the spatial gradient of the test function. -/
noncomputable def gradPart {d : ℕ} (F1 F2 : ℝ) (A : Mat d) (g : Vec d) (φ : ℝ) (pφ : Vec d) :
    ℝ :=
  F1 * vecDot (matVecMul A g) pφ + F2 * vecDot (matVecMul A g) g * φ

/-- The renormalized integrand is the time part plus the gradient part. -/
theorem renormalizedIntegrand_eq_time_add_gradPart {d : ℕ} {U : Set (Vec d)} {I : Set ℝ}
    (a : ParCoeffField d) (u : ParH1Function U I) (F : ℝ → ℝ) (φ : Vec d × ℝ → ℝ)
    (z : Vec d × ℝ) :
    PDE.Parabolic.Chain.renormalizedIntegrand a u F φ z =
      -(F (u.toFun z) * parTimeDeriv φ z) +
        gradPart (deriv F (u.toFun z)) (deriv (deriv F) (u.toFun z)) (a z) (u.grad z)
          (φ z) (parSpaceGrad φ z) := by
  unfold PDE.Parabolic.Chain.renormalizedIntegrand gradPart
  ring

/-- Elementary Young step: if `w² ≤ U V` with `U, V ≥ 0` then `w ≤ (U+V)/2`. -/
theorem le_half_add_of_sq_le_mul {w U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (h : w ^ 2 ≤ U * V) :
    w ≤ (U + V) / 2 := by
  have h2 : w ^ 2 ≤ ((U + V) / 2) ^ 2 := by nlinarith [sq_nonneg (U - V)]
  exact (le_abs_self w).trans (abs_le_of_sq_le_sq h2 (by positivity))

/-- `|A g · m|² ≤ Λ (A g · g) |m|²` for `IsEllipticMatrix 1 Λ A`. -/
theorem sq_vecDot_matVecMul_le {d : ℕ} {Λ : ℝ} {A : Mat d} (hA : IsEllipticMatrix 1 Λ A)
    (g m : Vec d) :
    vecDot (matVecMul A g) m ^ 2 ≤ Λ * vecDot (matVecMul A g) g * vecNormSq m := by
  have h1 := sq_vecDot_le_vecNormSq_mul_vecNormSq (matVecMul A g) m
  have h2 := ParabCaccioppoli.normSq_mul_le hA g
  rw [vecDot_comm g] at h2
  calc _ ≤ vecNormSq (matVecMul A g) * vecNormSq m := h1
    _ ≤ (Λ * vecDot (matVecMul A g) g) * vecNormSq m :=
        mul_le_mul_of_nonneg_right h2 (vecNormSq_nonneg m)

/-- **Gradient part, concave profile.**  For `F'' ≤ 0` and `F'² ≤ K (-F'')`, and the test
function `φ = ψ η²` with `∇φ = ψ (2η) ∇η` (`ψ ≥ 0` a time weight, `m = ∇η`):
`F' A g·∇φ + F'' (A g·g) φ ≤ ψ (F''/2 · η² |g|² + 2 K Λ |∇η|²)`.
Feeds the energy estimates and the log inequality of Proposition 5.13. -/
theorem gradPart_le_of_concave {d : ℕ} {Λ : ℝ} {A : Mat d} (hA : IsEllipticMatrix 1 Λ A)
    (g m : Vec d) {F1 F2 K ψ η : ℝ} (hψ : 0 ≤ ψ) (hF2 : F2 ≤ 0) (hK0 : 0 ≤ K)
    (hK : F1 ^ 2 ≤ K * (-F2)) :
    gradPart F1 F2 A g (ψ * η ^ 2) ((ψ * (2 * η)) • m) ≤
      ψ * ((F2 / 2) * η ^ 2 * vecNormSq g + 2 * K * Λ * vecNormSq m) := by
  unfold gradPart
  have hΛ := hA.Lam_pos
  set q := vecDot (matVecMul A g) g with hq
  set X := vecDot (matVecMul A g) m with hX
  have hdot : vecDot (matVecMul A g) ((ψ * (2 * η)) • m) = ψ * (2 * η) * X := by
    simp only [vecDot, Pi.smul_apply, smul_eq_mul, hX, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hdot]
  have hN : vecNormSq g ≤ q := by
    have := hA.coercive g
    rw [vecDot_comm] at this
    linarith
  have hM := vecNormSq_nonneg m
  have hX2 : X ^ 2 ≤ Λ * q * vecNormSq m := sq_vecDot_matVecMul_le hA g m
  have hq0 : 0 ≤ q := (vecNormSq_nonneg g).trans hN
  -- w = 2 η F1 X
  have hw : (2 * η * F1 * X) ^ 2 ≤ (-F2 * η ^ 2 * q) * (4 * K * Λ * vecNormSq m) := by
    have e1 : (2 * η * F1 * X) ^ 2 = 4 * η ^ 2 * F1 ^ 2 * X ^ 2 := by ring
    have h3 : F1 ^ 2 * X ^ 2 ≤ (K * (-F2)) * (Λ * q * vecNormSq m) :=
      mul_le_mul hK hX2 (sq_nonneg _) (by nlinarith)
    have h4 : 4 * η ^ 2 * (F1 ^ 2 * X ^ 2) ≤
        4 * η ^ 2 * ((K * (-F2)) * (Λ * q * vecNormSq m)) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    nlinarith [h4]
  have hU : 0 ≤ -F2 * η ^ 2 * q := by
    have : 0 ≤ -F2 := by linarith
    positivity
  have hV : 0 ≤ 4 * K * Λ * vecNormSq m := by positivity
  have hle := le_half_add_of_sq_le_mul hU hV hw
  have hinner : 2 * η * F1 * X + F2 * q * η ^ 2 ≤
      (F2 / 2) * η ^ 2 * vecNormSq g + 2 * K * Λ * vecNormSq m := by
    have h5 : (-F2) * η ^ 2 * (q - vecNormSq g) ≥ 0 :=
      mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (by linarith)
    nlinarith [h5]
  calc F1 * (ψ * (2 * η) * X) + F2 * q * (ψ * η ^ 2)
      = ψ * (2 * η * F1 * X + F2 * q * η ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hinner hψ

end PDE.Parabolic.WeakHarnack
