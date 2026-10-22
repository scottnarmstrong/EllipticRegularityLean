/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.Caccioppoli.Matrix

/-! # Pointwise Young inequality for the power energy estimate -/

@[expose] public section

namespace PDE.Parabolic.LocalMax

open PDE

/-- Real-number Young step: `|F' · 2ηχ P| ≤ ½ F'' Q η² χ + 2 Λ K F |∇η|² χ`. -/
theorem abs_young_le {F0 F1 F2 K L Q N η χ P : ℝ} (hF0 : 0 ≤ F0) (hF2 : 0 ≤ F2) (hK : 0 ≤ K)
    (hL : 0 ≤ L) (hQ : 0 ≤ Q) (hN : 0 ≤ N) (hχ : 0 ≤ χ) (h1 : F1 ^ 2 ≤ K * F2 * F0)
    (hP : P ^ 2 ≤ L * Q * N) :
    |F1 * (2 * η * χ * P)| ≤ 1 / 2 * F2 * Q * η ^ 2 * χ + 2 * L * K * F0 * N * χ := by
  set x : ℝ := 1 / 2 * F2 * Q * η ^ 2 * χ with hx
  set y : ℝ := 2 * L * K * F0 * N * χ with hy
  have hx0 : 0 ≤ x := by positivity
  have hy0 : 0 ≤ y := by positivity
  apply abs_le_of_sq_le_sq _ (add_nonneg hx0 hy0)
  have hm : F1 ^ 2 * P ^ 2 ≤ (K * F2 * F0) * (L * Q * N) :=
    mul_le_mul h1 hP (sq_nonneg _) (by positivity)
  have hexp : (F1 * (2 * η * χ * P)) ^ 2 = 4 * η ^ 2 * χ ^ 2 * (F1 ^ 2 * P ^ 2) := by ring
  have h4 : (F1 * (2 * η * χ * P)) ^ 2 ≤ 4 * x * y := by
    rw [hexp]
    calc 4 * η ^ 2 * χ ^ 2 * (F1 ^ 2 * P ^ 2)
        ≤ 4 * η ^ 2 * χ ^ 2 * ((K * F2 * F0) * (L * Q * N)) :=
          mul_le_mul_of_nonneg_left hm (by positivity)
      _ = 4 * x * y := by rw [hx, hy]; ring
  nlinarith [sq_nonneg (x - y)]

/-- Pointwise lower bound for the renormalized integrand tested against `η² χ`. -/
theorem renorm_pointwise_lower {d : ℕ} {Lam K : ℝ} {A : Mat d} (hA : IsEllipticMatrix 1 Lam A)
    {F0 F1 F2 η τ χ χ' : ℝ} (e p : Vec d) (hF0 : 0 ≤ F0) (hF2 : 0 ≤ F2) (hK : 0 ≤ K)
    (hχ : 0 ≤ χ) (h1 : F1 ^ 2 ≤ K * F2 * F0) :
    F0 * η ^ 2 * (-χ') + 1 / 2 * F2 * vecNormSq e * η ^ 2 * χ -
        χ * (F0 * (2 * |η| * |τ| + 2 * Lam * K * vecNormSq p)) ≤
      -(F0 * (2 * η * τ * χ + η ^ 2 * χ')) +
        F1 * vecDot (matVecMul A e) ((2 * η * χ) • p) +
        F2 * vecDot (matVecMul A e) e * (η ^ 2 * χ) := by
  have hLam : 0 ≤ Lam := hA.Lam_pos.le
  have hQ0 : 0 ≤ vecDot e (matVecMul A e) := ParabCaccioppoli.dot_nonneg hA e
  have hQ1 : vecNormSq e ≤ vecDot e (matVecMul A e) := by
    have := hA.coercive e
    rwa [one_mul] at this
  have hP : vecDot (matVecMul A e) p ^ 2 ≤ Lam * vecDot e (matVecMul A e) * vecNormSq p :=
    (sq_vecDot_le_vecNormSq_mul_vecNormSq _ _).trans
      (mul_le_mul_of_nonneg_right (ParabCaccioppoli.normSq_mul_le hA e) (vecNormSq_nonneg p))
  have hY := abs_young_le (η := η) hF0 hF2 hK hLam hQ0 (vecNormSq_nonneg p) hχ h1 hP
  rw [ParabCaccioppoli.vecDot_smul_right', vecDot_comm (matVecMul A e) e]
  have hY' := (abs_le.mp hY).1
  have hT : F0 * (2 * η * τ * χ) ≤ χ * (F0 * (2 * |η| * |τ|)) := by
    have : η * τ ≤ |η| * |τ| := by rw [← abs_mul]; exact le_abs_self _
    have h2 : 0 ≤ F0 * χ := mul_nonneg hF0 hχ
    nlinarith [mul_le_mul_of_nonneg_left this h2]
  have hA2 : 1 / 2 * F2 * vecNormSq e * η ^ 2 * χ ≤
      1 / 2 * F2 * vecDot e (matVecMul A e) * η ^ 2 * χ := by
    have : 0 ≤ 1 / 2 * F2 * η ^ 2 * χ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hQ1 this]
  have hB : 0 ≤ χ * (F0 * (2 * Lam * K * vecNormSq p)) := by
    have := vecNormSq_nonneg p
    positivity
  nlinarith [hY', hT, hA2, hB]

end PDE.Parabolic.LocalMax
