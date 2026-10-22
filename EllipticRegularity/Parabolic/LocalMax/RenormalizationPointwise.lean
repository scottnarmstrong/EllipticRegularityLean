/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import PDEFoundation.Ambient.CoefficientField

/-! # Pointwise bounds behind the renormalization domination -/

@[expose] public section

namespace PDE.Parabolic.LocalMax

open PDE

/-- `|(A e)·p| ≤ Λ |e| |p|` for an elliptic matrix. -/
theorem abs_vecDot_matVecMul_le {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (e p : Vec d) :
    |vecDot (matVecMul A e) p| ≤
      Lam * Real.sqrt (vecNormSq e) * Real.sqrt (vecNormSq p) := by
  have h1 := sq_vecDot_le_vecNormSq_mul_vecNormSq (matVecMul A e) p
  have h2 := vecNormSq_matVecMul_le_of_isEllipticMatrix hA e
  have hLam := hA.Lam_pos.le
  have hp := vecNormSq_nonneg p
  have he := vecNormSq_nonneg e
  apply abs_le_of_sq_le_sq _ (by positivity)
  have h3 : (Lam * Real.sqrt (vecNormSq e) * Real.sqrt (vecNormSq p)) ^ 2 =
      Lam ^ 2 * vecNormSq e * vecNormSq p := by
    rw [mul_pow, mul_pow, Real.sq_sqrt he, Real.sq_sqrt hp]
  rw [h3]
  calc vecDot (matVecMul A e) p ^ 2 ≤ vecNormSq (matVecMul A e) * vecNormSq p := h1
    _ ≤ (Lam ^ 2 * vecNormSq e) * vecNormSq p := mul_le_mul_of_nonneg_right h2 hp
    _ = _ := rfl

/-- `|(A e)·e| ≤ Λ |e|²` for an elliptic matrix. -/
theorem abs_vecDot_matVecMul_self_le {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (e : Vec d) :
    |vecDot (matVecMul A e) e| ≤ Lam * vecNormSq e := by
  have h := abs_vecDot_matVecMul_le hA e e
  have he := vecNormSq_nonneg e
  rwa [mul_assoc, Real.mul_self_sqrt he] at h

/-- Real-number algebra for the three terms of the renormalized integrand. -/
theorem abs_renorm_terms_le {Fv F1 F2 τ f x n PW PG f0 a C A Bt Bφ L Q : ℝ}
    (hf0 : 0 ≤ f0) (ha : 0 ≤ a) (hC : 0 ≤ C) (hA : 0 ≤ A) (hBt : 0 ≤ Bt) (hBφ : 0 ≤ Bφ)
    (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (hFv : |Fv| ≤ f0 + a * |x| + C * x ^ 2) (hF1 : |F1| ≤ a + C * |x|) (hF2 : |F2| ≤ A)
    (hτ : |τ| ≤ Bt) (hf : |f| ≤ Bφ) (hPW : |PW| ≤ L * n * Q) (hPG : |PG| ≤ L * n ^ 2) :
    |-(Fv * τ) + F1 * PW + F2 * PG * f| ≤
      (Bt * (f0 + a / 2) + L * Q * (a / 2)) +
        (Bt * (a / 2 + C) + L * Q * (a / 2 + C / 2) + A * L * Bφ) * (x ^ 2 + n ^ 2) := by
  have hx : 2 * |x| ≤ 1 + x ^ 2 := by linarith [sq_abs x, sq_nonneg (|x| - 1)]
  have hn2 : 2 * n ≤ 1 + n ^ 2 := by linarith [sq_nonneg (n - 1)]
  have hxn : 2 * (|x| * n) ≤ x ^ 2 + n ^ 2 := by
    linarith [sq_abs x, sq_nonneg (|x| - n)]
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  have hn22 : 0 ≤ n ^ 2 := sq_nonneg n
  have hax : 0 ≤ |x| := abs_nonneg x
  have T1 : |Fv * τ| ≤ Bt * (f0 + a / 2) + Bt * (a / 2 + C) * x ^ 2 := by
    rw [abs_mul]
    calc |Fv| * |τ| ≤ (f0 + a * |x| + C * x ^ 2) * Bt :=
          mul_le_mul hFv hτ (abs_nonneg _) (by positivity)
      _ ≤ Bt * (f0 + a / 2) + Bt * (a / 2 + C) * x ^ 2 := by
          have : a * |x| ≤ a / 2 + a / 2 * x ^ 2 := by
            linarith [mul_le_mul_of_nonneg_left hx ha]
          linarith [mul_le_mul_of_nonneg_left this hBt, mul_nonneg hBt hC, mul_nonneg hBt hx2]
  have T2 : |F1 * PW| ≤ L * Q * (a / 2) + L * Q * (a / 2 + C / 2) * (x ^ 2 + n ^ 2) := by
    rw [abs_mul]
    have hLQ : 0 ≤ L * Q := mul_nonneg hL hQ
    calc |F1| * |PW| ≤ (a + C * |x|) * (L * n * Q) :=
          mul_le_mul hF1 hPW (abs_nonneg _) (by positivity)
      _ = (L * Q) * (a * n + C * (|x| * n)) := by ring
      _ ≤ (L * Q) * (a / 2 + (a / 2 + C / 2) * (x ^ 2 + n ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ hLQ
          linarith [mul_le_mul_of_nonneg_left hn2 ha, mul_le_mul_of_nonneg_left hxn hC,
            mul_nonneg ha hn22, mul_nonneg ha hx2]
      _ = _ := by ring
  have T3 : |F2 * PG * f| ≤ A * L * Bφ * (x ^ 2 + n ^ 2) := by
    rw [abs_mul, abs_mul]
    calc |F2| * |PG| * |f| ≤ A * (L * n ^ 2) * Bφ :=
          mul_le_mul (mul_le_mul hF2 hPG (abs_nonneg _) hA) hf (abs_nonneg _)
            (by positivity)
      _ = A * L * Bφ * n ^ 2 := by ring
      _ ≤ A * L * Bφ * (x ^ 2 + n ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  calc |-(Fv * τ) + F1 * PW + F2 * PG * f|
      ≤ |-(Fv * τ) + F1 * PW| + |F2 * PG * f| := abs_add_le _ _
    _ ≤ |-(Fv * τ)| + |F1 * PW| + |F2 * PG * f| := by
        gcongr; exact abs_add_le _ _
    _ ≤ _ := by
        have hextra : 0 ≤ Bt * (a / 2 + C) * n ^ 2 :=
          mul_nonneg (mul_nonneg hBt (by positivity)) hn22
        rw [abs_neg]
        linarith [T1, T2, T3, hextra]

end PDE.Parabolic.LocalMax
