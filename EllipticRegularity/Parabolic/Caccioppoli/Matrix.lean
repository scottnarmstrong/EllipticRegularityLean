module

public import PDEFoundation.Ambient.CoefficientField

/-!
# Matrix bounds for the parabolic Caccioppoli inequality

Elementary consequences of `IsEllipticMatrix` (manuscript (5.1)): `|A e|² ≤ Λ e·A e` and the
pointwise Young inequality behind the absorption step.
-/

@[expose] public section

namespace PDE

namespace ParabCaccioppoli

theorem vecDot_add_right' {d : ℕ} (x y z : Vec d) :
    vecDot x (y + z) = vecDot x y + vecDot x z := by
  simp [vecDot, mul_add, Finset.sum_add_distrib]

theorem vecDot_smul_right' {d : ℕ} (x y : Vec d) (c : ℝ) :
    vecDot x (c • y) = c * vecDot x y := by
  simp only [vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `|A e|² ≤ Λ e·A e`. -/
theorem normSq_mul_le {d : ℕ} {lam Lam : ℝ} {A : Mat d} (hA : IsEllipticMatrix lam Lam A)
    (e : Vec d) : vecNormSq (matVecMul A e) ≤ Lam * vecDot e (matVecMul A e) :=
  vecNormSq_matVecMul_le_mul_vecDot_of_isEllipticMatrix hA e

/-- `e·A e ≥ 0`. -/
theorem dot_nonneg {d : ℕ} {lam Lam : ℝ} {A : Mat d} (hA : IsEllipticMatrix lam Lam A)
    (e : Vec d) : 0 ≤ vecDot e (matVecMul A e) :=
  (mul_nonneg hA.lam_pos.le (vecNormSq_nonneg e)).trans (hA.coercive e)

/-- Pointwise Young step: `φ² g·A g ≤ 2 (A g)·(φ² g + 2 φ u p) + 4 Λ u² |p|²`. -/
theorem young_pointwise {d : ℕ} {lam Lam : ℝ} {A : Mat d} (hA : IsEllipticMatrix lam Lam A)
    (g p : Vec d) (φ u : ℝ) :
    φ ^ 2 * vecDot g (matVecMul A g) ≤
      2 * vecDot (matVecMul A g) (φ ^ 2 • g + (2 * φ * u) • p) +
        4 * Lam * (u ^ 2 * vecNormSq p) := by
  set q := vecDot g (matVecMul A g) with hq
  set w := matVecMul A g
  have hq0 : 0 ≤ q := dot_nonneg hA g
  have hN : vecNormSq w ≤ Lam * q := normSq_mul_le hA g
  have hL := hA.Lam_pos
  have hexp : vecDot w (φ ^ 2 • g + (2 * φ * u) • p) =
      φ ^ 2 * q + (2 * φ * u) * vecDot w p := by
    rw [vecDot_add_right', vecDot_smul_right', vecDot_smul_right', vecDot_comm w g]
  have hcs := sq_vecDot_le_vecNormSq_mul_vecNormSq w p
  have hsq : ((2 * φ * u) * vecDot w p) ^ 2 ≤ (φ ^ 2 * q) * (4 * Lam * (u ^ 2 * vecNormSq p)) := by
    have h1 : ((2 * φ * u) * vecDot w p) ^ 2 = 4 * φ ^ 2 * u ^ 2 * vecDot w p ^ 2 := by ring
    have h2 : vecDot w p ^ 2 ≤ (Lam * q) * vecNormSq p :=
      hcs.trans (mul_le_mul_of_nonneg_right hN (vecNormSq_nonneg p))
    have h3 : 0 ≤ 4 * φ ^ 2 * u ^ 2 := by positivity
    calc _ = 4 * φ ^ 2 * u ^ 2 * vecDot w p ^ 2 := h1
      _ ≤ 4 * φ ^ 2 * u ^ 2 * ((Lam * q) * vecNormSq p) := mul_le_mul_of_nonneg_left h2 h3
      _ = _ := by ring
  have habs := abs_le_add_halves_of_sq_le_mul hsq (by positivity)
    (by have := vecNormSq_nonneg p; positivity)
  have := (abs_le.mp habs).1
  rw [hexp]
  nlinarith [this]

end ParabCaccioppoli

end PDE
