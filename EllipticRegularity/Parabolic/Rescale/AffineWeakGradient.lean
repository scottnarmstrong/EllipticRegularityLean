module

public import EllipticRegularity.Parabolic.Rescale.AffineMaps

/-!
# Weak gradients under the spatial rescaling

If `Df` is a weak gradient of `f` on `B(c, r)`, then `y ↦ r • Df (c + r • y)` is a weak
gradient of `y ↦ f (c + r • y)` on the unit ball.  This is the composition of the existing
translation and amplitude-normalized dilation lemmas with scalar multiplication.
-/

@[expose] public section

open MeasureTheory Set
open scoped Pointwise

namespace PDE.Parabolic.Rescale

theorem hasWeakPartialDerivOn_const_mul {d : ℕ} {U : Set (Vec d)} {i : Fin d}
    {u g : Vec d → ℝ} (h : HasWeakPartialDerivOn U i u g) (k : ℝ) :
    HasWeakPartialDerivOn U i (fun x => k * u x) (fun x => k * g x) := by
  intro φ hφ hc hsub
  have := h φ hφ hc hsub
  simp only [mul_assoc]
  rw [integral_const_mul, integral_const_mul, this, mul_neg]

theorem translateSet_neg_euclideanBall {d : ℕ} (c : Vec d) {r : ℝ} (hr : 0 < r) :
    translateSet (-c) (euclideanBall c r) = r • euclideanBall (0 : Vec d) 1 := by
  rw [euclideanBall_eq_translateSet_smul_unit_of_pos c hr, translateSet_translateSet,
    add_neg_cancel, translateSet_zero]

theorem inv_smul_smul_euclideanBall {d : ℕ} {r : ℝ} (hr : 0 < r) :
    r⁻¹ • (r • euclideanBall (0 : Vec d) 1) = euclideanBall (0 : Vec d) 1 := by
  rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

theorem hasWeakGradientOn_comp_spaceMap {d : ℕ} (c : Vec d) {r : ℝ} (hr : 0 < r)
    {f : Vec d → ℝ} {Df : Vec d → Vec d}
    (h : HasWeakGradientOn (euclideanBall c r) f Df) :
    HasWeakGradientOn (euclideanBall (0 : Vec d) 1) (fun y => f (c + r • y))
      (fun y => r • Df (c + r • y)) := by
  intro i
  have h1 := ((h.translate (-c)).dilate_of_pos (inv_pos.2 hr)) i
  rw [translateSet_neg_euclideanBall c hr, inv_smul_smul_euclideanBall hr] at h1
  have h2 := hasWeakPartialDerivOn_const_mul h1 r
  have hf : (fun y : Vec d => f (c + r • y)) =
      fun y => r * (r⁻¹ * f ((r⁻¹)⁻¹ • y - -c)) := by
    funext y
    rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul, inv_inv, sub_neg_eq_add, add_comm]
  have hg : (fun y : Vec d => (r • Df (c + r • y)) i) =
      fun y => r * Df ((r⁻¹)⁻¹ • y - -c) i := by
    funext y
    rw [inv_inv, sub_neg_eq_add, add_comm]
    rfl
  rw [hf, hg]
  exact h2

end PDE.Parabolic.Rescale
