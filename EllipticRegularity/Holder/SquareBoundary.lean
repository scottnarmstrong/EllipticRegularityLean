module

public import PDEFoundation.Sobolev.Inequalities.SmoothSegment

/-!
# Smooth tangential energy on square sides

This small module begins the good-boundary route to the planar Hölder
estimate.  Its first result is deliberately independent of weak traces: a
globally smooth scalar function restricted to an affine side satisfies the
one-dimensional, arclength-normalized energy inequality with its exact side
length.

All points use the native `Vec d` carrier, with the final specialization
recording the length of a side of a two-dimensional square. The energy below
is genuinely tangential: the derivative is paired with the side direction
before squaring.
-/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

/-- The arclength integral of the squared tangential derivative of `u` on
the affine segment from `y` to `x`.  The segment is parametrized on `[0,1]`;
the prefactor converts that parameter integral to arclength. -/
def segmentTangentialEnergy {d : ℕ} (u : Vec d → ℝ)
    (x y : Vec d) : ℝ :=
  (vecEuclideanNorm (x - y))⁻¹ *
    ∫ t in (0 : ℝ)..1,
      ((fderiv ℝ u (segmentBlend x t y)) (x - y)) ^ 2

/-- A smooth affine segment has its endpoint oscillation controlled by its
arclength tangential energy.  This is the sharp one-dimensional factor:
the side length appears once, not squared. -/
theorem abs_sub_sq_le_length_mul_segmentTangentialEnergy
    {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x y : Vec d)
    (hxy : 0 < vecEuclideanNorm (x - y)) :
    |u x - u y| ^ 2 ≤
      vecEuclideanNorm (x - y) * segmentTangentialEnergy u x y := by
  let q : ℝ → ℝ := fun t =>
    (fderiv ℝ u (segmentBlend x t y)) (x - y)
  have hγCont : Continuous (fun t : ℝ => segmentBlend x t y) := by
    rw [show (fun t : ℝ => segmentBlend x t y) =
        fun t => y + t • (x - y) by
      funext t
      exact segmentBlend_eq_add_smul_sub x y t]
    fun_prop
  have hqCont : Continuous q := by
    exact
      ((hu.continuous_fderiv (by norm_num)).comp hγCont)
        |>.clm_apply continuous_const
  have hJensen :
      |∫ t in (0 : ℝ)..1, q t| ^ 2 ≤
        ∫ t in (0 : ℝ)..1, |q t| ^ 2 := by
    have hpowInt :
        IntervalIntegrable (fun t => |q t| ^ (2 : ℝ))
          volume 0 1 := by
      simpa only [Real.rpow_two] using!
        (hqCont.abs.pow 2 |>.intervalIntegrable (μ := volume) 0 1)
    simpa only [Real.rpow_two] using
      (abs_intervalIntegral_rpow_le_intervalIntegral_abs_rpow
        (p := (2 : ℝ)) (by norm_num)
        (hqCont.intervalIntegrable (μ := volume) 0 1) hpowInt)
  have hsq :
      |u x - u y| ^ 2 ≤
        ∫ t in (0 : ℝ)..1, (q t) ^ 2 := by
    calc
      |u x - u y| ^ 2 = |∫ t in (0 : ℝ)..1, q t| ^ 2 := by
        rw [sub_eq_integral_fderiv_along_segment hu x y]
      _ ≤ ∫ t in (0 : ℝ)..1, |q t| ^ 2 := hJensen
      _ = ∫ t in (0 : ℝ)..1, (q t) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro t _ht
        exact sq_abs (q t)
  calc
    |u x - u y| ^ 2 ≤
        ∫ t in (0 : ℝ)..1, (q t) ^ 2 := hsq
    _ = vecEuclideanNorm (x - y) *
        segmentTangentialEnergy u x y := by
      unfold segmentTangentialEnergy
      dsimp only [q]
      field_simp [hxy.ne']

/-- A side of Euclidean length `2s` contributes exactly `2s` times its
arclength tangential energy to the endpoint oscillation. -/
theorem abs_sub_sq_le_two_mul_s_mul_segmentTangentialEnergy
    {u : Vec 2 → ℝ} {s : ℝ} (hs : 0 < s)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) {x y : Vec 2}
    (hside : vecEuclideanNorm (x - y) = 2 * s) :
    |u x - u y| ^ 2 ≤ 2 * s * segmentTangentialEnergy u x y := by
  have hlength : 0 < vecEuclideanNorm (x - y) := by
    rw [hside]
    positivity
  simpa only [hside] using
    abs_sub_sq_le_length_mul_segmentTangentialEnergy hu x y hlength

end

end PDE
