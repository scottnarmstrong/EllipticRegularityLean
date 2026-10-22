module

public import PDEFoundation.Geometry.EuclideanBall.Interior
public import PDEFoundation.Regularity.CenteredCubeAverage
public import PDEFoundation.Sobolev.Inequalities.ConvexPoincareL2
public import PDEFoundation.Sobolev.H1.MeanEnergy

/-! # From round-ball gradient energy to centered-cube oscillation -/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Poincaré on a centered cube in its normalized energy form. -/
theorem centeredCubeL2Oscillation_le_radius_mul_gradient_mean
    {U : Set (Vec d)} (u : H1Function U) (z : Vec d) {r : ℝ} (hr : 0 < r)
    (hsub : centeredAxisCube z r ⊆ U) :
    centeredCubeL2Oscillation u.toFun z r ≤
      ((2 : ℝ) ^ d * (2 * Real.sqrt d)) * r *
        Real.sqrt (integralAverage (centeredAxisCube z r)
          (fun x => vecNormSq (u.grad x))) := by
  have hp := centeredPoincare_sq_on_boundedConvexSubdomain u
    (isOpenBoundedConvexDomain_centeredAxisCube z r) hsub
    (hasEuclideanDiameterLE_centeredAxisCube z hr.le) (by positivity)
    ⟨z, center_mem_centeredAxisCube z hr⟩
  have hdiv := div_le_div_of_nonneg_right hp
    (ENNReal.toReal_nonneg : 0 ≤ (volume (centeredAxisCube z r)).toReal)
  apply (sq_le_sq₀ (centeredCubeL2Oscillation_nonneg _ _ _) (by positivity)).mp
  rw [centeredCubeL2Oscillation_sq_eq_setIntegral_div_volume]
  have hsqrt := Real.sq_sqrt (integralAverage_nonneg
    (isOpen_centeredAxisCube z r).measurableSet (fun x _ => vecNormSq_nonneg (u.grad x)))
  rw [mul_pow, mul_pow, hsqrt]
  change (∫ x in centeredAxisCube z r,
      (u.toFun x - integralAverage (centeredAxisCube z r) u.toFun) ^ 2) /
      (volume (centeredAxisCube z r)).toReal ≤ _
  refine hdiv.trans_eq ?_
  unfold integralAverage
  beta_reduce
  ring

/-- Exact volume conversion between a cube and its enclosing round ball. -/
theorem sqrt_volume_enclosingBall_div_cube
    (z : Vec d) {r : ℝ} (hr : 0 < r) (hd : 0 < d) :
    Real.sqrt (volume (euclideanBall z (2 * Real.sqrt d * r))).toReal /
      Real.sqrt (volume (centeredAxisCube z r)).toReal =
      Real.sqrt ((Real.sqrt d) ^ d * (volume (euclideanBall (0 : Vec d) 1)).toReal) := by
  have hroot : 0 < Real.sqrt d := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)
  rw [← Real.sqrt_div ENNReal.toReal_nonneg,
    volume_euclideanBall_toReal_eq_unit_mul_of_pos z (by positivity),
    volume_centeredAxisCube_toReal z hr.le]
  have heq : (2 * Real.sqrt d * r) ^ d = (Real.sqrt d) ^ d * (2 * r) ^ d := by
    rw [← mul_pow]
    congr 1
    ring
  rw [heq]
  congr 1
  have hnonzero : (2 * r) ^ d ≠ 0 := by positivity
  field_simp

/-- Cube oscillation is controlled by the normalized gradient energy on its
enclosing round ball, with a constant depending only on dimension. -/
theorem centeredCubeL2Oscillation_le_radius_mul_ball_gradient_mean
    {U : Set (Vec d)} (hd : 0 < d) (u : H1Function U) (z : Vec d)
    {r : ℝ} (hr : 0 < r)
    (hball : euclideanBall z (2 * Real.sqrt d * r) ⊆ U) :
    centeredCubeL2Oscillation u.toFun z r ≤
      (((2 : ℝ) ^ d * (2 * Real.sqrt d)) *
        Real.sqrt ((Real.sqrt d) ^ d * (volume (euclideanBall (0 : Vec d) 1)).toReal)) * r *
        Real.sqrt (integralAverage (euclideanBall z (2 * Real.sqrt d * r))
          (fun x => vecNormSq (u.grad x))) := by
  have hcube := centeredAxisCube_subset_euclideanBall hd z hr
  have hroot : 0 < Real.sqrt d := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)
  have hmean := sqrt_integralAverage_vecNormSq_mono_set hcube
    (volume_euclideanBall_toReal_pos z (by positivity))
    (fun i => memLpOn_mono hball (u.gradMemL2 i))
  rw [sqrt_volume_enclosingBall_div_cube z hr hd] at hmean
  calc
    _ ≤ ((2 : ℝ) ^ d * (2 * Real.sqrt d)) * r *
        Real.sqrt (integralAverage (centeredAxisCube z r)
          (fun x => vecNormSq (u.grad x))) :=
      centeredCubeL2Oscillation_le_radius_mul_gradient_mean u z hr (hcube.trans hball)
    _ ≤ ((2 : ℝ) ^ d * (2 * Real.sqrt d)) * r *
        (Real.sqrt ((Real.sqrt d) ^ d * (volume (euclideanBall (0 : Vec d) 1)).toReal) *
          Real.sqrt (integralAverage (euclideanBall z (2 * Real.sqrt d * r))
            (fun x => vecNormSq (u.grad x)))) :=
      mul_le_mul_of_nonneg_left hmean (by positivity)
    _ = _ := by ring

end

end PDE
