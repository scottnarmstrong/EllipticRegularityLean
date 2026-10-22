module

public import EllipticRegularity.Parabolic.Cauchy.Lions.KernelTest
public import PDEFoundation.Measure.LpPower

/-! # Translation invariance of the mollifier-test norms -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace PDE.Parabolic.Lions

/-- The `L²` norm of a centered kernel test does not depend on its center. -/
theorem cauchyKernelTest_norm_eq {d : ℕ} {a : ℝ} (x : Vec d)
    (hmemx : MemLp (cauchyKernelTest a x) 2 (volume : Measure (Vec d)))
    (hmem0 : MemLp (cauchyKernelTest a (0 : Vec d)) 2
      (volume : Measure (Vec d))) :
    ‖hmemx.toLp (cauchyKernelTest a x)‖ =
      ‖hmem0.toLp (cauchyKernelTest a (0 : Vec d))‖ := by
  have hsqx : ‖hmemx.toLp (cauchyKernelTest a x)‖ ^ 2 =
      ∫ y, (cauchyKernelTest a x y) ^ 2 := by
    rw [Lp.norm_toLp]
    exact PDE.toReal_eLpNorm_two_sq_eq_integral_sq hmemx
  have hsq0 : ‖hmem0.toLp (cauchyKernelTest a (0 : Vec d))‖ ^ 2 =
      ∫ y, (cauchyKernelTest a (0 : Vec d) y) ^ 2 := by
    rw [Lp.norm_toLp]
    exact PDE.toReal_eLpNorm_two_sq_eq_integral_sq hmem0
  have hIx : ∫ y, (cauchyKernelTest a x y) ^ 2 =
      ∫ y : Vec d, (PDE.Parabolic.Energy.kern (d := d) a y) ^ 2 := by
    unfold cauchyKernelTest
    exact integral_sub_left_eq_self
      (fun z : Vec d => (PDE.Parabolic.Energy.kern (d := d) a z) ^ 2) volume x
  have hI0 : ∫ y, (cauchyKernelTest a (0 : Vec d) y) ^ 2 =
      ∫ y : Vec d, (PDE.Parabolic.Energy.kern (d := d) a y) ^ 2 := by
    unfold cauchyKernelTest
    exact integral_sub_left_eq_self
      (fun z : Vec d => (PDE.Parabolic.Energy.kern (d := d) a z) ^ 2) volume (0 : Vec d)
  have hnormsq : ‖hmemx.toLp (cauchyKernelTest a x)‖ ^ 2 =
      ‖hmem0.toLp (cauchyKernelTest a (0 : Vec d))‖ ^ 2 := by
    rw [hsqx, hsq0, hIx, hI0]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hnormsq

/-- The `L²` norm of a coordinate derivative of the centered kernel test does not depend on its
center. -/
theorem cauchyKernelTest_spaceGrad_norm_eq {d : ℕ} {a : ℝ}
    (i : Fin d) (x : Vec d)
    (hmemx : MemLp (fun y => spaceGradC1 (cauchyKernelTest a x) y i) 2
      (volume : Measure (Vec d)))
    (hmem0 : MemLp (fun y => spaceGradC1 (cauchyKernelTest a (0 : Vec d)) y i) 2
      (volume : Measure (Vec d))) :
    ‖hmemx.toLp (fun y => spaceGradC1 (cauchyKernelTest a x) y i)‖ =
      ‖hmem0.toLp (fun y => spaceGradC1 (cauchyKernelTest a (0 : Vec d)) y i)‖ := by
  let ψx : Vec d → ℝ := fun y => spaceGradC1 (cauchyKernelTest a x) y i
  let ψ0 : Vec d → ℝ := fun y => spaceGradC1 (cauchyKernelTest a (0 : Vec d)) y i
  have hcontx : Continuous ψx := by
    dsimp [ψx]
    change Continuous fun y : Vec d => (fderiv ℝ (cauchyKernelTest a x) y) (basisVec i)
    exact ((cauchyKernelTest_contDiff_one a x).continuous_fderiv
      (by norm_num)).clm_apply continuous_const
  have hcont0 : Continuous ψ0 := by
    dsimp [ψ0]
    change Continuous fun y : Vec d =>
      (fderiv ℝ (cauchyKernelTest a (0 : Vec d)) y) (basisVec i)
    exact ((cauchyKernelTest_contDiff_one a (0 : Vec d)).continuous_fderiv
      (by norm_num)).clm_apply continuous_const
  have hmemx' : MemLp ψx 2 (volume : Measure (Vec d)) := by
    simpa [ψx] using hmemx
  have hmem0' : MemLp ψ0 2 (volume : Measure (Vec d)) := by
    simpa [ψ0] using hmem0
  have hsqx : ‖hmemx'.toLp ψx‖ ^ 2 = ∫ y, ψx y ^ 2 := by
    rw [Lp.norm_toLp]
    exact PDE.toReal_eLpNorm_two_sq_eq_integral_sq hmemx'
  have hsq0 : ‖hmem0'.toLp ψ0‖ ^ 2 = ∫ y, ψ0 y ^ 2 := by
    rw [Lp.norm_toLp]
    exact PDE.toReal_eLpNorm_two_sq_eq_integral_sq hmem0'
  have hIx : ∫ y, ψx y ^ 2 =
      ∫ y, (fderiv ℝ (PDE.Parabolic.Energy.kern a) y (basisVec i)) ^ 2 := by
    calc
      ∫ y, ψx y ^ 2 = ∫ y,
          (fderiv ℝ (PDE.Parabolic.Energy.kern a) (x - y) (basisVec i)) ^ 2 := by
        apply integral_congr_ae
        filter_upwards [] with y
        rw [show ψx y = spaceGradC1 (cauchyKernelTest a x) y i by rfl,
          cauchyKernelTest_spaceGrad]
        ring
      _ = ∫ y, (fderiv ℝ (PDE.Parabolic.Energy.kern a) y (basisVec i)) ^ 2 := by
        exact integral_sub_left_eq_self
          (fun z : Vec d => (fderiv ℝ (PDE.Parabolic.Energy.kern a) z (basisVec i)) ^ 2)
          volume x
  have hI0 : ∫ y, ψ0 y ^ 2 =
      ∫ y, (fderiv ℝ (PDE.Parabolic.Energy.kern a) y (basisVec i)) ^ 2 := by
    calc
      ∫ y, ψ0 y ^ 2 = ∫ y,
          (fderiv ℝ (PDE.Parabolic.Energy.kern a) ((0 : Vec d) - y) (basisVec i)) ^ 2 := by
        apply integral_congr_ae
        filter_upwards [] with y
        rw [show ψ0 y = spaceGradC1 (cauchyKernelTest a (0 : Vec d)) y i by rfl,
          cauchyKernelTest_spaceGrad]
        ring
      _ = ∫ y, (fderiv ℝ (PDE.Parabolic.Energy.kern a) y (basisVec i)) ^ 2 := by
        exact integral_sub_left_eq_self
          (fun z : Vec d => (fderiv ℝ (PDE.Parabolic.Energy.kern a) z (basisVec i)) ^ 2)
          volume (0 : Vec d)
  have hnormsq : ‖hmemx'.toLp ψx‖ ^ 2 = ‖hmem0'.toLp ψ0‖ ^ 2 := by
    rw [hsqx, hsq0, hIx, hI0]
  have hnonnegx : 0 ≤ ‖hmemx'.toLp ψx‖ := norm_nonneg _
  have hnonneg0 : 0 ≤ ‖hmem0'.toLp ψ0‖ := norm_nonneg _
  have hnorm : ‖hmemx'.toLp ψx‖ = ‖hmem0'.toLp ψ0‖ :=
    (sq_eq_sq₀ hnonnegx hnonneg0).mp hnormsq
  simpa [ψx, ψ0] using hnorm

end PDE.Parabolic.Lions
