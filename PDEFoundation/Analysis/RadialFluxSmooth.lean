module

public import PDEFoundation.Analysis.RadialCoefficientFlux
public import PDEFoundation.Analysis.RadialForcingDivergence
public import PDEFoundation.Analysis.RadialModeSmooth
public import PDEFoundation.Measure.RadialLogModeLp

@[expose] public section

namespace PDE
noncomputable section

private theorem vecNormSq_ne_zero_on_punctured {d : ℕ} :
    ∀ x ∈ ({0} : Set (Vec d))ᶜ, vecNormSq x ≠ 0 := by
  intro x hx hq
  exact hx (vecNormSq_eq_zero hq)

private theorem contDiffOn_coordinate_product_div_vecNormSq
    {d : ℕ} (i j : Fin d) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec d => x i * x j / vecNormSq x)
      ({0} : Set (Vec d))ᶜ := by
  exact (by fun_prop : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec d => x i * x j)
    ({0} : Set (Vec d))ᶜ).div contDiff_vecNormSq.contDiffOn
      vecNormSq_ne_zero_on_punctured

/-- The coefficient flux of a homogeneous radial mode is smooth off zero. -/
theorem contDiffOn_radialCoefficientFlux_apply
    {d : ℕ} (δ β : ℝ) (k i : Fin d) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec d => radialCoefficientFlux δ k β x i)
      ({0} : Set (Vec d))ᶜ := by
  unfold radialCoefficientFlux matVecMul
  apply ContDiffOn.sum
  intro j hj
  have hquot := contDiffOn_coordinate_product_div_vecNormSq i j
  have hcoef : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x : Vec d => ((1 : Mat d) + δ • radialReflectionMatrix x) i j)
      ({0} : Set (Vec d))ᶜ := by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      radialReflectionMatrix, two_smul, Matrix.sub_apply, radialProjectionMatrix_apply]
    fun_prop
  exact hcoef.mul (contDiffOn_radialModePowerField_apply k j β)

/-- Every coordinate of the bounded radial forcing is smooth off zero. -/
theorem contDiffOn_radialForcing_apply
    {d : ℕ} (k i : Fin d) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec d => radialForcing k x i)
      ({0} : Set (Vec d))ᶜ := by
  have hquot : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec d => x k / vecNormSq x)
      ({0} : Set (Vec d))ᶜ :=
    (by fun_prop : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec d => x k)
      ({0} : Set (Vec d))ᶜ).div contDiff_vecNormSq.contDiffOn vecNormSq_ne_zero_on_punctured
  simp only [radialForcing, Pi.smul_apply, smul_eq_mul]
  fun_prop

/-- Every coordinate of the logarithmic mode's gradient is smooth off zero. -/
theorem contDiffOn_radialLogGradientField_apply
    {d : ℕ} (k i : Fin d) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec d => radialLogGradientField k x i)
      ({0} : Set (Vec d))ᶜ := by
  have hlogq : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec d => Real.log (vecNormSq x))
      ({0} : Set (Vec d))ᶜ :=
    contDiff_vecNormSq.contDiffOn.log vecNormSq_ne_zero_on_punctured
  have hlog : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec d => Real.log (vecEuclideanNorm x))
      ({0} : Set (Vec d))ᶜ := by
    apply ((contDiffOn_const (c := (1 / 2 : ℝ))).mul hlogq).congr
    intro x hx
    rw [← vecEuclideanNorm_sq, Real.log_pow]
    ring
  have hquot := contDiffOn_coordinate_product_div_vecNormSq k i
  unfold radialLogGradientField
  fun_prop

end
end PDE
