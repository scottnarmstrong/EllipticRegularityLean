module

public import PDEFoundation.Measure.MatrixPerturbationProbabilityAverage
public import PDEFoundation.Measure.ProbabilityConvolutionLp

/-! # Exact operator bounds preserved by matrix convolution -/

@[expose] public section

namespace PDE
open MeasureTheory
open scoped ENNReal Convolution

private theorem integral_kernel_density_eq {d : ℕ}
    (K : Vec d → ℝ) (hKn : ∀ y, 0 ≤ K y)
    (hKm : AEMeasurable K volume) (f : Vec d → ℝ) :
    ∫ y, f y ∂(volume.withDensity (fun y => ENNReal.ofReal (K y))) =
      ∫ y, K y * f y := by
  have heq : (fun y => ENNReal.ofReal (K y)) =
      fun y => (Real.toNNReal (K y):ENNReal) := by
    funext y
    rw [ENNReal.ofReal_eq_coe_nnreal (hKn y), Real.toNNReal_of_nonneg (hKn y)]
  rw [heq, integral_withDensity_eq_integral_smul₀ hKm.real_toNNReal]
  congr 1
  funext y
  simp [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (hKn y)]

/-- Convolution by a nonnegative unit-mass smooth kernel preserves the
exact Euclidean operator bound of an identity perturbation at every point. -/
theorem isMatrixPerturbationLE_identity_add_convolution
    {d : ℕ} {ρ : Vec d → ℝ} (hρ : IsConvexApproxKernel ρ)
    {r delta : ℝ} (hr : 0 < r) (hdelta : 0 ≤ delta)
    (b : CoeffField d)
    (hb : ∀ i j, AEMeasurable (fun x => b x i j) volume)
    (hclose : ∀ᵐ x ∂volume, IsMatrixPerturbationLE delta (b x) (0 : Mat d))
    (x : Vec d) :
    IsMatrixPerturbationLE delta
      ((1 : Mat d) + Matrix.of (fun i j =>
        (scaledConvexApproxKernel ρ r ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (fun y => b y i j)) x)) (1 : Mat d) := by
  let K := scaledConvexApproxKernel ρ r
  let μ : Measure (Vec d) := volume.withDensity (fun y => ENNReal.ofReal (K y))
  have hKn : ∀ y, 0 ≤ K y := scaledConvexApproxKernel_nonneg hρ hr
  have hKm : Measurable K := measurable_scaledConvexApproxKernel hρ.continuous r
  have hKi : Integrable K volume := integrable_scaledConvexApproxKernel hρ hr
  have hKone : ∫ y, K y = 1 := integral_scaledConvexApproxKernel hρ hr
  let : IsProbabilityMeasure μ := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal hKi (ae_of_all _ hKn),hKone]
    simp
  have hAC : μ ≪ volume := withDensity_absolutelyContinuous _ _
  have hmp : MeasurePreserving (fun y : Vec d => x - y) volume volume := by
    have hadd := measurePreserving_add_right (volume : Measure (Vec d)) x
    have hneg := Measure.measurePreserving_neg (volume : Measure (Vec d))
    convert hadd.comp hneg using 1
    funext y
    simp only [Function.comp_apply, sub_eq_add_neg, add_comm]
  have hbμ : ∀ i j, AEMeasurable (fun y => b (x - y) i j) μ := by
    intro i j
    exact (AEStronglyMeasurable.mono_ac hAC
      ((hb i j).aestronglyMeasurable.comp_quasiMeasurePreserving
        hmp.quasiMeasurePreserving)).aemeasurable
  have hcμ : ∀ᵐ y ∂μ, IsMatrixPerturbationLE delta (b (x - y)) (0 : Mat d) :=
    hAC.ae_le (hmp.quasiMeasurePreserving.ae hclose)
  have h := isMatrixPerturbationLE_add_coordinateIntegral_of_probability
    (μ := μ) (fun y => b (x - y)) (1 : Mat d) hdelta hbμ hcμ
  have heq : Matrix.of (fun i j => ∫ y, b (x - y) i j ∂μ) =
      Matrix.of (fun i j =>
        (scaledConvexApproxKernel ρ r ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (fun y => b y i j)) x) := by
    ext i j
    simp only [Matrix.of_apply, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    exact integral_kernel_density_eq K hKn hKm.aemeasurable _
  rw [heq] at h
  exact h

end PDE
