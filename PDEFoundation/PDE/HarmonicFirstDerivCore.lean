module

public import PDEFoundation.PDE.HarmonicKernel
public import PDEFoundation.PDE.HarmonicConvolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# First derivative core for the harmonic kernel convolution

The core is stated conditionally on a local representative being equal to its
kernel convolution. The pointwise estimate follows from derivative-kernel
support, the Euclidean ball geometry, and the exact derivative scaling law.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Convolution Topology

noncomputable section

namespace PDE

variable {d : ℕ}

/-- Integral convention for scalar left convolution on native vectors. -/
theorem harmonicLsmulConvolution_eq_integral (k w : Vec d → ℝ) (x : Vec d) :
    (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w) x =
      ∫ y, k y * w (x - y) ∂volume := by
  simp [MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply,
    smul_eq_mul]

/-- A scaled harmonic kernel regularizes every locally integrable function. -/
theorem contDiff_harmonicKernelScaled_convolution {s : ℝ} (hs : 0 < s)
    {w : Vec d → ℝ} (hw : LocallyIntegrable w volume) :
    ContDiff ℝ (⊤ : ℕ∞)
      (harmonicKernelScaled s ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w) := by
  exact HasCompactSupport.contDiff_convolution_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
    (harmonicKernelScaled_hasCompactSupport hs)
    (harmonicKernelScaled_smooth s) hw

/-- Coordinate derivatives commute with convolution by the scaled harmonic
kernel, pointwise everywhere. -/
theorem euclideanCoordDeriv_harmonicKernelScaled_convolution {s : ℝ}
    (hs : 0 < s) {w : Vec d → ℝ} (hw : LocallyIntegrable w volume)
    (i : Fin d) :
    euclideanCoordDeriv i
        (harmonicKernelScaled s ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w) =
      euclideanCoordDeriv i (harmonicKernelScaled s) ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        volume] w := by
  exact euclideanCoordDeriv_convolution_left
    (harmonicKernelScaled_hasCompactSupport hs)
    (harmonicKernelScaled_smooth s) hw i

/-- The `L¹` norm of one coordinate derivative of the unit kernel is bounded
by the explicit dimension-dependent derivative constant. -/
theorem harmonicKernel_deriv_abs_integral_le_DerivConst (i : Fin d) :
    (∫ y, |euclideanCoordDeriv i harmonicKernel y| ∂volume) ≤
      harmonicKernelDerivConst d := by
  unfold harmonicKernelDerivConst
  have hterms : ∀ j ∈ Finset.univ, 0 ≤
      ∫ y : Vec d, |euclideanCoordDeriv j (harmonicKernel (d := d)) y| ∂volume := by
    intro j hj
    exact integral_nonneg fun y =>
      abs_nonneg (euclideanCoordDeriv j (harmonicKernel (d := d)) y)
  simpa only using
    (Finset.single_le_sum (s := Finset.univ)
      (f := fun j : Fin d =>
        ∫ y : Vec d, |euclideanCoordDeriv j (harmonicKernel (d := d)) y| ∂volume)
      hterms (Finset.mem_univ i))

/-- Pointwise derivative-convolution estimate in terms of the unit kernel's
coordinate `L¹` norm. -/
theorem abs_euclideanCoordDeriv_convolution_le_integral {s : ℝ}
    (hs : 0 < s) {w : Vec d → ℝ} (hw : LocallyIntegrable w volume)
    (x : Vec d) (M : ℝ)
    (hbound : ∀ y ∈ euclideanBall x s, |w y| ≤ M) (i : Fin d) :
    |(euclideanCoordDeriv i (harmonicKernelScaled s) ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        volume] w) x| ≤
      M * (∫ y, |euclideanCoordDeriv i harmonicKernel y| ∂volume) * s⁻¹ := by
  let D : Vec d → ℝ := euclideanCoordDeriv i (harmonicKernelScaled s)
  have hM : 0 ≤ M := by
    exact (abs_nonneg (w x)).trans (hbound x (center_mem_euclideanBall x hs))
  have hDcont : Continuous D := by
    dsimp only [D]
    exact (contDiff_euclideanCoordDeriv (harmonicKernelScaled_smooth s) i).continuous
  have hDcompact : HasCompactSupport D := by
    dsimp only [D]
    exact hasCompactSupport_euclideanCoordDeriv
      (harmonicKernelScaled_hasCompactSupport hs) i
  have hproduct : Integrable (fun y => D y * w (x - y)) volume := by
    have hExists : ConvolutionExistsAt D w x
        (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
      (hDcompact.convolutionExists_left
        (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) hDcont hw) x
    simpa [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using hExists.integrable
  have hmajorant : Integrable (fun y => M * |D y|) volume := by
    simpa only [mul_comm] using
      (harmonicKernelScaled_deriv_abs_integrable i hs).const_mul M
  have hpointwise : ∀ y, |D y * w (x - y)| ≤ M * |D y| := by
    intro y
    by_cases hDy : D y = 0
    · simp [hDy]
    · have hySupport : y ∈ Function.support D :=
        Function.mem_support.mpr hDy
      have hyKernel : y ∈ tsupport (harmonicKernelScaled s) :=
        (tsupport_euclideanCoordDeriv_subset_tsupport i
          (harmonicKernelScaled s)) (subset_tsupport D hySupport)
      have hyBall : y ∈ euclideanBall 0 s :=
        harmonicKernelScaled_tsupport_subset hs hyKernel
      have hxyBall : x - y ∈ euclideanBall x s := by
        apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hs).2
        have hyNorm := (mem_euclideanBall_iff_vecEuclideanNorm_lt hs).1 hyBall
        have hsub : (x - y) - x = -y := by abel
        rw [hsub, vecEuclideanNorm_neg]
        simpa only [sub_zero] using hyNorm
      calc
        |D y * w (x - y)| = |D y| * |w (x - y)| := by rw [abs_mul]
        _ ≤ |D y| * M :=
          mul_le_mul_of_nonneg_left (hbound (x - y) hxyBall) (abs_nonneg _)
        _ = M * |D y| := by ring
  calc
    |(D ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w) x| =
        |∫ y, D y * w (x - y) ∂volume| := by
          rw [harmonicLsmulConvolution_eq_integral]
    _ ≤ ∫ y, |D y * w (x - y)| ∂volume := abs_integral_le_integral_abs
    _ ≤ ∫ y, M * |D y| ∂volume :=
      integral_mono_ae hproduct.abs hmajorant (Filter.Eventually.of_forall hpointwise)
    _ = M * ∫ y, |D y| ∂volume := by rw [integral_const_mul]
    _ = M * (s⁻¹ * ∫ y, |euclideanCoordDeriv i harmonicKernel y| ∂volume) := by
      rw [show D = euclideanCoordDeriv i (harmonicKernelScaled s) from rfl,
        harmonicKernelScaled_deriv_abs_integral i hs]
    _ = M * (∫ y, |euclideanCoordDeriv i harmonicKernel y| ∂volume) * s⁻¹ := by
      ring

/-- The dimension-only constant version of the pointwise derivative estimate. -/
theorem abs_euclideanCoordDeriv_convolution_le_DerivConst {s : ℝ}
    (hs : 0 < s) {w : Vec d → ℝ} (hw : LocallyIntegrable w volume)
    (x : Vec d) (M : ℝ)
    (hbound : ∀ y ∈ euclideanBall x s, |w y| ≤ M) (i : Fin d) :
    |(euclideanCoordDeriv i (harmonicKernelScaled s) ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        volume] w) x| ≤
      harmonicKernelDerivConst d / s * M := by
  have hM : 0 ≤ M := by
    exact (abs_nonneg (w x)).trans (hbound x (center_mem_euclideanBall x hs))
  have hcoord := harmonicKernel_deriv_abs_integral_le_DerivConst (d := d) i
  calc
    |(euclideanCoordDeriv i (harmonicKernelScaled s) ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        volume] w) x|
        ≤ M * (∫ y, |euclideanCoordDeriv i harmonicKernel y| ∂volume) * s⁻¹ :=
          abs_euclideanCoordDeriv_convolution_le_integral hs hw x M hbound i
    _ = M * ((∫ y, |euclideanCoordDeriv i harmonicKernel y| ∂volume) * s⁻¹) := by
      ring
    _ ≤ M * (harmonicKernelDerivConst d * s⁻¹) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hcoord (inv_nonneg.mpr hs.le)) hM
    _ = harmonicKernelDerivConst d / s * M := by
      rw [div_eq_mul_inv]
      ring

/-- Conditional first-derivative core: any representative agreeing locally
with the kernel convolution satisfies its pointwise derivative estimate. -/
theorem abs_euclideanCoordDeriv_le_of_eventuallyEq_convolution {s : ℝ}
    (hs : 0 < s) {w v : Vec d → ℝ} (hw : LocallyIntegrable w volume)
    {x : Vec d} (heq : v =ᶠ[𝓝 x]
      (harmonicKernelScaled s ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w))
    (M : ℝ) (hbound : ∀ y ∈ euclideanBall x s, |w y| ≤ M) (i : Fin d) :
    |euclideanCoordDeriv i v x| ≤ harmonicKernelDerivConst d / s * M := by
  let q : Vec d → ℝ :=
    harmonicKernelScaled s ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w
  have hK1 : ContDiff ℝ 1 (harmonicKernelScaled (d := d) s) :=
    (harmonicKernelScaled_smooth (d := d) s).of_le
      (by norm_num)
  have hq : HasFDerivAt q
      ((fderiv ℝ (harmonicKernelScaled s) ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompL
        (Vec d), volume] w) x) x := by
    exact (harmonicKernelScaled_hasCompactSupport hs).hasFDerivAt_convolution_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) hK1 hw x
  have hv : HasFDerivAt v
      ((fderiv ℝ (harmonicKernelScaled s) ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompL
        (Vec d), volume] w) x) x :=
    hq.congr_of_eventuallyEq heq
  have hderiv : fderiv ℝ v x = fderiv ℝ q x :=
    hv.fderiv.trans hq.fderiv.symm
  have hcoord : euclideanCoordDeriv i v x = euclideanCoordDeriv i q x := by
    unfold euclideanCoordDeriv
    rw [hderiv]
  calc
    |euclideanCoordDeriv i v x| = |euclideanCoordDeriv i q x| :=
      congrArg abs hcoord
    _ = |(euclideanCoordDeriv i (harmonicKernelScaled s) ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        volume] w) x| := by
      rw [euclideanCoordDeriv_harmonicKernelScaled_convolution hs hw i]
    _ ≤ harmonicKernelDerivConst d / s * M :=
      abs_euclideanCoordDeriv_convolution_le_DerivConst hs hw x M hbound i

end PDE
