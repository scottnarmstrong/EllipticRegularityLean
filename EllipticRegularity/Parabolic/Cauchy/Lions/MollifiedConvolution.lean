module

public import EllipticRegularity.Parabolic.Cauchy.Lions.KernelTest
public import EllipticRegularity.Parabolic.Energy.Mollifier

/-! # Convolution tests for the mollified time-slice identity -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Convolution Set

namespace PDE.Parabolic.Lions

/-- The spatial test obtained by applying scale `b` mollification to a centered scale `a` kernel.
It is the test that converts a scalar Lions time trace into a time trace of the twice-smoothed
value field. -/
noncomputable def cauchyDoubleKernelTest {d : ℕ} (a b : ℝ) (x : Vec d) : Vec d → ℝ :=
  PDE.wholeSpaceMollify b (cauchyKernelTest a x)

theorem cauchyDoubleKernelTest_contDiff {d : ℕ} {a b : ℝ} (hb : 0 < b) (x : Vec d) :
    ContDiff ℝ (⊤ : ℕ∞) (cauchyDoubleKernelTest a b x) := by
  unfold cauchyDoubleKernelTest
  exact PDE.Parabolic.Energy.moll_contDiff hb
    ((cauchyKernelTest_contDiff_one a x).continuous.locallyIntegrable)

theorem cauchyDoubleKernelTest_hasCompactSupport {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (x : Vec d) :
    HasCompactSupport (cauchyDoubleKernelTest a b x) := by
  have hconv : cauchyDoubleKernelTest a b x =
      cauchyKernelTest a x ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        PDE.Parabolic.Energy.kern b := by
    funext y
    rw [cauchyDoubleKernelTest, PDE.Parabolic.Energy.moll_eq, convolution_def]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    ring
  rw [hconv]
  exact HasCompactSupport.convolution
    (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (cauchyKernelTest_hasCompactSupport ha x)
    (PDE.Parabolic.Energy.kern_hasCompactSupport hb)

theorem cauchyDoubleKernelTest_deriv {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (_hb : 0 < b) (x q : Vec d) (i : Fin d) :
    fderiv ℝ (cauchyDoubleKernelTest a b x) q (basisVec i) =
      -∫ y, PDE.Parabolic.Energy.kern b (y - q) *
        fderiv ℝ (PDE.Parabolic.Energy.kern a) (x - y) (basisVec i) := by
  let A : Vec d → ℝ := cauchyKernelTest a x
  have hAcont : ContDiff ℝ 1 A := cauchyKernelTest_contDiff_one a x
  have hAcompact : HasCompactSupport A := cauchyKernelTest_hasCompactSupport ha x
  have hconv : cauchyDoubleKernelTest a b x =
      A ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] PDE.Parabolic.Energy.kern b := by
    funext z
    rw [cauchyDoubleKernelTest, PDE.Parabolic.Energy.moll_eq, convolution_def]
    apply integral_congr_ae
    filter_upwards [] with y
    simp only [A, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    ring
  have hfd := hAcompact.hasFDerivAt_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ)
    hAcont
    ((PDE.Parabolic.Energy.kern_continuous b).locallyIntegrable
      (μ := (volume : Measure (Vec d)))) q
  have hfd' := hfd.fderiv
  rw [hconv, hfd']
  have hderivA : ∀ y, fderiv ℝ A y (basisVec i) =
      -fderiv ℝ (PDE.Parabolic.Energy.kern a) (x - y) (basisVec i) := by
    intro y
    change spaceGradC1 (cauchyKernelTest a x) y i = _
    exact cauchyKernelTest_spaceGrad a x y i
  have hAderivCont : Continuous (fderiv ℝ A) :=
    hAcont.continuous_fderiv (by simp)
  have hex := (hAcompact.fderiv (𝕜 := ℝ)).convolutionExists_left
    (ContinuousLinearMap.precompL (Vec d) (ContinuousLinearMap.lsmul ℝ ℝ))
    hAderivCont
    ((PDE.Parabolic.Energy.kern_continuous b).locallyIntegrable
      (μ := (volume : Measure (Vec d)))) q
  rw [convolution_def]
  have hcomp := (ContinuousLinearMap.apply ℝ ℝ (basisVec i)).integral_comp_comm hex
  simp only [ContinuousLinearMap.apply_apply] at hcomp
  rw [← hcomp]
  simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply,
    smul_eq_mul]
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [hderivA y, ← cauchyKernel_even b (q - y)]
  ring_nf

end PDE.Parabolic.Lions
