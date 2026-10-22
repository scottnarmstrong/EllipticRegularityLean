module

public import PDEFoundation.PDE.HarmonicApproximation
public import PDEFoundation.Sobolev.Cutoff.Ball
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# A normalized Euclidean-radial harmonic mollifier

The kernel is a normalized round-ball cutoff. Its radial profile is written
as a smooth function of the squared Euclidean radius, avoiding the norm's
nondifferentiability at the origin. Dilations use the Euclidean scaling law.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace PDE

def harmonicKernelCutoff {d : ℕ} : Vec d → ℝ :=
  canonicalBallCutoff 0 (1 / 4) 1

private theorem harmonicKernelCutoff_smooth {d : ℕ} :
    ContDiff ℝ (⊤ : ℕ∞) (harmonicKernelCutoff (d := d)) := by
  exact canonicalBallCutoff_smooth 0 (by norm_num) (by norm_num)

private theorem harmonicKernelCutoff_compact {d : ℕ} :
    HasCompactSupport (harmonicKernelCutoff (d := d)) := by
  exact canonicalBallCutoff_hasCompactSupport (by norm_num) (by norm_num)

private theorem harmonicKernelCutoff_nonneg {d : ℕ} (y : Vec d) :
    0 ≤ harmonicKernelCutoff y :=
  canonicalBallCutoff_nonneg 0 _ _ y

private theorem harmonicKernelCutoff_one_zero {d : ℕ} :
    harmonicKernelCutoff (0 : Vec d) = 1 := by
  apply canonicalBallCutoff_eq_one_on_inner (by norm_num) (by norm_num)
  exact center_mem_euclideanBall 0 (by norm_num)

/-- The positive normalizing integral of the round cutoff. -/
def harmonicKernelNormalizer (d : ℕ) : ℝ :=
  (∫ y, harmonicKernelCutoff (d := d) y)⁻¹

theorem harmonicKernelNormalizer_pos {d : ℕ} :
    0 < harmonicKernelNormalizer d := by
  unfold harmonicKernelNormalizer
  have hpos : 0 < ∫ y, harmonicKernelCutoff (d := d) y :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      harmonicKernelCutoff_smooth.continuous harmonicKernelCutoff_compact
      harmonicKernelCutoff_nonneg (by rw [harmonicKernelCutoff_one_zero]; norm_num)
  exact inv_pos.mpr hpos

/-- The fixed unit-scale radial kernel, normalized to have integral one. -/
def harmonicKernel {d : ℕ} : Vec d → ℝ :=
  harmonicKernelNormalizer d • harmonicKernelCutoff

/-- The smooth profile as a function of squared Euclidean radius. -/
def harmonicKernelProfile (d : ℕ) (t : ℝ) : ℝ :=
  harmonicKernelNormalizer d *
    smoothTransitionProfile
      (((5 / 8 : ℝ) ^ 2 - t) / ((5 / 8 : ℝ) ^ 2 - (1 / 4 : ℝ) ^ 2))

theorem harmonicKernel_smooth {d : ℕ} :
    ContDiff ℝ (⊤ : ℕ∞) (harmonicKernel (d := d)) := by
  unfold harmonicKernel
  exact contDiff_const.smul harmonicKernelCutoff_smooth

theorem harmonicKernel_nonneg {d : ℕ} (y : Vec d) :
    0 ≤ harmonicKernel y := by
  rw [harmonicKernel]
  exact smul_nonneg (harmonicKernelNormalizer_pos.le) (harmonicKernelCutoff_nonneg y)

theorem harmonicKernel_hasCompactSupport {d : ℕ} :
    HasCompactSupport (harmonicKernel (d := d)) := by
  exact harmonicKernelCutoff_compact.smul_left

theorem harmonicKernelProfile_smooth (d : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (harmonicKernelProfile d) := by
  unfold harmonicKernelProfile
  have harg : ContDiff ℝ (⊤ : ℕ∞)
      (fun t : ℝ => ((5 / 8 : ℝ) ^ 2 - t) /
        ((5 / 8 : ℝ) ^ 2 - (1 / 4 : ℝ) ^ 2)) := by
    apply (contDiff_const.sub contDiff_id).div contDiff_const
    intro _
    norm_num
  exact contDiff_const.mul (smoothTransitionProfile.smooth.comp harg)

private theorem harmonicKernelProfile_zero_of_cutoff_radius {d : ℕ} {t : ℝ}
    (ht : (5 / 8 : ℝ) ^ 2 ≤ t) : harmonicKernelProfile d t = 0 := by
  unfold harmonicKernelProfile
  have hden : 0 < (5 / 8 : ℝ) ^ 2 - (1 / 4 : ℝ) ^ 2 := by norm_num
  have hnum : (5 / 8 : ℝ) ^ 2 - t ≤ 0 := by linarith
  rw [smoothTransitionProfile.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg hnum hden.le)]
  simp

theorem harmonicKernelProfile_zero_of_one_le {d : ℕ} {t : ℝ}
    (ht : 1 ≤ t) : harmonicKernelProfile d t = 0 := by
  apply harmonicKernelProfile_zero_of_cutoff_radius
  nlinarith

theorem harmonicKernel_eq_profile {d : ℕ} (y : Vec d) :
    harmonicKernel y = harmonicKernelProfile d (vecNormSq y) := by
  unfold harmonicKernel
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [harmonicKernelProfile]
  change harmonicKernelNormalizer d * canonicalBallCutoff 0 (1 / 4) 1 y = _
  unfold canonicalBallCutoff
  rw [show ballCutoffMidRadius (1 / 4) 1 = (5 / 8 : ℝ) by
    norm_num [ballCutoffMidRadius]]
  apply congrArg (fun q : ℝ => harmonicKernelNormalizer d * smoothTransitionProfile q)
  norm_num [ballCutoffArgument, euclideanSqDist]

private theorem harmonicKernel_support_subset_cutoffBall {d : ℕ} :
    Function.support (harmonicKernel (d := d)) ⊆
      euclideanClosedBall 0 (5 / 8) := by
  intro y hy
  have hne : harmonicKernel y ≠ 0 := by
    simpa only [Function.mem_support] using hy
  rw [harmonicKernel_eq_profile] at hne
  have hrad : vecNormSq y < (5 / 8 : ℝ) ^ 2 := by
    by_contra hnot
    exact hne (harmonicKernelProfile_zero_of_cutoff_radius (le_of_not_gt hnot))
  simpa [euclideanClosedBall, euclideanSqDist] using hrad.le

theorem harmonicKernel_tsupport_subset {d : ℕ} :
    tsupport (harmonicKernel (d := d)) ⊆ euclideanBall 0 1 := by
  have hts : tsupport (harmonicKernel (d := d)) ⊆
      euclideanClosedBall 0 (5 / 8) :=
    closure_minimal harmonicKernel_support_subset_cutoffBall
      (isClosed_euclideanClosedBall (0 : Vec d) (5 / 8))
  exact hts.trans (euclideanClosedBall_subset_euclideanBall (by norm_num) (by norm_num))

theorem harmonicKernel_integral_eq_one {d : ℕ} :
    (∫ y, harmonicKernel (d := d) y) = 1 := by
  change ∫ y, harmonicKernelNormalizer d * harmonicKernelCutoff y = 1
  rw [integral_const_mul]
  unfold harmonicKernelNormalizer
  exact inv_mul_cancel₀ (ne_of_gt (by
    have h := harmonicKernelNormalizer_pos (d := d)
    unfold harmonicKernelNormalizer at h
    exact inv_pos.mp h))

/-- Dilation of the unit kernel to radius `s`. -/
def harmonicKernelScaled {d : ℕ} (s : ℝ) (y : Vec d) : ℝ :=
  s⁻¹ ^ d * harmonicKernel (s⁻¹ • y)

/-- The radial profile after dilation, still parameterized by squared radius. -/
def harmonicKernelScaledProfile (d : ℕ) (s t : ℝ) : ℝ :=
  s⁻¹ ^ d * harmonicKernelProfile d (s⁻¹ ^ 2 * t)

theorem harmonicKernelScaled_smooth {d : ℕ} (s : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (harmonicKernelScaled (d := d) s) := by
  unfold harmonicKernelScaled
  exact contDiff_const.mul
    (harmonicKernel_smooth.comp (contDiff_id.const_smul s⁻¹))

theorem harmonicKernelScaled_nonneg {d : ℕ} {s : ℝ}
    (hs : 0 < s) (y : Vec d) : 0 ≤ harmonicKernelScaled (d := d) s y := by
  unfold harmonicKernelScaled
  exact mul_nonneg (pow_nonneg (inv_nonneg.mpr hs.le) _)
    (harmonicKernel_nonneg _)

theorem harmonicKernelScaled_hasCompactSupport {d : ℕ} {s : ℝ}
    (hs : 0 < s) : HasCompactSupport (harmonicKernelScaled (d := d) s) := by
  unfold harmonicKernelScaled
  have hcomp := (harmonicKernel_hasCompactSupport (d := d)).comp_smul
    (inv_ne_zero hs.ne')
  convert (hcomp.smul_left (f := fun _ : Vec d => s⁻¹ ^ d)) using 1

theorem harmonicKernelScaledProfile_smooth (d : ℕ) (s : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (harmonicKernelScaledProfile d s) := by
  unfold harmonicKernelScaledProfile
  exact contDiff_const.mul ((harmonicKernelProfile_smooth d).comp
    (contDiff_const.mul contDiff_id))

theorem harmonicKernelScaledProfile_zero_of_scale_squared_le {d : ℕ}
    {s t : ℝ} (hs : 0 < s) (ht : s ^ 2 ≤ t) :
    harmonicKernelScaledProfile d s t = 0 := by
  unfold harmonicKernelScaledProfile
  have hinv : s⁻¹ ^ 2 * s ^ 2 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hs.ne', one_pow]
  have harg : 1 ≤ s⁻¹ ^ 2 * t := by
    have hmul := mul_le_mul_of_nonneg_left ht (sq_nonneg s⁻¹)
    rw [hinv] at hmul
    exact hmul
  rw [harmonicKernelProfile_zero_of_one_le harg, mul_zero]

theorem harmonicKernelScaled_eq_profile {d : ℕ} (s : ℝ) (y : Vec d) :
    harmonicKernelScaled (d := d) s y =
      harmonicKernelScaledProfile d s (vecNormSq y) := by
  rw [harmonicKernelScaled, harmonicKernelScaledProfile, harmonicKernel_eq_profile]
  congr 2
  rw [vecNormSq_smul]

theorem harmonicKernelScaled_integral_eq_one {d : ℕ} {s : ℝ}
    (hs : 0 < s) : (∫ y, harmonicKernelScaled (d := d) s y) = 1 := by
  change ∫ y, (s⁻¹ ^ d) * harmonicKernel (s⁻¹ • y) = 1
  rw [integral_const_mul,
    MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg volume
      (harmonicKernel (d := d)) hs.le]
  rw [harmonicKernel_integral_eq_one]
  have hdim : Module.finrank ℝ (Vec d) = d := by simp [Vec]
  rw [hdim, smul_eq_mul]
  rw [mul_one, inv_pow]
  exact inv_mul_cancel₀ (pow_ne_zero d hs.ne')

theorem harmonicKernelScaled_tsupport_subset {d : ℕ} {s : ℝ}
    (hs : 0 < s) :
    tsupport (harmonicKernelScaled (d := d) s) ⊆ euclideanBall 0 s := by
  let r : ℝ := 5 / 8
  have hr : 0 < r := by norm_num [r]
  have hr1 : r < 1 := by norm_num [r]
  have hclosed : Function.support (harmonicKernelScaled (d := d) s) ⊆
      euclideanClosedBall 0 (s * r) := by
    intro y hy
    have hval : harmonicKernelScaled (d := d) s y ≠ 0 := by
      simpa only [Function.mem_support] using hy
    have hz : harmonicKernel (s⁻¹ • y) ≠ 0 := by
      intro hzero
      apply hval
      simp [harmonicKernelScaled, hzero]
    have hzball : s⁻¹ • y ∈ euclideanClosedBall 0 r :=
      harmonicKernel_support_subset_cutoffBall hz
    have hnorm :=
      (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hr.le).mp hzball
    have hnorm' : vecEuclideanNorm (s⁻¹ • y) ≤ r := by
      simpa only [sub_zero] using hnorm
    rw [vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr hs)] at hnorm'
    have hm := mul_le_mul_of_nonneg_left hnorm' hs.le
    have hinv : s * s⁻¹ = 1 := mul_inv_cancel₀ hs.ne'
    rw [← mul_assoc, hinv, one_mul] at hm
    have hnormy : vecEuclideanNorm y ≤ s * r := hm
    exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le
      (mul_nonneg hs.le hr.le)).mpr (by simpa only [sub_zero] using hnormy)
  have hts : tsupport (harmonicKernelScaled (d := d) s) ⊆
      euclideanClosedBall 0 (s * r) :=
    closure_minimal hclosed
      (isClosed_euclideanClosedBall (0 : Vec d) (s * r))
  exact hts.trans (euclideanClosedBall_subset_euclideanBall
    (mul_nonneg hs.le hr.le) (by nlinarith))

private theorem euclideanCoordDeriv_const_mul {d : ℕ} {f : Vec d → ℝ}
    {x : Vec d} (i : Fin d) (c : ℝ) (hf : DifferentiableAt ℝ f x) :
    euclideanCoordDeriv i (fun y => c * f y) x = c * euclideanCoordDeriv i f x := by
  unfold euclideanCoordDeriv
  rw [fderiv_const_mul hf c]
  simp [smul_eq_mul]

theorem harmonicKernelScaled_deriv {d : ℕ} (i : Fin d) {s : ℝ}
    (y : Vec d) :
    euclideanCoordDeriv i (harmonicKernelScaled (d := d) s) y =
      (s⁻¹ ^ d * s⁻¹) * euclideanCoordDeriv i harmonicKernel (s⁻¹ • y) := by
  change euclideanCoordDeriv i (fun z => s⁻¹ ^ d * harmonicKernel (s⁻¹ • z)) y = _
  have hconst := euclideanCoordDeriv_const_mul
    (f := fun z : Vec d => harmonicKernel (s⁻¹ • z)) i (s⁻¹ ^ d)
    ((harmonicKernel_smooth.comp (contDiff_id.const_smul s⁻¹)).differentiable
      (by simp) y)
  have hcomp := euclideanCoordDeriv_comp_smul_add
    harmonicKernel_smooth s⁻¹ (0 : Vec d) y i
  have hcomp' : euclideanCoordDeriv i (fun z : Vec d => harmonicKernel (s⁻¹ • z)) y =
      s⁻¹ * euclideanCoordDeriv i harmonicKernel (s⁻¹ • y) := by
    simpa only [add_zero] using hcomp
  calc
    _ = s⁻¹ ^ d * euclideanCoordDeriv i
        (fun z : Vec d => harmonicKernel (s⁻¹ • z)) y := hconst
    _ = s⁻¹ ^ d * (s⁻¹ * euclideanCoordDeriv i harmonicKernel (s⁻¹ • y)) := by
      rw [hcomp']
    _ = (s⁻¹ ^ d * s⁻¹) * euclideanCoordDeriv i harmonicKernel (s⁻¹ • y) := by ring

theorem harmonicKernel_deriv_integrable {d : ℕ} (i : Fin d) :
    Integrable (euclideanCoordDeriv i (harmonicKernel (d := d))) := by
  exact (contDiff_euclideanCoordDeriv harmonicKernel_smooth i).continuous
    |>.integrable_of_hasCompactSupport
      (hasCompactSupport_euclideanCoordDeriv harmonicKernel_hasCompactSupport i)

theorem harmonicKernel_deriv_abs_integrable {d : ℕ} (i : Fin d) :
    Integrable (fun y => |euclideanCoordDeriv i (harmonicKernel (d := d)) y|) := by
  exact (harmonicKernel_deriv_integrable i).abs

theorem harmonicKernel_deriv_abs_hasFiniteIntegral {d : ℕ} (i : Fin d) :
    HasFiniteIntegral (fun y =>
      |euclideanCoordDeriv i (harmonicKernel (d := d)) y|) volume :=
  (harmonicKernel_deriv_abs_integrable i).hasFiniteIntegral

theorem harmonicKernelScaled_deriv_integrable {d : ℕ} (i : Fin d)
    {s : ℝ} (hs : 0 < s) :
    Integrable (euclideanCoordDeriv i (harmonicKernelScaled (d := d) s)) := by
  exact (contDiff_euclideanCoordDeriv (harmonicKernelScaled_smooth s) i).continuous
    |>.integrable_of_hasCompactSupport
      (hasCompactSupport_euclideanCoordDeriv
        (harmonicKernelScaled_hasCompactSupport hs) i)

theorem harmonicKernelScaled_deriv_abs_integrable {d : ℕ} (i : Fin d)
    {s : ℝ} (hs : 0 < s) :
    Integrable (fun y => |euclideanCoordDeriv i (harmonicKernelScaled (d := d) s) y|) := by
  exact (harmonicKernelScaled_deriv_integrable i hs).abs

/-- Sum of the coordinate derivative `L¹` norms; this depends only on `d`. -/
def harmonicKernelDerivConst (d : ℕ) : ℝ :=
  ∑ i : Fin d, ∫ y, |euclideanCoordDeriv i (harmonicKernel (d := d)) y|

theorem harmonicKernelDerivConst_nonneg {d : ℕ} :
    0 ≤ harmonicKernelDerivConst d := by
  unfold harmonicKernelDerivConst
  exact Finset.sum_nonneg fun i _ => integral_nonneg (fun y => abs_nonneg _)

theorem harmonicKernelScaled_deriv_abs_integral {d : ℕ} (i : Fin d)
    {s : ℝ} (hs : 0 < s) :
    (∫ y, |euclideanCoordDeriv i (harmonicKernelScaled (d := d) s) y|) =
      s⁻¹ * ∫ y, |euclideanCoordDeriv i harmonicKernel y| := by
  have hcoeff : 0 ≤ s⁻¹ ^ d * s⁻¹ := by positivity
  have hpoint : ∀ y,
      |euclideanCoordDeriv i (harmonicKernelScaled (d := d) s) y| =
        (s⁻¹ ^ d * s⁻¹) *
          |euclideanCoordDeriv i harmonicKernel (s⁻¹ • y)| := by
    intro y
    rw [harmonicKernelScaled_deriv i y, abs_mul, abs_of_nonneg hcoeff]
  calc
    _ = (s⁻¹ ^ d * s⁻¹) *
        ∫ y, |euclideanCoordDeriv i harmonicKernel (s⁻¹ • y)| := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hpoint), integral_const_mul]
    _ = (s⁻¹ ^ d * s⁻¹) *
        (s ^ d * ∫ y, |euclideanCoordDeriv i harmonicKernel y|) := by
      rw [MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg volume
        (fun y => |euclideanCoordDeriv i harmonicKernel y|) hs.le]
      have hdim : Module.finrank ℝ (Vec d) = d := by simp [Vec]
      rw [hdim, smul_eq_mul]
    _ = s⁻¹ * ∫ y, |euclideanCoordDeriv i harmonicKernel y| := by
      rw [inv_pow]
      field_simp [hs.ne']

end PDE
