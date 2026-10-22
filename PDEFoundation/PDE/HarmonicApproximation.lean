module

public import PDEFoundation.PDE.HarmonicSmoothing
public import PDEFoundation.Sobolev.W1p.ConvexApprox.Density

/-!
# Harmonicity of convex smooth approximation

The existing approximation first convolves the zero extension, then composes
with a scalar affine contraction. Every sampled point lies in the convex
domain, so the weak harmonic equation applies to the reflected kernel.
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped Convolution ENNReal

noncomputable section

variable {d : ℕ}

/-- Coordinate differentiation under a scalar affine sampling map. -/
theorem euclideanCoordDeriv_comp_smul_add
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (a : ℝ) (b x : Vec d) (i : Fin d) :
    euclideanCoordDeriv i (fun y => f (a • y + b)) x =
      a * euclideanCoordDeriv i f (a • x + b) := by
  have hg : HasFDerivAt (fun y : Vec d => a • y + b)
      (a • (1 : Vec d →L[ℝ] Vec d)) x :=
    ((hasFDerivAt_id x).const_smul a).add_const b
  have h := ((hf.differentiable (by simp) (a • x + b)).hasFDerivAt.comp x hg).fderiv
  change fderiv ℝ (fun y => f (a • y + b)) x = _ at h
  unfold euclideanCoordDeriv
  rw [h]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    one_apply_eq_self, map_smul, smul_eq_mul]

/-- The native coordinate Laplacian has the exact scalar affine factor. -/
theorem euclideanCoordLaplacian_comp_smul_add
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (a : ℝ) (b x : Vec d) :
    euclideanCoordLaplacian (fun y => f (a • y + b)) x =
      a ^ 2 * euclideanCoordLaplacian f (a • x + b) := by
  have hfirst : ∀ i : Fin d,
      euclideanCoordDeriv i (fun y => f (a • y + b)) =
        fun y => a * euclideanCoordDeriv i f (a • y + b) := by
    intro i
    funext y
    exact euclideanCoordDeriv_comp_smul_add hf a b y i
  have hsecond : ∀ i : Fin d,
      euclideanCoordSecondDeriv i i (fun y => f (a • y + b)) x =
        a ^ 2 * euclideanCoordSecondDeriv i i f (a • x + b) := by
    intro i
    unfold euclideanCoordSecondDeriv
    rw [hfirst i]
    have hD := contDiff_euclideanCoordDeriv hf i
    have hcomp : DifferentiableAt ℝ (fun y => euclideanCoordDeriv i f (a • y + b)) x :=
      ((hD.comp ((contDiff_id.const_smul a).add (contDiff_const (c := b)))).differentiable
        (by simp)) x
    rw [fderiv_const_mul hcomp]
    simp only [smul_apply, smul_eq_mul]
    change a * euclideanCoordDeriv i (fun y => euclideanCoordDeriv i f (a • y + b)) x = _
    rw [euclideanCoordDeriv_comp_smul_add hD]
    simp only [euclideanCoordDeriv]
    ring
  rw [euclideanCoordLaplacian, Finset.sum_congr rfl (fun i _ => hsecond i),
    ← Finset.mul_sum]
  rfl

/-- Scaling a convex approximation kernel scales its inherited-metric support. -/
theorem tsupport_scaledConvexApproxKernel_subset_closedBall
    {ρ : Vec d → ℝ} (hρ : IsConvexApproxKernel ρ)
    {a : ℝ} (ha : 0 < a) :
    tsupport (scaledConvexApproxKernel ρ a) ⊆ Metric.closedBall 0 a := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro y hy
  have hρy : ρ (a⁻¹ • y) ≠ 0 := by
    intro hz
    apply hy
    simp only [scaledConvexApproxKernel, hz, mul_zero]
  have hmem := hρ.support_subset_closedBall (subset_tsupport ρ hρy)
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)] at hmem
  rw [Metric.mem_closedBall, dist_zero_right]
  have hmul := mul_le_mul_of_nonneg_left hmem ha.le
  simpa only [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul, mul_one] using hmul

/-- Reflected support of the scaled kernel samples only points in the convex domain. -/
theorem tsupport_reflected_scaledConvexApproxKernel_subset
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {ρ : Vec d → ℝ} (hρ : IsConvexApproxKernel ρ)
    {x0 x : Vec d} {r ε : ℝ} (hx : x ∈ U)
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    tsupport (fun y => scaledConvexApproxKernel ρ (ε * r)
      ((1 - ε) • x + ε • x0 - y)) ⊆ U := by
  let A : Vec d := (1 - ε) • x + ε • x0
  have ha : 0 < ε * r := mul_pos hε hr
  have hK := tsupport_scaledConvexApproxKernel_subset_closedBall hρ ha
  intro y hy
  have hky : A - y ∈ tsupport (scaledConvexApproxKernel ρ (ε * r)) := by
    let he : Homeomorph (Vec d) (Vec d) := Homeomorph.subLeft A
    have hs := he.preimage_closure (s := Function.support (scaledConvexApproxKernel ρ (ε * r)))
    have hpre : Function.support (fun y => scaledConvexApproxKernel ρ (ε * r) (A - y)) =
        he ⁻¹' Function.support (scaledConvexApproxKernel ρ (ε * r)) := by
      ext w
      simp [he, Homeomorph.subLeft, sub_eq_add_neg]
    change y ∈ closure (Function.support (fun y => scaledConvexApproxKernel ρ (ε * r) (A - y))) at hy
    rw [hpre, ← hs] at hy
    simpa [he, Homeomorph.subLeft, sub_eq_add_neg, add_comm] using! hy
  have hnorm : ‖A - y‖ ≤ ε * r := by
    have h := hK hky
    simpa only [Metric.mem_closedBall, dist_zero_right] using h
  let z : Vec d := (ε * r)⁻¹ • (A - y)
  have hz : ‖z‖ ≤ 1 := by
    dsimp only [z]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
    calc
      (ε * r)⁻¹ * ‖A - y‖ ≤ (ε * r)⁻¹ * (ε * r) :=
        mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr ha.le)
      _ = 1 := inv_mul_cancel₀ ha.ne'
  have hsample := convexApproxSample_mem_of_isOpenBoundedConvexDomain
    hU hx hball hr.le hz hε.le hε1
  have heq : convexApproxSample x0 z r ε x = y := by
    dsimp only [convexApproxSample, z, A]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [hε.ne', hr.ne']
    ring
  exact heq ▸ hsample

/-- Convex smooth approximation of an actual weak harmonic function remains
classically harmonic throughout the original convex domain. -/
theorem euclideanCoordLaplacian_convexApproxSmoothRepresentative_eq_zero
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U)
    (hu : ∀ φ : WeakTestFunction U,
      ∫ x in U, vecDot (u.grad x) (φ.grad x) = 0)
    {ρ : Vec d → ℝ} (hρ : IsConvexApproxKernel ρ)
    {x0 x : Vec d} {r ε : ℝ} (hx : x ∈ U)
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    euclideanCoordLaplacian
      (convexApproxSmoothRepresentative U ρ u.toFun x0 r ε) x = 0 := by
  let K := scaledConvexApproxKernel ρ (ε * r)
  have hKs : HasCompactSupport K :=
    hasCompactSupport_scaledConvexApproxKernel hρ.compactSupport (mul_pos hε hr)
  have hK : ContDiff ℝ (⊤ : ℕ∞) K := contDiff_scaledConvexApproxKernel hρ _
  have hui : MemLp (Set.indicator U u.toFun) 2 volume := by
    rw [memLp_indicator_iff_restrict hU.measurableSet]
    exact u.memL2
  have hconv : ContDiff ℝ (⊤ : ℕ∞)
      (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Set.indicator U u.toFun) :=
    HasCompactSupport.contDiff_convolution_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ) hKs hK
      (hui.locallyIntegrable (by norm_num))
  have hzero := euclideanCoordLaplacian_convolution_indicator_eq_zero hU.isOpen hu hKs hK
    ((1 - ε) • x + ε • x0)
    (tsupport_reflected_scaledConvexApproxKernel_subset hU hρ hx hball hr hε hε1)
  change euclideanCoordLaplacian
    (fun y => (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Set.indicator U u.toFun)
      ((1 - ε) • y + ε • x0)) x = 0
  rw [euclideanCoordLaplacian_comp_smul_add hconv, hzero, mul_zero]

/-- Every member of the already established smooth Sobolev approximation
sequence is classically harmonic, including its initial zero contraction. -/
theorem euclideanCoordLaplacian_convexApproxSmoothW1p_eq_zero
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U)
    (hu : ∀ φ : WeakTestFunction U,
      ∫ x in U, vecDot (u.grad x) (φ.grad x) = 0)
    {x0 x : Vec d} {r : ℝ} (hx : x ∈ U)
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) (n : ℕ) :
    euclideanCoordLaplacian
      (W1pFunction.convexApproxSmoothW1p hU (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        u.toW1pFunction x0 hr n).toFun x = 0 := by
  rw [W1pFunction.convexApproxSmoothW1p_toFun]
  exact euclideanCoordLaplacian_convexApproxSmoothRepresentative_eq_zero hU u hu
    isConvexApproxKernel_unitConvexApproxKernel hx hball hr
    (unitConvexApproxScale_pos n) (unitConvexApproxScale_le_one n)

end

end PDE
