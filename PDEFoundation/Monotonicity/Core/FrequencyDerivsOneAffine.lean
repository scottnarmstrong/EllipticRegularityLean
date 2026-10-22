module

public import PDEFoundation.Monotonicity.Core.FrequencyDerivsOne
public import PDEFoundation.Sobolev.ClassicalLaplacian

/-!
# Chapter 2 frequency derivatives: harmonic functions in dimension one

A `C²` function on an interval with vanishing second derivative is affine; the frequency
derivative identities follow by direct computation.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace PDE

noncomputable section

/-- A `C²` harmonic function on a ball of `Vec 1` is affine. -/
theorem affine_of_harmonicOn_one {u : Vec 1 → ℝ} {R : ℝ} (hR : 0 < R)
    (hu : ContDiffOn ℝ 2 u (euclideanBall 0 R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec 1) R, euclideanCoordLaplacian u x = 0) :
    ∃ a b : ℝ, ∀ x ∈ euclideanBall (0 : Vec 1) R,
      u x = a + b * x 0 ∧ classicalGradient u x 0 = b := by
  have hU : IsOpen (euclideanBall (0 : Vec 1) R) := isOpen_euclideanBall 0 R
  have hpre : IsPreconnected (euclideanBall (0 : Vec 1) R) :=
    (convex_euclideanBall 0 R).isPreconnected
  have h0 : (0 : Vec 1) ∈ euclideanBall (0 : Vec 1) R := center_mem_euclideanBall 0 hR
  set g : Vec 1 → ℝ := euclideanCoordDeriv 0 u with hg
  have hfd : ContDiffOn ℝ 1 (fderiv ℝ u) (euclideanBall (0 : Vec 1) R) :=
    hu.fderiv_of_isOpen hU (by norm_num)
  have hgc : ContDiffOn ℝ 1 g (euclideanBall (0 : Vec 1) R) :=
    hfd.clm_apply contDiffOn_const
  have hgdiff : DifferentiableOn ℝ g (euclideanBall (0 : Vec 1) R) := hgc.differentiableOn one_ne_zero
  have hdecomp : ∀ v : Vec 1, v = (v 0) • basisVec (0 : Fin 1) := by
    intro v; ext i; fin_cases i; simp [basisVec]
  have hg' : EqOn (fderiv ℝ g) 0 (euclideanBall (0 : Vec 1) R) := by
    intro x hx
    have hl := hharm x hx
    simp only [euclideanCoordLaplacian, euclideanCoordSecondDeriv, Fin.sum_univ_one] at hl
    ext v
    conv_lhs => rw [hdecomp v]
    rw [map_smul, hl]
    simp
  have gconst : ∀ x ∈ euclideanBall (0 : Vec 1) R, g x = g 0 := fun x hx =>
    hU.is_const_of_fderiv_eq_zero hpre hgdiff hg' hx h0
  set h : Vec 1 → ℝ := fun x => u x - g 0 * x 0 with hh
  have hudiff : DifferentiableOn ℝ u (euclideanBall (0 : Vec 1) R) :=
    hu.differentiableOn (by norm_num)
  have hproj : ∀ x : Vec 1, HasFDerivAt (fun y : Vec 1 => y 0)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) x :=
    fun _ => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).hasFDerivAt
  have hhdiff : DifferentiableOn ℝ h (euclideanBall (0 : Vec 1) R) := fun x hx =>
    ((hudiff x hx).sub
      (((hproj x).differentiableAt.const_mul _).differentiableWithinAt))
  have hh' : EqOn (fderiv ℝ h) 0 (euclideanBall (0 : Vec 1) R) := by
    intro x hx
    have hux : DifferentiableAt ℝ u x := hudiff.differentiableAt (hU.mem_nhds hx)
    have hd : HasFDerivAt h (fderiv ℝ u x - g 0 • ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin 1 => ℝ) 0) x := hux.hasFDerivAt.sub ((hproj x).const_mul (g 0))
    rw [hd.fderiv]
    ext v
    conv_lhs => rw [hdecomp v]
    simp only [sub_apply, map_smul, smul_eq_mul, smul_apply,
      ContinuousLinearMap.proj_apply]
    have hgx := gconst x hx
    simp only [hg, euclideanCoordDeriv] at hgx
    rw [hgx]
    simp [hg, euclideanCoordDeriv]
  refine ⟨u 0, g 0, fun x hx => ⟨?_, ?_⟩⟩
  · have := hU.is_const_of_fderiv_eq_zero hpre hhdiff hh' hx h0
    simp only [hh, Pi.zero_apply, mul_zero, sub_zero] at this
    linarith only [this]
  · simpa [hg, euclideanCoordDeriv] using gconst x hx

/-- Points `0 ± s e` lie in the ball when `|s| < R`. -/
theorem pm_mem_euclideanBall_one {R s : ℝ} (hR : 0 < R) (hs : |s| < R) :
    ((0 : Vec 1) + s • basisVec (0 : Fin 1) ∈ euclideanBall (0 : Vec 1) R) ∧
      ((0 : Vec 1) - s • basisVec (0 : Fin 1) ∈ euclideanBall (0 : Vec 1) R) := by
  have hn : vecEuclideanNorm (basisVec (0 : Fin 1)) = 1 := by
    simp [vecEuclideanNorm, vecNormSq, vecDot, basisVec]
  constructor
  · rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hR, zero_add, sub_zero, vecEuclideanNorm_smul, hn]
    simpa using hs
  · rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hR, zero_sub, sub_zero, vecEuclideanNorm_neg,
      vecEuclideanNorm_smul, hn]
    simpa using hs

theorem energy_const_one (c r : ℝ) (hr : 0 < r) :
    ∫ _ in euclideanBall (0 : Vec 1) r, c = 2 * c * r := by
  rw [integral_euclideanBall_eq_intervalIntegral_sphereIntegral continuous_const hr]
  simp_rw [sphereIntegral_one]
  simp
  ring

/-- `D(r) = r⁻¹ ∫_{∂B_r} u (x · ∇u)` in dimension one. -/
theorem energy_eq_inv_mul_sphereIntegral_one {u : Vec 1 → ℝ} {R r : ℝ}
    (hu : ContDiffOn ℝ 2 u (euclideanBall 0 R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec 1) R, euclideanCoordLaplacian u x = 0)
    (hr : 0 < r) (hrR : r < R) :
    ∫ x in euclideanBall (0 : Vec 1) r, vecNormSq (classicalGradient u x) =
      r⁻¹ * sphereIntegral 0 r (fun x => u x * vecDot x (classicalGradient u x)) := by
  have hR : 0 < R := hr.trans hrR
  obtain ⟨a, b, hab⟩ := affine_of_harmonicOn_one hR hu hharm
  have hsub : euclideanBall (0 : Vec 1) r ⊆ euclideanBall (0 : Vec 1) R :=
    euclideanBall_mono hr.le hrR.le
  have hD : ∫ x in euclideanBall (0 : Vec 1) r, vecNormSq (classicalGradient u x) =
      ∫ x in euclideanBall (0 : Vec 1) r, b ^ 2 := by
    refine setIntegral_congr_fun (isOpen_euclideanBall 0 r).measurableSet fun x hx => ?_
    rw [vecNormSq_eq_sum_sq, Fin.sum_univ_one, (hab x (hsub hx)).2]
  rw [hD, energy_const_one _ _ hr, sphereIntegral_one]
  obtain ⟨hp, hm⟩ := pm_mem_euclideanBall_one hR (s := r) (by rwa [abs_of_pos hr])
  have e1 := hab _ hp
  have e2 := hab _ hm
  rw [e1.1, e2.1]
  simp only [vecDot, Fin.sum_univ_one]
  rw [e1.2, e2.2]
  simp [basisVec]
  field_simp
  ring

/-- The derivative of the sphere mean of `u²` in dimension one. -/
theorem hasDerivAt_sphereMean_sq_one {u : Vec 1 → ℝ} {R r : ℝ}
    (hu : ContDiffOn ℝ 2 u (euclideanBall 0 R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec 1) R, euclideanCoordLaplacian u x = 0)
    (hr : 0 < r) (hrR : r < R) :
    HasDerivAt (fun s => sphereMean 0 s (fun x => u x ^ 2))
      (2 * (∫ x in euclideanBall (0 : Vec 1) r, vecNormSq (classicalGradient u x)) /
        (sphereArea 1 * r ^ (1 - 1))) r := by
  have hR : 0 < R := hr.trans hrR
  obtain ⟨a, b, hab⟩ := affine_of_harmonicOn_one hR hu hharm
  have hsub : euclideanBall (0 : Vec 1) r ⊆ euclideanBall (0 : Vec 1) R :=
    euclideanBall_mono hr.le hrR.le
  have hD : ∫ x in euclideanBall (0 : Vec 1) r, vecNormSq (classicalGradient u x) =
      ∫ x in euclideanBall (0 : Vec 1) r, b ^ 2 := by
    refine setIntegral_congr_fun (isOpen_euclideanBall 0 r).measurableSet fun x hx => ?_
    rw [vecNormSq_eq_sum_sq, Fin.sum_univ_one, (hab x (hsub hx)).2]
  rw [hD, energy_const_one _ _ hr, sphereArea_one]
  have hpoly : HasDerivAt (fun s : ℝ => a ^ 2 + b ^ 2 * s ^ 2) (2 * b ^ 2 * r) r := by
    have := ((hasDerivAt_pow 2 r).const_mul (b ^ 2)).const_add (a ^ 2)
    convert this using 1
    simp
    ring
  have hev : (fun s => sphereMean 0 s (fun x => u x ^ 2)) =ᶠ[𝓝 r]
      fun s : ℝ => a ^ 2 + b ^ 2 * s ^ 2 := by
    filter_upwards [Ioo_mem_nhds (show -R < r by linarith) hrR] with s hs
    obtain ⟨hp, hm⟩ := pm_mem_euclideanBall_one hR (s := s) (abs_lt.mpr hs)
    rw [sphereMean_one, (hab _ hp).1, (hab _ hm).1]
    simp [basisVec]
    ring
  refine (hpoly.congr_of_eventuallyEq hev).congr_deriv ?_
  simp

end

end PDE
