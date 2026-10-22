module

public import PDEFoundation.Monotonicity.Core.FrequencyDerivsLocal
public import PDEFoundation.Analysis.HilbertBallFluxOrigin
public import PDEFoundation.PDE.HarmonicBochner

/-!
# Chapter 2 frequency derivatives: the globally smooth case, `d ≥ 2`

For a globally `C^∞` function `v` which is harmonic on `B_ρ`, the flux of `∇(v²)` through `∂B_r`
equals `2 ∫_{B_r} |∇v|²`, giving the radial derivative of the sphere mean of `v²` and the
identity `D(r) = r⁻¹ ∫_{∂B_r} v (x · ∇v)`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology Laplacian

namespace PDE

noncomputable section

variable {d : ℕ}

theorem zero_toHilbertVec : (0 : Vec d).toHilbertVec = 0 := by
  ext i; simp [Vec.toHilbertVec_apply]

/-- The Green identity for the square of a globally smooth function, harmonic on a ball. -/
theorem weighted_sphereFlux_sq_eq [NeZero d] (hd : 2 ≤ d) {v : Vec d → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (hrρ : r < ρ)
    (hharm : ∀ y ∈ euclideanBall (0 : Vec d) ρ, euclideanCoordLaplacian v y = 0) :
    r ^ (d - 1) * Internal.sphereFlux (0 : HilbertVec d) r (fun y => v y.toVec ^ 2) =
      2 * ∫ x in euclideanBall (0 : Vec d) r, vecNormSq (classicalGradient v x) := by
  have h2 : (2 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
  have hq : ContDiff ℝ 2 (fun y : HilbertVec d => v y.toVec ^ 2) :=
    ((hv.pow 2).of_le h2).comp Internal.toHilbert.symm.contDiff
  have hflux := Internal.weightedSphereFlux_eq_integral_ball_laplacian_of_two_le hd hq
    (0 : HilbertVec d) (R := r + 1) hr (by linarith)
  rw [hflux]
  have hlap : ∀ y ∈ Metric.ball (0 : HilbertVec d) r,
      Δ (fun y : HilbertVec d => v y.toVec ^ 2) y =
        2 * vecNormSq (classicalGradient v y.toVec) := by
    intro y hy
    have hyn : Internal.toHilbert.symm y ∈ euclideanBall (0 : Vec d) ρ := by
      rw [← Internal.preimage_ball_toHilbert (0 : Vec d) hρ]
      have : y ∈ Metric.ball (Internal.toHilbert (0 : Vec d)) ρ := by
        have h0 : Internal.toHilbert (0 : Vec d) = 0 := zero_toHilbertVec
        rw [h0]
        exact Metric.ball_subset_ball hrρ.le hy
      simpa using this
    change Δ ((fun x => v x ^ 2) ∘ Internal.toHilbert.symm) y = _
    rw [← Internal.euclideanCoordLaplacian_eq_laplacian_comp_toHilbert_symm
      ((hv.pow 2).of_le h2)]
    rw [euclideanCoordLaplacian_sq hv, hharm _ hyn, mul_zero, add_zero]
    simp [vecNormSq, vecDot, classicalGradient, euclideanCoordDeriv, pow_two]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_ball hlap,
    MeasureTheory.integral_const_mul,
    integral_euclideanBall_eq_hilbert (fun x => vecNormSq (classicalGradient v x)) 0 hr,
    zero_toHilbertVec]

/-- Fréchet derivative of the squared function on the Hilbert side. -/
theorem fderiv_sq_comp_toVec {v : Vec d → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) (y w : HilbertVec d) :
    fderiv ℝ (fun y : HilbertVec d => v y.toVec ^ 2) y w =
      2 * v y.toVec * fderiv ℝ v y.toVec w.toVec := by
  have hvd : DifferentiableAt ℝ v y.toVec :=
    (hv.differentiable (by simp)) _
  have h1 : HasFDerivAt (fun x => v x ^ 2) ((2 * v y.toVec) • fderiv ℝ v y.toVec) y.toVec := by
    have := hvd.hasFDerivAt.pow 2
    simpa using this
  have h2 : HasFDerivAt (fun y : HilbertVec d => v y.toVec ^ 2)
      (((2 * v y.toVec) • fderiv ℝ v y.toVec).comp
        (Internal.toHilbert.symm : HilbertVec d ≃L[ℝ] Vec d).toContinuousLinearMap) y := by
    have h3 : HasFDerivAt (fun y : HilbertVec d => y.toVec)
        (Internal.toHilbert.symm : HilbertVec d ≃L[ℝ] Vec d).toContinuousLinearMap y :=
      Internal.toHilbert.symm.hasFDerivAt
    exact h1.comp y h3
  rw [h2.fderiv]
  simp

/-- `D(r) = r⁻¹ ∫_{∂B_r} v (x · ∇v)` for globally smooth `v` harmonic on a ball, `d ≥ 2`. -/
theorem energy_eq_inv_mul_sphereIntegral_global [NeZero d] (hd : 2 ≤ d) {v : Vec d → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (hrρ : r < ρ)
    (hharm : ∀ y ∈ euclideanBall (0 : Vec d) ρ, euclideanCoordLaplacian v y = 0) :
    ∫ x in euclideanBall (0 : Vec d) r, vecNormSq (classicalGradient v x) =
      r⁻¹ * sphereIntegral 0 r (fun x => v x * vecDot x (classicalGradient v x)) := by
  have hG := weighted_sphereFlux_sq_eq hd hv hρ hr hrρ hharm
  have hpt : ∀ ω : Metric.sphere (0 : HilbertVec d) 1,
      v ((0 : Vec d) + r • (ω : HilbertVec d).toVec) *
          vecDot ((0 : Vec d) + r • (ω : HilbertVec d).toVec)
            (classicalGradient v ((0 : Vec d) + r • (ω : HilbertVec d).toVec)) =
        (r / 2) * fderiv ℝ (fun y : HilbertVec d => v y.toVec ^ 2)
          ((0 : HilbertVec d) + r • (ω : HilbertVec d)) (ω : HilbertVec d) := by
    intro ω
    have e1 : (0 : Vec d) + r • (ω : HilbertVec d).toVec =
        ((0 : HilbertVec d) + r • (ω : HilbertVec d)).toVec := by
      ext i; simp [HilbertVec.toVec_apply]
    rw [e1, fderiv_sq_comp_toVec hv, vecDot_comm, ← fderiv_apply_eq_vecDot_classicalGradient]
    have e2 : ((0 : HilbertVec d) + r • (ω : HilbertVec d)).toVec =
        r • (ω : HilbertVec d).toVec := by
      ext i; simp [HilbertVec.toVec_apply]
    rw [e2, map_smul, smul_eq_mul]
    ring
  unfold sphereIntegral
  simp_rw [hpt]
  rw [integral_const_mul]
  have hflux : Internal.sphereFlux (0 : HilbertVec d) r (fun y => v y.toVec ^ 2) =
      ∫ ω : Metric.sphere (0 : HilbertVec d) 1,
        fderiv ℝ (fun y : HilbertVec d => v y.toVec ^ 2)
          ((0 : HilbertVec d) + r • (ω : HilbertVec d)) (ω : HilbertVec d)
          ∂((volume : Measure (HilbertVec d)).toSphere) := rfl
  rw [← hflux]
  have hr0 : r ≠ 0 := hr.ne'
  have : r ^ (d - 1) * (r / 2 * Internal.sphereFlux (0 : HilbertVec d) r
      (fun y => v y.toVec ^ 2)) = r / 2 * (r ^ (d - 1) * Internal.sphereFlux (0 : HilbertVec d) r
      (fun y => v y.toVec ^ 2)) := by ring
  rw [this, hG]
  field_simp

/-- Radial derivative of the sphere mean of `v²`, `d ≥ 2`. -/
theorem hasDerivAt_sphereMean_sq_global [NeZero d] (hd : 2 ≤ d) {v : Vec d → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (hrρ : r < ρ)
    (hharm : ∀ y ∈ euclideanBall (0 : Vec d) ρ, euclideanCoordLaplacian v y = 0) :
    HasDerivAt (fun s => sphereMean 0 s (fun x => v x ^ 2))
      (2 * (∫ x in euclideanBall (0 : Vec d) r, vecNormSq (classicalGradient v x)) /
        (sphereArea d * r ^ (d - 1))) r := by
  have h1 : (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
  have hq : ContDiff ℝ 1 (fun y : HilbertVec d => v y.toVec ^ 2) :=
    ((hv.pow 2).of_le h1).comp Internal.toHilbert.symm.contDiff
  have hder := Internal.hasDerivAt_sphereAverage hq (0 : HilbertVec d) r
  have hfun : (fun s => sphereMean 0 s (fun x => v x ^ 2)) =
      fun s => Internal.sphereAverage (0 : HilbertVec d) s (fun y => v y.toVec ^ 2) := by
    funext s
    rw [sphereMean_eq_sphereAverage, zero_toHilbertVec]
  rw [hfun]
  convert hder using 1
  have hG := weighted_sphereFlux_sq_eq hd hv hρ hr hrρ hharm
  rw [← Internal.sphereFlux_def, smul_eq_mul]
  have hσ : sphereArea d ≠ 0 := sphereArea_ne_zero
  have hrp : r ^ (d - 1) ≠ 0 := pow_ne_zero _ hr.ne'
  have hfl : Internal.sphereFlux (0 : HilbertVec d) r (fun y => v y.toVec ^ 2) =
      2 * (∫ x in euclideanBall (0 : Vec d) r, vecNormSq (classicalGradient v x)) /
        r ^ (d - 1) := by
    rw [eq_div_iff hrp, mul_comm]; exact hG
  rw [hfl]
  unfold sphereArea
  field_simp

end

end PDE
