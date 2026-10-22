module

public import PDEFoundation.Analysis.HilbertBallAverageContinuity
public import PDEFoundation.Analysis.HilbertBallFluxOrigin
public import PDEFoundation.Analysis.HilbertHarmonicGrowth
public import PDEFoundation.PDE.HarmonicEnergySmooth

/-! # Exact quadratic oscillation decay for smooth harmonic functions -/

@[expose] public section

namespace PDE

open MeasureTheory Metric Set
open scoped Laplacian
open scoped InnerProductSpace

noncomputable section

variable {d : ℕ}

private theorem normalizedRadialIntegral_quadratic_decay_of_energy
    [NeZero d] {H A : ℝ → ℝ} (hH0 : H 0 = 0) (hH : Continuous H)
    (hA : Continuous A) {R : ℝ}
    (hHderiv : ∀ r ∈ Ioo (0 : ℝ) R,
      HasDerivAt H ((2 * r / d) * A r) r)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbR : b < R)
    (hAmono : MonotoneOn A (Ioc 0 b)) :
    (d : ℝ) / a ^ d * ∫ t in (0 : ℝ)..a, t ^ (d - 1) * H t ≤
      (a / b) ^ 2 *
        ((d : ℝ) / b ^ d * ∫ t in (0 : ℝ)..b, t ^ (d - 1) * H t) := by
  let G : ℝ → ℝ := fun r => (d : ℝ)⁻¹ *
    Internal.fixedScaleRadialAverage (d := 2) A r
  have hG : Continuous G := continuous_const.mul
    (Internal.continuous_fixedScaleRadialAverage A hA)
  have hratio := Internal.sphereProfile_div_sq_mono_of_hasDerivAt_energy
    hH0 hH hA hHderiv ha hab hbR hAmono
  have hfactor : ∀ r : ℝ, 0 < r → r ≤ b → H r = r ^ 2 * G r := by
    intro r hr hrb
    have hcont : ContinuousOn H (Icc 0 r) := hH.continuousOn
    have hderiv : ∀ s ∈ Ioo (0 : ℝ) r,
        HasDerivAt H ((2 / d) * (s * A s)) s := by
      intro s hs
      convert hHderiv s ⟨hs.1, (hs.2.trans_le hrb).trans hbR⟩ using 1
      ring
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (f := H) (f' := fun s => (2 / d) * (s * A s)) (a := 0) (b := r)
      hr.le hcont hderiv
      ((continuous_const.mul (continuous_id.mul hA)).intervalIntegrable 0 r)
    have hprimitive : H r = (2 / d) * ∫ s in (0 : ℝ)..r, s * A s := by
      change (∫ s in (0 : ℝ)..r, (2 / d) * (s * A s)) = H r - H 0 at hint
      rw [hH0, sub_zero, intervalIntegral.integral_const_mul] at hint
      exact hint.symm
    dsimp only [G]
    rw [hprimitive]
    rw [Internal.fixedScaleRadialAverage_eq_normalizedRadialIntegral A hr]
    norm_num
    field_simp
  have hGa : ∫ t in (0 : ℝ)..a, t ^ (d - 1) * H t =
      ∫ t in (0 : ℝ)..a, t ^ (d - 1) * (t ^ 2 * G t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    by_cases ht0 : t = 0
    · simp [ht0, hH0]
    · have ht' : t ∈ Ioc (0 : ℝ) a := by
        have htle : 0 ≤ t ∧ t ≤ a := by simpa [ha.le] using ht
        exact ⟨lt_of_le_of_ne htle.1 (Ne.symm ht0), htle.2⟩
      dsimp
      rw [hfactor t ht'.1 (ht'.2.trans hab)]
  have hGb : ∫ t in (0 : ℝ)..b, t ^ (d - 1) * H t =
      ∫ t in (0 : ℝ)..b, t ^ (d - 1) * (t ^ 2 * G t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    by_cases ht0 : t = 0
    · simp [ht0, hH0]
    · have ht' : t ∈ Ioc (0 : ℝ) b := by
        have htle : 0 ≤ t ∧ t ≤ b := by simpa [(ha.trans_le hab).le] using ht
        exact ⟨lt_of_le_of_ne htle.1 (Ne.symm ht0), htle.2⟩
      dsimp
      rw [hfactor t ht'.1 ht'.2]
  rw [hGa, hGb]
  apply Internal.normalizedRadialIntegral_quadratic_decay (d := d) hG ha hab
  intro r hr s hs hrs
  have hlocal := Internal.sphereProfile_div_sq_mono_of_hasDerivAt_energy
    hH0 hH hA hHderiv hr.1 hrs (hs.2.trans_lt hbR)
      (hAmono.mono (Ioc_subset_Ioc_right hs.2))
  rw [hfactor r hr.1 hr.2, hfactor s hs.1 hs.2] at hlocal
  field_simp [hr.1.ne', hs.1.ne'] at hlocal
  exact hlocal

/-- A smooth harmonic function vanishing at the center has exact quadratic
decay of its normalized squared oscillation on concentric round balls. -/
theorem integralAverage_sq_harmonic_decay [NeZero d] (hd : 2 ≤ d)
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {z : Vec d} {R a b : ℝ} (hR : 0 < R)
    (hharm : ∀ y ∈ euclideanBall z R, euclideanCoordLaplacian u y = 0)
    (huz : u z = 0) (ha : 0 < a) (hab : a ≤ b) (hbR : b < R) :
    integralAverage (euclideanBall z a) (fun y => u y ^ 2) ≤
      (a / b) ^ 2 * integralAverage (euclideanBall z b) (fun y => u y ^ 2) := by
  let v : HilbertVec d → ℝ := u ∘ Internal.toHilbert.symm
  let q : HilbertVec d → ℝ := fun y => v y ^ 2
  let e : HilbertVec d → ℝ := fun y =>
    vecNormSq (classicalGradient u (Internal.toHilbert.symm y))
  let H : ℝ → ℝ := fun r => Internal.sphereAverage (Internal.toHilbert z) r q
  let A : ℝ → ℝ := Internal.fixedScaleRadialAverage (d := d)
    (fun r => Internal.sphereAverage (Internal.toHilbert z) r e)
  have hv : ContDiff ℝ (⊤ : ℕ∞) v := hu.comp Internal.toHilbert.symm.contDiff
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := hv.pow 2
  have he : Continuous e := by
    have h1 : (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) :=
      WithTop.coe_le_coe.mpr le_top
    exact continuous_vecNormSq.comp
      ((PDE.ContDiff.continuous_classicalGradient
        (hu.of_le h1)).comp
          Internal.toHilbert.symm.continuous)
  have hA : Continuous A := Internal.continuous_fixedScaleRadialAverage _
    (Internal.continuous_sphereAverage he (Internal.toHilbert z))
  have hAeq : ∀ r : ℝ, 0 < r →
      A r = integralAverage (euclideanBall z r)
        (fun y => vecNormSq (classicalGradient u y)) := by
    intro r hr
    rw [integralAverage_euclideanBall_eq_hilbert _ z hr]
    dsimp only [A]
    rw [Internal.fixedScaleRadialAverage_eq_normalizedRadialIntegral _ hr]
    rw [← Internal.normalizedIntegral_metricBall_eq_radialSphereAverage he
      (Internal.toHilbert z) hr]
  have hAmono : MonotoneOn A (Ioc 0 b) := by
    intro r hr s hs hrs
    rw [hAeq r hr.1, hAeq s hs.1]
    exact integralAverage_vecNormSq_classicalGradient_mono hu hR hharm
      hr.1 hrs (hs.2.trans_lt hbR)
  have hH : Continuous H := Internal.continuous_sphereAverage hq.continuous _
  have hH0 : H 0 = 0 := by simp [H, q, v, huz]
  have hHderiv : ∀ r ∈ Ioo (0 : ℝ) R,
      HasDerivAt H ((2 * r / d) * A r) r := by
    intro r hrange
    have h2 : (2 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) :=
      WithTop.coe_le_coe.mpr le_top
    have hgreen :=
      Internal.hasDerivAt_sphereAverage_eq_r_div_dim_mul_ballAverage_laplacian_of_two_le
        hd (hq.of_le h2)
          (Internal.toHilbert z) hrange.1 hrange.2
    dsimp only [H]
    convert hgreen using 1
    rw [hAeq r hrange.1, integralAverage_euclideanBall_eq_hilbert _ z hrange.1]
    have hlap : ∀ y ∈ Metric.ball (Internal.toHilbert z) r, Δ q y = 2 * e y := by
      intro y hy
      have hyn : Internal.toHilbert.symm y ∈ euclideanBall z R := by
        rw [← Internal.preimage_ball_toHilbert z hR]
        exact Metric.ball_subset_ball (le_of_lt hrange.2) hy
      change Δ ((fun x => u x ^ 2) ∘ Internal.toHilbert.symm) y = _
      rw [← Internal.euclideanCoordLaplacian_eq_laplacian_comp_toHilbert_symm
        ((hu.pow 2).of_le h2)]
      rw [euclideanCoordLaplacian_sq hu, hharm _ hyn, mul_zero, add_zero]
      simp [e, vecNormSq, vecDot, classicalGradient, euclideanCoordDeriv, pow_two]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_ball hlap]
    rw [MeasureTheory.integral_const_mul]
    ring
  have hradial := normalizedRadialIntegral_quadratic_decay_of_energy
    hH0 hH hA hHderiv ha hab hbR hAmono
  rw [integralAverage_euclideanBall_eq_hilbert _ z ha,
    integralAverage_euclideanBall_eq_hilbert _ z (ha.trans_le hab)]
  change (volume (Metric.ball (Internal.toHilbert z) a)).toReal⁻¹ *
      ∫ y in Metric.ball (Internal.toHilbert z) a, q y ≤
    (a / b) ^ 2 * ((volume (Metric.ball (Internal.toHilbert z) b)).toReal⁻¹ *
      ∫ y in Metric.ball (Internal.toHilbert z) b, q y)
  rw [Internal.normalizedIntegral_metricBall_eq_radialSphereAverage hq.continuous _ ha,
    Internal.normalizedIntegral_metricBall_eq_radialSphereAverage hq.continuous _
      (ha.trans_le hab)]
  exact hradial

end

end PDE
