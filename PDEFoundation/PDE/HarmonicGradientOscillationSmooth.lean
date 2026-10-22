module

public import PDEFoundation.PDE.HarmonicOscillationSmooth
public import PDEFoundation.Sobolev.H1.VectorMeanOscillation

/-! # Exact centered gradient decay for smooth harmonic functions -/

@[expose] public section

namespace PDE

open MeasureTheory Metric Set
open scoped Laplacian
open scoped InnerProductSpace ENNReal

noncomputable section

variable {d : ℕ}

/-- The normalized ball average of a smooth harmonic function is its value at
the center. This is derived from the ball flux identity. -/
theorem integralAverage_euclideanBall_eq_center_of_harmonic [NeZero d]
    (hd : 2 ≤ d) {v : Vec d → ℝ} (hv : ContDiff ℝ 2 v)
    {z : Vec d} {R r : ℝ} (hR : 0 < R)
    (hharm : ∀ y ∈ euclideanBall z R, euclideanCoordLaplacian v y = 0)
    (hr : 0 < r) (hrR : r < R) :
    integralAverage (euclideanBall z r) v = v z := by
  let w : HilbertVec d → ℝ := v ∘ Internal.toHilbert.symm
  have hw : ContDiff ℝ 2 w := hv.comp Internal.toHilbert.symm.contDiff
  have hflux : ∀ s ∈ Ioo (0 : ℝ) R,
      Internal.sphereFlux (Internal.toHilbert z) s w = 0 := by
    intro s hs
    have hgreen := Internal.weightedSphereFlux_eq_integral_ball_laplacian_of_two_le
      hd hw (Internal.toHilbert z) hs.1 hs.2
    have hlap : ∀ y ∈ Metric.ball (Internal.toHilbert z) s, Δ w y = 0 := by
      intro y hy
      rw [← Internal.euclideanCoordLaplacian_eq_laplacian_comp_toHilbert_symm hv]
      apply hharm
      rw [← Internal.preimage_ball_toHilbert z hR]
      exact Metric.ball_subset_ball (le_of_lt hs.2) hy
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_ball hlap] at hgreen
    simp only [integral_zero] at hgreen
    exact (mul_eq_zero.mp hgreen).resolve_left
      (pow_ne_zero _ (ne_of_gt hs.1))
  have hsphere : ∀ s ∈ Ico (0 : ℝ) R,
      Internal.sphereAverage (Internal.toHilbert z) s w = w (Internal.toHilbert z) :=
    Internal.sphereAverage_eq_center_of_flux_zero (hw.of_le (by norm_num)) _ hflux
  rw [integralAverage_euclideanBall_eq_hilbert v z hr]
  change (volume (Metric.ball (Internal.toHilbert z) r)).toReal⁻¹ *
    ∫ y in Metric.ball (Internal.toHilbert z) r, w y = v z
  rw [Internal.normalizedIntegral_metricBall_eq_radialSphereAverage hw.continuous _ hr]
  have hsphere' : ∀ s ∈ Ioc (0 : ℝ) r,
      Internal.sphereAverage (Internal.toHilbert z) s w = v z := by
    intro s hs
    simpa only [w, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply] using
      hsphere s ⟨hs.1.le, hs.2.trans_lt hrR⟩
  have hcongr : (∫ s in (0 : ℝ)..r, s ^ (d - 1) *
      Internal.sphereAverage (Internal.toHilbert z) s w) =
      ∫ s in (0 : ℝ)..r, s ^ (d - 1) * v z := by
    apply intervalIntegral.integral_congr
    intro s hs
    by_cases hs0 : s = 0
    · have hdsub : d - 1 ≠ 0 := by omega
      simp [hs0, hdsub, w]
    · have hsle : 0 ≤ s ∧ s ≤ r := by simpa [hr.le] using hs
      dsimp
      have heq := hsphere' s ⟨lt_of_le_of_ne hsle.1 (Ne.symm hs0), hsle.2⟩
      simpa only [Internal.toHilbert_apply] using congrArg (fun c => s ^ (d - 1) * c) heq
  rw [hcongr, intervalIntegral.integral_mul_const, integral_pow]
  have hd1 : 1 ≤ d := by omega
  simp only [zero_pow (NeZero.ne d), Nat.sub_add_cancel hd1,
    Nat.cast_sub hd1, Nat.cast_one]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hr0 : r ≠ 0 := hr.ne'
  field_simp
  field_simp [hd0]
  ring

/-- Exact linear decay of the centered gradient mean oscillation for a smooth
harmonic function. -/
theorem centeredVectorMeanL2_classicalGradient_harmonic_decay [NeZero d]
    (hd : 2 ≤ d) {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {z : Vec d} {R a b : ℝ} (hR : 0 < R)
    (hharm : ∀ y ∈ euclideanBall z R, euclideanCoordLaplacian u y = 0)
    (ha : 0 < a) (hab : a ≤ b) (hbR : b < R) :
    centeredVectorMeanL2 (euclideanBall z a) (classicalGradient u) ≤
      (a / b) * centeredVectorMeanL2 (euclideanBall z b) (classicalGradient u) := by
  let g : Vec d → Vec d := classicalGradient u
  have hmean : ∀ r : ℝ, 0 < r → r < R →
      vectorIntegralAverage (euclideanBall z r) g = g z := by
    intro r hr hrR
    funext i
    rw [vectorIntegralAverage_apply]
    have h2 : (2 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) :=
      WithTop.coe_le_coe.mpr le_top
    exact integralAverage_euclideanBall_eq_center_of_harmonic hd
      ((contDiff_euclideanCoordDeriv hu i).of_le h2) hR
      (fun y hy => euclideanCoordLaplacian_euclideanCoordDeriv_eq_zero
        hu (isOpen_euclideanBall z R) hharm hy i) hr hrR
  have hcoord : ∀ i : Fin d,
      integralAverage (euclideanBall z a) (fun x => (g x i - g z i) ^ 2) ≤
        (a / b) ^ 2 * integralAverage (euclideanBall z b)
          (fun x => (g x i - g z i) ^ 2) := by
    intro i
    let vi : Vec d → ℝ := fun x => euclideanCoordDeriv i u x - euclideanCoordDeriv i u z
    have hvi : ContDiff ℝ (⊤ : ℕ∞) vi :=
      (contDiff_euclideanCoordDeriv hu i).sub contDiff_const
    have hviharm : ∀ y ∈ euclideanBall z R, euclideanCoordLaplacian vi y = 0 := by
      intro y hy
      have hbase := euclideanCoordLaplacian_euclideanCoordDeriv_eq_zero
        hu (isOpen_euclideanBall z R) hharm hy i
      have hfirst : ∀ j : Fin d, euclideanCoordDeriv j vi =
          euclideanCoordDeriv j (euclideanCoordDeriv i u) := by
        intro j
        funext x
        dsimp only [vi]
        unfold euclideanCoordDeriv
        rw [show (fun y => (fderiv ℝ u y) (basisVec i) -
            (fderiv ℝ u z) (basisVec i)) =
          (fun y => (fderiv ℝ u y) (basisVec i)) -
            (fun _ => (fderiv ℝ u z) (basisVec i)) by rfl]
        rw [fderiv_sub]
        · simp
        · exact ((contDiff_euclideanCoordDeriv hu i).differentiable (by simp) x)
        · exact differentiableAt_const _
      unfold euclideanCoordLaplacian at hbase ⊢
      simp_rw [euclideanCoordSecondDeriv, hfirst]
      exact hbase
    simpa only [g, classicalGradient, euclideanCoordDeriv] using!
      integralAverage_sq_harmonic_decay hd hvi hR hviharm (by simp [vi]) ha hab hbR
  have henergy : integralAverage (euclideanBall z a) (fun x => vecNormSq (g x - g z)) ≤
      (a / b) ^ 2 * integralAverage (euclideanBall z b)
        (fun x => vecNormSq (g x - g z)) := by
    have hint : ∀ r : ℝ, 0 < r → ∀ i : Fin d,
        IntegrableOn (fun x => (g x i - g z i) ^ 2) (euclideanBall z r) := by
      intro r hr i
      have hc : Continuous (fun x => (g x i - g z i) ^ 2) := by
        have hcg := PDE.ContDiff.continuous_classicalGradient
          (hu.of_le (WithTop.coe_le_coe.mpr le_top :
            (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞)))
        exact (((continuous_apply i).comp hcg).sub continuous_const).pow 2
      exact (hc.continuousOn.integrableOn_compact
        (isCompact_euclideanClosedBall z hr.le)).mono_set
          (euclideanBall_subset_euclideanClosedBall z r)
    have hdecomp : ∀ r : ℝ, 0 < r →
        integralAverage (euclideanBall z r) (fun x => vecNormSq (g x - g z)) =
          ∑ i : Fin d, integralAverage (euclideanBall z r)
            (fun x => (g x i - g z i) ^ 2) := by
      intro r hr
      unfold integralAverage
      simp_rw [vecNormSq, vecDot, Pi.sub_apply, ← pow_two]
      rw [integral_finsetSum Finset.univ (fun i _ => hint r hr i), Finset.mul_sum]
    rw [hdecomp a ha, hdecomp b (ha.trans_le hab), Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hcoord i
  unfold centeredVectorMeanL2
  rw [hmean a ha (hab.trans_lt hbR), hmean b (ha.trans_le hab) hbR]
  have hsqrt := Real.sqrt_le_sqrt henergy
  rw [Real.sqrt_mul (sq_nonneg (a / b)), Real.sqrt_sq_eq_abs,
    abs_of_pos (div_pos ha (ha.trans_le hab))] at hsqrt
  exact hsqrt

end

end PDE
