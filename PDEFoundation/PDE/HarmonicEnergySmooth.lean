module

public import PDEFoundation.Analysis.HilbertBallAverage
public import PDEFoundation.Analysis.HilbertDictionary
public import PDEFoundation.PDE.HarmonicBochner
public import PDEFoundation.Sobolev.Mean

/-! # Exact native ball comparison for smooth harmonic gradients -/

@[expose] public section

namespace PDE

open MeasureTheory Metric
open scoped InnerProductSpace

noncomputable section

variable {d : ℕ}

/-- Exact normalized-integral dictionary, with no dimension factor. -/
theorem integralAverage_euclideanBall_eq_hilbert
    (f : Vec d → ℝ) (z : Vec d) {r : ℝ} (hr : 0 < r) :
    integralAverage (euclideanBall z r) f =
      (volume (Metric.ball (Internal.toHilbert z) r)).toReal⁻¹ *
        ∫ y in Metric.ball (Internal.toHilbert z) r,
          f (Internal.toHilbert.symm y) := by
  have hpre := Internal.preimage_ball_toHilbert z hr
  have hvol : volume (euclideanBall z r) =
      volume (Metric.ball (Internal.toHilbert z) r) := by
    rw [← hpre]
    exact Internal.measurePreserving_toHilbert.measure_preimage
      measurableSet_ball.nullMeasurableSet
  have hint : ∫ x in euclideanBall z r, f x =
      ∫ y in Metric.ball (Internal.toHilbert z) r,
        f (Internal.toHilbert.symm y) := by
    rw [← hpre]
    have h := Internal.measurePreserving_toHilbert.setIntegral_preimage_emb
      Internal.toHilbert.toHomeomorph.measurableEmbedding
      (fun y : HilbertVec d => f (Internal.toHilbert.symm y))
      (Metric.ball (Internal.toHilbert z) r)
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using h
  unfold integralAverage
  rw [hvol, hint]

/-- Exact ball-average monotonicity for native smooth subharmonic functions. -/
theorem integralAverage_euclideanBall_mono_of_laplacian_nonneg [NeZero d]
    {f : Vec d → ℝ} (hf : ContDiff ℝ 2 f) {z : Vec d} {R : ℝ}
    (hR : 0 < R)
    (hlap : ∀ y ∈ euclideanBall z R, 0 ≤ euclideanCoordLaplacian f y)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbR : b < R) :
    integralAverage (euclideanBall z a) f ≤
      integralAverage (euclideanBall z b) f := by
  rw [integralAverage_euclideanBall_eq_hilbert f z ha,
    integralAverage_euclideanBall_eq_hilbert f z (ha.trans_le hab)]
  apply Internal.normalizedIntegral_metricBall_mono_of_laplacian_nonneg
    (hf.comp Internal.toHilbert.symm.contDiff) _ ha hab hbR
  intro y hy
  rw [← Internal.euclideanCoordLaplacian_eq_laplacian_comp_toHilbert_symm hf]
  apply hlap
  have hpre := Internal.preimage_ball_toHilbert z hR
  rw [← hpre]
  simpa only [Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using hy

/-- Exact comparison for each squared coordinate of a smooth harmonic gradient. -/
theorem integralAverage_sq_coordDeriv_mono [NeZero d]
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {z : Vec d} {R : ℝ} (hR : 0 < R)
    (hharm : ∀ y ∈ euclideanBall z R, euclideanCoordLaplacian u y = 0)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbR : b < R) (i : Fin d) :
    integralAverage (euclideanBall z a) (fun x => euclideanCoordDeriv i u x ^ 2) ≤
      integralAverage (euclideanBall z b) (fun x => euclideanCoordDeriv i u x ^ 2) := by
  apply integralAverage_euclideanBall_mono_of_laplacian_nonneg
    (((contDiff_euclideanCoordDeriv hu i).pow 2).of_le (by norm_cast)) hR _ ha hab hbR
  intro y hy
  exact euclideanCoordLaplacian_sq_euclideanCoordDeriv_nonneg hu
    (isOpen_euclideanBall z R) hharm hy i

/-- The exact constant-one normalized gradient energy comparison on concentric
round balls for a smooth harmonic function. -/
theorem integralAverage_vecNormSq_classicalGradient_mono [NeZero d]
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {z : Vec d} {R : ℝ} (hR : 0 < R)
    (hharm : ∀ y ∈ euclideanBall z R, euclideanCoordLaplacian u y = 0)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbR : b < R) :
    integralAverage (euclideanBall z a) (fun x => vecNormSq (classicalGradient u x)) ≤
      integralAverage (euclideanBall z b) (fun x => vecNormSq (classicalGradient u x)) := by
  let q : Fin d → Vec d → ℝ := fun i x => euclideanCoordDeriv i u x ^ 2
  have hqint : ∀ i : Fin d, ∀ t : ℝ, 0 < t → IntegrableOn (q i) (euclideanBall z t) := by
    intro i t ht
    have hqcont : Continuous (q i) := ((contDiff_euclideanCoordDeriv hu i).pow 2).continuous
    exact (hqcont.continuousOn.integrableOn_compact
      (isCompact_euclideanClosedBall z ht.le)).mono_set
        (euclideanBall_subset_euclideanClosedBall z t)
  have hpoint : ∀ x : Vec d, vecNormSq (classicalGradient u x) = ∑ i : Fin d, q i x := by
    intro x
    simp only [q, vecNormSq, vecDot, classicalGradient, euclideanCoordDeriv, pow_two]
  have hsum : ∑ i : Fin d, integralAverage (euclideanBall z a) (q i) ≤
      ∑ i : Fin d, integralAverage (euclideanBall z b) (q i) := by
    apply Finset.sum_le_sum
    intro i _
    exact integralAverage_sq_coordDeriv_mono hu hR hharm ha hab hbR i
  simp only [integralAverage] at hsum ⊢
  simp_rw [hpoint]
  rw [integral_finsetSum Finset.univ (fun i _ => hqint i a ha),
    integral_finsetSum Finset.univ (fun i _ => hqint i b (ha.trans_le hab)),
    Finset.mul_sum, Finset.mul_sum]
  exact hsum

end

end PDE
