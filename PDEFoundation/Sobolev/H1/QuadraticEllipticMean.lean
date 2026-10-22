module

public import PDEFoundation.Measure.LinearAverage
public import PDEFoundation.Measure.LinearNormalizedVolume
public import PDEFoundation.Sobolev.H1.QuadraticEllipticGradient
public import PDEFoundation.Sobolev.W1p.EuclideanGradient

/-! # Normalized gradient bounds under quadratic elliptic normalization -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

namespace H1Function

/-- The normalized Euclidean gradient energy grows by at most `sqrt Lam`
under quadratic elliptic normalization. -/
theorem sqrt_integralAverage_comp_quadraticEllipticNormalizer_grad_le
    {A0 : Mat d} {Lam : ℝ} (hLam : 1 ≤ Lam)
    (hLower : ∀ xi : Vec d,
      vecNormSq xi ≤ vecDot xi (matVecMul A0 xi))
    (hUpper : ∀ xi : Vec d,
      vecDot xi (matVecMul (symmPart A0) xi) ≤ Lam * vecNormSq xi)
    (u : H1Function U) (hUPos : 0 < volume U) (hUTop : volume U < ∞) :
    Real.sqrt (integralAverage
      (quadraticEllipticNormalizerContinuousLinearEquiv hLower '' U)
      (fun y => vecNormSq
        ((u.compLinearEquiv
          (quadraticEllipticNormalizerContinuousLinearEquiv hLower)).grad y))) ≤
      Real.sqrt Lam *
        Real.sqrt (integralAverage U (fun x => vecNormSq (u.grad x))) := by
  let e := quadraticEllipticNormalizerContinuousLinearEquiv hLower
  let v := u.compLinearEquiv e
  have hpoint (x : Vec d) :
      vecNormSq (v.grad (e x)) ≤
        (Real.sqrt Lam) ^ 2 * vecNormSq (u.grad x) := by
    have hn := vecEuclideanNorm_comp_quadraticEllipticNormalizer_grad_le
      hLam hLower hUpper u (e x)
    simp only [e, ContinuousLinearEquiv.symm_apply_apply] at hn
    rw [← vecEuclideanNorm_sq, ← vecEuclideanNorm_sq]
    have hp := pow_le_pow_left₀ (vecEuclideanNorm_nonneg _) hn 2
    simpa only [e, v, mul_pow] using hp
  have hvcomp : MemVectorL2On U (fun x => v.grad (e x)) := by
    intro i
    exact memLpOn_comp_linearEquiv e (v.gradMemL2 i)
  have hint :
      (∫ x in U, vecNormSq (v.grad (e x))) ≤
        ∫ x in U, (Real.sqrt Lam) ^ 2 * vecNormSq (u.grad x) :=
    integral_mono_ae
      (integrableOn_vecNormSq_of_memVectorL2On hvcomp)
      ((integrableOn_vecNormSq_of_memVectorL2On u.gradMemL2).const_mul _)
      (Filter.Eventually.of_forall hpoint)
  have havg :
      integralAverage U (fun x => vecNormSq (v.grad (e x))) ≤
        (Real.sqrt Lam) ^ 2 *
          integralAverage U (fun x => vecNormSq (u.grad x)) := by
    unfold integralAverage
    calc
      (volume U).toReal⁻¹ * ∫ x in U, vecNormSq (v.grad (e x)) ≤
          (volume U).toReal⁻¹ *
            ∫ x in U, (Real.sqrt Lam) ^ 2 * vecNormSq (u.grad x) :=
        mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr ENNReal.toReal_nonneg)
      _ = (Real.sqrt Lam) ^ 2 *
          ((volume U).toReal⁻¹ * ∫ x in U, vecNormSq (u.grad x)) := by
        rw [integral_const_mul]
        ring
  rw [← integralAverage_comp_linearEquiv e hUPos hUTop
    (fun y => vecNormSq (v.grad y))]
  have hsqrt := Real.sqrt_le_sqrt havg
  calc
    Real.sqrt (integralAverage U (fun x => vecNormSq (v.grad (e x)))) ≤
        Real.sqrt ((Real.sqrt Lam) ^ 2 *
          integralAverage U (fun x => vecNormSq (u.grad x))) := hsqrt
    _ = Real.sqrt Lam *
        Real.sqrt (integralAverage U (fun x => vecNormSq (u.grad x))) := by
      rw [Real.sqrt_mul (sq_nonneg (Real.sqrt Lam)), Real.sqrt_sq_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg Lam)]

/-- If the quadratically normalized gradient belongs to raw `Lᵖ`, then the
original gradient does as well, and its guarded normalized Euclidean norm is
no larger. -/
theorem exists_grad_memLp_and_lpMeanNorm_le_comp_quadraticEllipticNormalizer
    {A0 : Mat d}
    (hLower : ∀ xi : Vec d,
      vecNormSq xi ≤ vecDot xi (matVecMul A0 xi))
    (u : H1Function U) (hUPos : 0 < volume U) (hUTop : volume U < ∞)
    (p : ENNReal)
    (hNormalized : MemLp
      (fun y => vecEuclideanNorm
        ((u.compLinearEquiv
          (quadraticEllipticNormalizerContinuousLinearEquiv hLower)).grad y))
      p (volumeOn
        (quadraticEllipticNormalizerContinuousLinearEquiv hLower '' U))) :
    ∃ hGrad : MemLp (fun x => vecEuclideanNorm (u.grad x)) p (volumeOn U),
      euclideanFieldLpMeanNormOn U p u.grad
          (memLp_normalizedVolumeOn_of_memLpOn hGrad hUPos) ≤
        euclideanFieldLpMeanNormOn
          (quadraticEllipticNormalizerContinuousLinearEquiv hLower '' U) p
          (u.compLinearEquiv
            (quadraticEllipticNormalizerContinuousLinearEquiv hLower)).grad
          (memLp_normalizedVolumeOn_of_memLpOn hNormalized
            (volume_image_linearEquiv_pos
              (quadraticEllipticNormalizerContinuousLinearEquiv hLower) hUPos)) := by
  let e := quadraticEllipticNormalizerContinuousLinearEquiv hLower
  let v := u.compLinearEquiv e
  let X := e '' U
  have hXPos : 0 < volume X := volume_image_linearEquiv_pos e hUPos
  have hXTop : volume X < ∞ := volume_image_linearEquiv_lt_top e hUTop
  have hNormalizedMean :=
    memLp_normalizedVolumeOn_of_memLpOn hNormalized hXPos
  have hForward := measurePreserving_linearEquiv_normalizedVolumeOn e U
  have hPull : MemLp (fun x => vecEuclideanNorm (v.grad (e x))) p
      (normalizedVolumeOn U) := by
    simpa only [Function.comp_apply] using!
      hNormalizedMean.comp_measurePreserving hForward
  have hGradMeas : AEStronglyMeasurable
      (fun x => vecEuclideanNorm (u.grad x)) (normalizedVolumeOn U) :=
    (memLp_normalizedVolumeOn_of_memLpOn
      u.gradMemL2.memLp_vecEuclideanNorm hUPos).aestronglyMeasurable
  have hGradMean : MemLp (fun x => vecEuclideanNorm (u.grad x)) p
      (normalizedVolumeOn U) := by
    apply hPull.of_le hGradMeas
    filter_upwards with x
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (vecEuclideanNorm_nonneg (u.grad x)),
      abs_of_nonneg (vecEuclideanNorm_nonneg (v.grad (e x)))] using
      vecEuclideanNorm_grad_le_comp_quadraticEllipticNormalizer_grad
        hLower u x
  have hGradRaw : MemLp (fun x => vecEuclideanNorm (u.grad x)) p
      (volumeOn U) := by
    rw [← volume_smul_normalizedVolumeOn_eq_volumeOn hUPos hUTop]
    exact hGradMean.smul_measure hUTop.ne
  refine ⟨hGradRaw, ?_⟩
  change (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) p
      (normalizedVolumeOn U)).toReal ≤
    (eLpNorm (fun y => vecEuclideanNorm (v.grad y)) p
      (normalizedVolumeOn X)).toReal
  apply ENNReal.toReal_mono hNormalizedMean.eLpNorm_ne_top
  have hmono : eLpNorm (fun x => vecEuclideanNorm (u.grad x)) p
      (normalizedVolumeOn U) ≤
      eLpNorm (fun x => vecEuclideanNorm (v.grad (e x))) p
        (normalizedVolumeOn U) := by
    apply eLpNorm_mono_ae hGradMeas
    filter_upwards with x
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (vecEuclideanNorm_nonneg (u.grad x)),
      abs_of_nonneg (vecEuclideanNorm_nonneg (v.grad (e x)))] using
      vecEuclideanNorm_grad_le_comp_quadraticEllipticNormalizer_grad
        hLower u x
  have hpullNorm : eLpNorm (fun x => vecEuclideanNorm (v.grad (e x))) p
      (normalizedVolumeOn U) =
      eLpNorm (fun y => vecEuclideanNorm (v.grad y)) p
        (normalizedVolumeOn X) := by
    simpa only [Function.comp_apply] using!
      eLpNorm_comp_measurePreserving hNormalizedMean.aestronglyMeasurable hForward
  exact hmono.trans_eq hpullNorm

end H1Function

end

end PDE
