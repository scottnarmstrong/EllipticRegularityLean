module

public import PDEFoundation.Measure.ForcingScale
public import PDEFoundation.Measure.MeanLpBoundTransport
public import PDEFoundation.PDE.PerturbativeTesting
public import PDEFoundation.PDE.PerturbativeDirichletStability
public import PDEFoundation.PDE.DirichletGradientConvergence

/-! # Energy bounds for perturbative zero-boundary solutions -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Testing an actual zero-boundary perturbative equation by its solution gives
the sharp coercive energy bound. -/
theorem norm_gradient_h10_le_inv_one_sub_mul_forcing
    {d : ℕ} {U : Set (Vec d)} {delta : ℝ}
    (_hdelta : 0 ≤ delta) (hdeltaOne : delta < 1)
    (a : CoeffField d)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hclose : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (F : Vec d → Vec d) (hF : MemVectorL2On U F)
    (w : H10Function U)
    (hsol : IsWeakDivergenceFormSolutionOn a U w.toH1Function 0 F) :
    ‖w.toH1Function.gradMemL2.toHilbertVectorLp‖ ≤
      (1 - delta)⁻¹ * ‖hF.toHilbertVectorLp‖ := by
  have hsol10 := hsol.toH10SolutionOn_of_isMatrixPerturbationLE ha hclose hF
  have heq := (hsol10 w).2
  simp only [Pi.zero_apply, zero_mul, integral_zero, zero_sub] at heq
  have hpoint : ∀ᵐ x ∂volumeOn U,
      (1 - delta) * vecNormSq (w.toH1Function.grad x) ≤
        vecDot (matVecMul (a x) (w.toH1Function.grad x))
          (w.toH1Function.grad x) := by
    filter_upwards [hclose] with x hx
    simpa only [vecDot_comm] using
      one_sub_delta_mul_vecNormSq_le_vecDot_matVecMul_of_isMatrixPerturbationLE
        hx (w.toH1Function.grad x)
  have hflux := memVectorL2On_matVecMul_of_isMatrixPerturbationLE
    ha hclose w.toH1Function.gradMemL2
  have henergy :
      (1 - delta) * ∫ x in U, vecNormSq (w.toH1Function.grad x) ≤
        ∫ x in U, vecDot (matVecMul (a x) (w.toH1Function.grad x))
          (w.toH1Function.grad x) := by
    rw [← integral_const_mul]
    exact integral_mono_ae
      ((integrableOn_vecNormSq_of_memVectorL2On w.toH1Function.gradMemL2).const_mul _)
      (integrableOn_vecDot_of_memVectorL2On hflux w.toH1Function.gradMemL2)
      hpoint
  rw [heq] at henergy
  have hpair := abs_setIntegral_vecDot_le_sqrt_setIntegral_vecNormSq_mul
    hF w.toH1Function.gradMemL2
  have hmain := henergy.trans ((neg_le_abs _).trans hpair)
  rw [setIntegral_vecNormSq_eq_sq_norm_toHilbertVectorLp
      w.toH1Function.gradMemL2,
    setIntegral_vecNormSq_eq_sq_norm_toHilbertVectorLp hF,
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hmain
  by_cases hz : ‖w.toH1Function.gradMemL2.toHilbertVectorLp‖ = 0
  · simp [hz, mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hdeltaOne.le))
      (norm_nonneg _)]
  · have hp : 0 < ‖w.toH1Function.gradMemL2.toHilbertVectorLp‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hcancel : (1 - delta) *
        ‖w.toH1Function.gradMemL2.toHilbertVectorLp‖ ≤
        ‖hF.toHilbertVectorLp‖ := by
      apply le_of_mul_le_mul_right ?_ hp
      simpa only [pow_two, mul_assoc] using hmain
    exact (le_inv_mul_iff₀ (sub_pos.mpr hdeltaOne)).2 hcancel

/-- On the unit ball, the energy endpoint is bounded by twice the normalized
`Lᵖ` forcing norm for every `p ≥ 2` when `delta ≤ 1/2`. -/
theorem sqrt_integralAverage_gradient_h10_le_two_mul_forcingLpMean
    {d : ℕ} {p delta : ℝ} (hp : 2 ≤ p)
    (hdelta : 0 ≤ delta) (hdeltaHalf : delta ≤ 1 / 2)
    (a : CoeffField d)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec d) 1)))
    (hclose : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
      IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (F : Vec d → Vec d)
    (hFcoord : ∀ i, AEStronglyMeasurable (fun x => F x i)
      (volumeOn (euclideanBall (0 : Vec d) 1)))
    (hFp : MemLp (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p)
      (volumeOn (euclideanBall (0 : Vec d) 1)))
    (w : H10Function (euclideanBall (0 : Vec d) 1))
    (hsol : IsWeakDivergenceFormSolutionOn a
      (euclideanBall (0 : Vec d) 1) w.toH1Function 0 F) :
    Real.sqrt (integralAverage (euclideanBall (0 : Vec d) 1)
      (fun x => vecNormSq (w.toH1Function.grad x))) ≤
      2 * euclideanFieldLpMeanNormOn (euclideanBall (0 : Vec d) 1)
        (ENNReal.ofReal p) F
        (memLp_normalizedVolumeOn_of_memLpOn hFp
          (volume_euclideanBall_pos (0 : Vec d) (by norm_num))) := by
  let U := euclideanBall (0 : Vec d) 1
  have hFL2 : MemVectorL2On U F :=
    memVectorL2On_euclideanBall_of_memLp_vecEuclideanNorm hp
      (0 : Vec d) (by norm_num) (V := U) (by rfl) hFp hFcoord
  have henergy := norm_gradient_h10_le_inv_one_sub_mul_forcing
    hdelta (by linarith) a ha hclose F hFL2 w hsol
  have hinv : (1 - delta)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith : 0 < 1 - delta) (by norm_num : 0 < (2 : ℝ))]
    norm_num
    linarith
  have hraw : ‖w.toH1Function.gradMemL2.toHilbertVectorLp‖ ≤
      2 * ‖hFL2.toHilbertVectorLp‖ :=
    henergy.trans (mul_le_mul_of_nonneg_right hinv (norm_nonneg _))
  have hUpos : 0 < volume U := volume_euclideanBall_pos _ (by norm_num)
  have hUtop : volume U < ∞ :=
    lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top _ (by norm_num))
  have hgradRaw := w.toH1Function.gradMemL2.memLp_vecEuclideanNorm
  have hFRaw := hFL2.memLp_vecEuclideanNorm
  have hgradMean := memLp_normalizedVolumeOn_of_memLpOn hgradRaw hUpos
  have hFMeanTwo := memLp_normalizedVolumeOn_of_memLpOn hFRaw hUpos
  have hFMeanP := memLp_normalizedVolumeOn_of_memLpOn hFp hUpos
  have hmeanRawGrad := lpMeanNormOn_eq_volume_toReal_neg_rpow_mul_eLpNorm
    hUpos hUtop (2 : ENNReal) (fun x => vecEuclideanNorm (w.toH1Function.grad x)) hgradRaw
  have hmeanRawF := lpMeanNormOn_eq_volume_toReal_neg_rpow_mul_eLpNorm
    hUpos hUtop (2 : ENNReal) (fun x => vecEuclideanNorm (F x)) hFRaw
  have hraw' : (eLpNorm (fun x => vecEuclideanNorm (w.toH1Function.grad x))
      2 (volumeOn U)).toReal ≤
      2 * (eLpNorm (fun x => vecEuclideanNorm (F x)) 2 (volumeOn U)).toReal := by
    simpa only [GradMemLpOn.norm_toHilbertVectorLp_eq_eLpNorm] using hraw
  have hmeanTwo : euclideanFieldLpMeanNormOn U 2 w.toH1Function.grad hgradMean ≤
      2 * euclideanFieldLpMeanNormOn U 2 F hFMeanTwo := by
    change lpMeanNormOn U 2 (fun x => vecEuclideanNorm (w.toH1Function.grad x))
        hgradMean ≤ 2 * lpMeanNormOn U 2 (fun x => vecEuclideanNorm (F x)) hFMeanTwo
    rw [hmeanRawGrad, hmeanRawF]
    calc
      _ ≤ (volume U).toReal ^ (-(1 / (2 : ENNReal)).toReal) *
          (2 * (eLpNorm (fun x => vecEuclideanNorm (F x)) 2
            (volumeOn U)).toReal) :=
        mul_le_mul_of_nonneg_left hraw'
          (Real.rpow_nonneg ENNReal.toReal_nonneg _)
      _ = _ := by ring
  let : IsProbabilityMeasure (normalizedVolumeOn U) :=
    isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top hUpos hUtop
  have hExp : (2 : ENNReal) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_ofNat]
    exact ENNReal.ofReal_le_ofReal hp
  have hFmono : euclideanFieldLpMeanNormOn U 2 F hFMeanTwo ≤
      euclideanFieldLpMeanNormOn U (ENNReal.ofReal p) F hFMeanP := by
    change (eLpNorm (fun x => vecEuclideanNorm (F x)) 2
        (normalizedVolumeOn U)).toReal ≤
      (eLpNorm (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p)
        (normalizedVolumeOn U)).toReal
    apply ENNReal.toReal_mono hFMeanP.eLpNorm_ne_top
    exact eLpNorm_le_eLpNorm_of_exponent_le hExp
  rw [sqrt_integralAverage_vecNormSq_eq_euclideanFieldLpMeanNormOn_two hgradMean]
  exact hmeanTwo.trans (mul_le_mul_of_nonneg_left hFmono (by norm_num))

end

end PDE
