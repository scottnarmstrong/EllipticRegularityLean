module

public import EllipticRegularity.CalderonZygmund.RoughHighExponent
public import PDEFoundation.Measure.MeanLpBoundTransport
public import PDEFoundation.PDE.BallDirichletInteriorGradient
public import PDEFoundation.PDE.PerturbativeDirichletEnergy

/-! # Actual quadratic and fourth-power bounds for the interior Dirichlet operator -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped _root_.ENNReal

noncomputable section

/-- The actual interior solution operator has quadratic norm at most two. -/
theorem eLpNorm_ballDirichletInteriorGradientCLM_two_le
    {d : ℕ} (hd : 0 < d) (a : CoeffField d) {delta : ℝ}
    (hdelta : 0 ≤ delta) (hdeltaOne : delta < 1) (hdeltaHalf : delta ≤ 1 / 2)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec d) 1)))
    (hclose : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
      IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (f : HilbertVectorLp (euclideanBall (0 : Vec d) 1) 2) :
    eLpNorm (ballDirichletInteriorGradientCLM hd 0 1 (by norm_num)
      a delta hdelta hdeltaOne ha hclose f) 2
      (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
      2 * eLpNorm f 2 (volumeOn (euclideanBall (0 : Vec d) 1)) := by
  let T := ballDirichletInteriorGradientCLM hd 0 1 (by norm_num)
    a delta hdelta hdeltaOne ha hclose
  have hnorm : ‖T f‖ ≤ 2 * ‖f‖ := by
    have hbase := norm_ballDirichletInteriorGradientCLM_le hd 0 1 (by norm_num)
      a delta hdelta hdeltaOne ha hclose f
    have hinv : (1 - delta)⁻¹ ≤ 2 :=
      (inv_le_comm₀ (by linarith : 0 < 1 - delta)
        (by norm_num : 0 < (2 : ℝ))).2 (by norm_num; linarith)
    exact hbase.trans (mul_le_mul_of_nonneg_right hinv (norm_nonneg _))
  have h := ENNReal.ofReal_le_ofReal hnorm
  simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_ofNat, Lp.norm_def,
    ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (T f)),
    ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f), T] using h

/-- The rough CZ theorem and zero-boundary energy give an actual fourth-power
endpoint for the same canonical interior solution operator. -/
theorem exists_ballDirichletInteriorGradient_four_constants
    (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 1 ≤ C ∧
    ∀ (a : CoeffField d) (delta : ℝ)
      (hdelta : 0 ≤ delta) (hdeltaOne : delta < 1)
      (ha : ∀ i j, AEMeasurable (fun x => a x i j)
        (volumeOn (euclideanBall (0 : Vec d) 1)))
      (hclose : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
        IsMatrixPerturbationLE delta (a x) (1 : Mat d)),
    delta ≤ 1 / (4 * C) →
    ∀ f : HilbertVectorLp (euclideanBall (0 : Vec d) 1) 2,
    MemLp f 4 (volumeOn (euclideanBall (0 : Vec d) 1)) →
    MemLp (ballDirichletInteriorGradientCLM hd 0 1 (by norm_num)
      a delta hdelta hdeltaOne ha hclose f) 4
      (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ∧
    eLpNorm (ballDirichletInteriorGradientCLM hd 0 1 (by norm_num)
      a delta hdelta hdeltaOne ha hclose f) 4
      (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
      ENNReal.ofReal (6 * C) * eLpNorm f 4
        (volumeOn (euclideanBall (0 : Vec d) 1)) := by
  obtain ⟨C, hC, hHigh⟩ := exists_calderonZygmund_highExponent_constants d hd
  refine ⟨C, hC, ?_⟩
  intro a delta hdelta hdeltaOne ha hclose hsmall f hfFour
  let U := euclideanBall (0 : Vec d) 1
  let V := euclideanBall (0 : Vec d) (1 / 2)
  let F : Vec d → Vec d := fun x => (f x).toVec
  have hFL2 : MemVectorL2On U F := by
    apply gradMemLpOn_iff_memLp_toHilbertVecField.mpr
    simpa only [F, toHilbertVecField, Vec.toHilbertVec_toVec] using! Lp.memLp f
  have hFclass : hFL2.toHilbertVectorLp = f := by
    apply Lp.ext
    filter_upwards [hFL2.coeFn_toHilbertVectorLp] with x hx
    simpa only [F, toHilbertVecField, Vec.toHilbertVec_toVec] using hx
  have hFmagEq : (fun x => vecEuclideanNorm (F x)) = fun x => ‖f x‖ := by
    funext x
    rw [Vec.vecEuclideanNorm_eq_norm_toHilbertVec]
    rfl
  have hFfour : MemLp (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal (4 : ℝ))
      (volumeOn U) := by
    rw [hFmagEq]
    simpa only [ENNReal.ofReal_ofNat] using hfFour.norm
  have hFcoord : ∀ i, AEStronglyMeasurable (fun x => F x i) (volumeOn U) :=
    fun i => (hFL2 i).aestronglyMeasurable
  obtain ⟨w, _, hwAE, hwsol⟩ := exists_ballDirichletInteriorGradient_solution
    hd 0 1 (by norm_num) a delta hdelta hdeltaOne ha hclose F hFL2
  let T := ballDirichletInteriorGradientCLM hd 0 1 (by norm_num)
    a delta hdelta hdeltaOne ha hclose
  have hTAE : ⇑(T f) =ᵐ[volumeOn V] toHilbertVecField w.toH1Function.grad := by
    simpa only [hFclass] using hwAE
  have hdeltaHalf : delta ≤ 1 / 2 := by
    apply hsmall.trans
    apply (div_le_iff₀ (by positivity : 0 < 4 * C)).2
    linarith only [hC]
  have hcloseHigh : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE (1 / (C * 4)) (a x) (1 : Mat d) := by
    filter_upwards [hclose] with x hx
    intro ξ
    exact (hx ξ).trans (mul_le_mul_of_nonneg_right
      (by simpa only [mul_comm] using hsmall) (vecEuclideanNorm_nonneg ξ))
  have hsol := hwsol.toIsWeakDivergenceFormSolutionOn (isOpen_euclideanBall _ _)
  obtain ⟨_, hgrad, hest⟩ := hHigh 4 (by norm_num) a ha hcloseHigh
    w.toH1Function F hFcoord hFfour hsol
  have henergy := sqrt_integralAverage_gradient_h10_le_two_mul_forcingLpMean
    (by norm_num : (2 : ℝ) ≤ 4) hdelta hdeltaHalf a ha hclose F hFcoord hFfour w hsol
  let NF : ℝ := euclideanFieldLpMeanNormOn U (ENNReal.ofReal (4 : ℝ)) F
    (memLp_normalizedVolumeOn_of_memLpOn hFfour (volume_euclideanBall_pos _ (by norm_num)))
  have hMeanEst : euclideanFieldLpMeanNormOn V (ENNReal.ofReal (4 : ℝ))
      w.toH1Function.grad (memLp_normalizedVolumeOn_of_memLpOn hgrad
        (volume_euclideanBall_pos _ (by norm_num))) ≤ (6 * C) * NF := by
    have hC0 : 0 ≤ C := zero_le_one.trans hC
    exact hest.trans (by
      change C * (_ + 4 * NF) ≤ (6 * C) * NF
      have he := mul_le_mul_of_nonneg_left henergy hC0
      nlinarith only [he])
  have hMeanBound : eLpNorm (fun x => vecEuclideanNorm (w.toH1Function.grad x))
      4 (normalizedVolumeOn V) ≤ ENNReal.ofReal (6 * C) *
        eLpNorm (fun x => vecEuclideanNorm (F x)) 4 (normalizedVolumeOn U) := by
    have h := ENNReal.ofReal_le_ofReal hMeanEst
    have hgradMean := memLp_normalizedVolumeOn_of_memLpOn hgrad
      (volume_euclideanBall_pos _ (by norm_num))
    have hFMean := memLp_normalizedVolumeOn_of_memLpOn hFfour
      (volume_euclideanBall_pos _ (by norm_num))
    have hgTop : eLpNorm (fun x => vecEuclideanNorm (w.toH1Function.grad x))
        4 (normalizedVolumeOn V) ≠ ⊤ := by simpa [V] using hgradMean.eLpNorm_ne_top
    have hfTop : eLpNorm (fun x => vecEuclideanNorm (F x))
        4 (normalizedVolumeOn U) ≠ ⊤ := by simpa [U] using hFMean.eLpNorm_ne_top
    simpa only [NF, euclideanFieldLpMeanNormOn, lpMeanNormOn_eq_toReal,
      eLpMeanNormOn, ENNReal.ofReal_ofNat,
      ENNReal.ofReal_mul (by positivity : 0 ≤ 6 * C),
      ENNReal.ofReal_toReal hgTop,
      ENNReal.ofReal_toReal hfTop] using h
  have hRawBound := eLpNorm_le_of_eLpMeanNorm_le_of_volume_le
    (volume_euclideanBall_pos (0 : Vec d) (by norm_num : (0 : ℝ) < 1))
    (lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top (0 : Vec d) (by norm_num)))
    (volume_euclideanBall_pos (0 : Vec d) (by norm_num : (0 : ℝ) < 1 / 2))
    (lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top (0 : Vec d) (by norm_num)))
    (measure_mono (euclideanBall_mono (by norm_num) (by norm_num))) hMeanBound
  have hNormAE : (fun x => ‖T f x‖) =ᵐ[volumeOn V]
      fun x => vecEuclideanNorm (w.toH1Function.grad x) := by
    filter_upwards [hTAE] with x hx
    rw [hx]
    exact norm_toHilbertVecField_apply _ x
  have hTargetMem : MemLp (T f) 4 (volumeOn V) := by
    apply (by simpa only [ENNReal.ofReal_ofNat] using hgrad :
      MemLp (fun x => vecEuclideanNorm (w.toH1Function.grad x)) 4 (volumeOn V)).of_le
      (Lp.memLp (T f)).aestronglyMeasurable
    filter_upwards [hNormAE] with x hx
    rw [hx, Real.norm_eq_abs, abs_of_nonneg (vecEuclideanNorm_nonneg _)]
  refine ⟨hTargetMem, ?_⟩
  rw [← eLpNorm_norm (T f) (Lp.aestronglyMeasurable _), eLpNorm_congr_ae hNormAE]
  simpa only [hFmagEq, eLpNorm_norm _ (Lp.aestronglyMeasurable f)] using! hRawBound

end

end PDE
