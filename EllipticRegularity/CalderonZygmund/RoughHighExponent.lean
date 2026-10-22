module

public import EllipticRegularity.CalderonZygmund.SmoothHighExponent
public import PDEFoundation.PDE.UnitBallDirichletApproximation
public import PDEFoundation.Measure.EuclideanFieldNormTendsto
public import PDEFoundation.Measure.LpLimitBound
public import PDEFoundation.Measure.ForcingScale
public import PDEFoundation.Sobolev.H1.GradientLpUpgrade

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open Filter MeasureTheory

noncomputable section

/-! # The high-exponent Calderón--Zygmund estimate for measurable data -/

/-- Smooth approximation and lower semicontinuity remove all smoothness and
bounded-gradient hypotheses from the high-exponent estimate. The constant
is chosen before the exponent and every coefficient, solution and forcing. -/
theorem exists_calderonZygmund_highExponent_constants
    (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (p : ℝ), 4 ≤ p →
      ∀ (a : CoeffField d),
      (∀ i j : Fin d,
        AEMeasurable (fun x => a x i j)
          (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
        IsMatrixPerturbationLE (1 / (C * p)) (a x) (1 : Mat d)) →
      ∀ (u : H1Function (euclideanBall (0 : Vec d) 1))
        (F : Vec d → Vec d),
      (∀ i : Fin d,
        AEStronglyMeasurable (fun x => F x i)
          (volumeOn (euclideanBall (0 : Vec d) 1))) →
      ∀ (hF : MemLp (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p)
          (volumeOn (euclideanBall (0 : Vec d) 1))),
      IsWeakDivergenceFormSolutionOn a
          (euclideanBall (0 : Vec d) 1) u (0 : Vec d → ℝ) F →
      MemW1p (euclideanBall (0 : Vec d) (1 / 2 : ℝ))
          (ENNReal.ofReal p) u.toFun ∧
        ∃ hgrad : MemLp (fun x => vecEuclideanNorm (u.grad x))
            (ENNReal.ofReal p)
            (volumeOn (euclideanBall (0 : Vec d) (1 / 2 : ℝ))),
          euclideanFieldLpMeanNormOn
              (euclideanBall (0 : Vec d) (1 / 2 : ℝ))
              (ENNReal.ofReal p) u.grad
              (memLp_normalizedVolumeOn_of_memLpOn hgrad
                (volume_euclideanBall_pos (0 : Vec d) (by norm_num))) ≤
            C *
              (Real.sqrt
                  (integralAverage (euclideanBall (0 : Vec d) 1)
                    (fun x => vecNormSq (u.grad x))) +
                p * euclideanFieldLpMeanNormOn
                  (euclideanBall (0 : Vec d) 1) (ENNReal.ofReal p) F
                  (memLp_normalizedVolumeOn_of_memLpOn hF
                    (volume_euclideanBall_pos (0 : Vec d) (by norm_num)))) := by
  obtain ⟨C, hC, hSmooth⟩ := exists_calderonZygmund_smooth_highExponent_constants d hd
  refine ⟨C, hC, ?_⟩
  intro p hp a ha hclose u F hFcoord hF hsol
  let U := euclideanBall (0 : Vec d) 1
  let V := euclideanBall (0 : Vec d) (1 / 2)
  have hUpos : 0 < volume U := volume_euclideanBall_pos _ (by norm_num)
  have hUtop : volume U < ∞ :=
    lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top _ (by norm_num))
  have hVpos : 0 < volume V := volume_euclideanBall_pos _ (by norm_num)
  have hVtop : volume V < ∞ :=
    lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top _ (by norm_num))
  have hVU : V ⊆ U := euclideanBall_mono (by norm_num) (by norm_num)
  have hpTwo : 2 ≤ p := (by norm_num : (2 : ℝ) ≤ 4).trans hp
  have hpOne : (1 : ENNReal) ≤ ENNReal.ofReal p :=
    ENNReal.one_le_ofReal.mpr ((by norm_num : (1 : ℝ) ≤ 4).trans hp)
  have hdelta : 0 ≤ 1 / (C * p) := by positivity
  have hdeltaOne : 1 / (C * p) < 1 := by
    apply (div_lt_one (by positivity : 0 < C * p)).2
    have hmul : p ≤ C * p := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hC (by linarith : 0 ≤ p)
    exact (by norm_num : (1 : ℝ) < 4).trans_le (hp.trans hmul)
  obtain ⟨φ, _, w, hsolSeq, hgradConv, hforceConv, _⟩ :=
    exists_unitBallDirichletApproximation hd hpTwo hdelta hdeltaOne
      a ha hclose u F hFcoord hF hsol
  let uSeq : ℕ → H1Function U := fun n => u + (w n).toH1Function
  let FSeq : ℕ → Vec d → Vec d := fun n => unitBallVectorMollification F (φ n)
  obtain ⟨hFsmooth, hFSeqMem, _⟩ :=
    unitBallVectorMollification_properties hd hpOne ENNReal.ofReal_ne_top F hFcoord hF
  have hHigh (n : ℕ) := hSmooth p hp
    (unitBallMatrixMollification a (φ n)) (FSeq n)
    (contDiff_unitBallMatrixMollification_entry hd hdelta a ha hclose (φ n))
    (hFsmooth (φ n))
    (fun x _ => unitBallMatrixMollification_isMatrixPerturbationLE
      hd hdelta a ha hclose (φ n) x)
    (uSeq n) (hFSeqMem (φ n)) (hsolSeq n)
  have hGradSeq (n : ℕ) : MemLp
      (fun x => vecEuclideanNorm ((uSeq n).grad x)) (ENNReal.ofReal p) (volumeOn V) :=
    (hHigh n).2.choose
  have hGradMeanSeq (n : ℕ) : MemLp
      (fun x => vecEuclideanNorm ((uSeq n).grad x)) (ENNReal.ofReal p)
        (normalizedVolumeOn V) :=
    memLp_normalizedVolumeOn_of_memLpOn (hGradSeq n) hVpos
  have hFSeqCoord (n : ℕ) (i : Fin d) :
      MemLp (fun x => FSeq n x i) (ENNReal.ofReal p) (volumeOn U) := by
    apply (hFSeqMem (φ n)).of_le (hFsmooth (φ n) i).continuous.aestronglyMeasurable
    filter_upwards with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (vecEuclideanNorm_nonneg _)] using
      abs_apply_le_vecEuclideanNorm (FSeq n x) i
  have hFcoordMem (i : Fin d) :
      MemLp (fun x => F x i) (ENNReal.ofReal p) (volumeOn U) := by
    apply hF.of_le (hFcoord i)
    filter_upwards with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (vecEuclideanNorm_nonneg _)] using
      abs_apply_le_vecEuclideanNorm (F x) i
  have hFNormConv := tendsto_toReal_euclideanFieldELpMeanNormOn_of_sub
    hpOne hUpos hUtop hFSeqCoord hFcoordMem hforceConv
  have hGradNormConv := tendsto_toReal_euclideanFieldELpMeanNormOn_of_sub
    (by norm_num : (1 : ENNReal) ≤ 2) hUpos hUtop
    (fun n => (uSeq n).gradMemL2) u.gradMemL2 hgradConv
  have hEnergyConv : Tendsto
      (fun n => Real.sqrt (integralAverage U (fun x => vecNormSq ((uSeq n).grad x))))
      atTop (𝓝 (Real.sqrt (integralAverage U (fun x => vecNormSq (u.grad x))))) := by
    have hIdentity (v : H1Function U) :
        Real.sqrt (integralAverage U (fun x => vecNormSq (v.grad x))) =
          (eLpMeanNormOn U 2 (fun x => vecEuclideanNorm (v.grad x))).toReal := by
      exact sqrt_integralAverage_vecNormSq_eq_euclideanFieldLpMeanNormOn_two
        (memLp_normalizedVolumeOn_of_memLpOn v.gradMemL2.memLp_vecEuclideanNorm hUpos)
    simp_rw [hIdentity]
    exact hGradNormConv
  have hMagnitudeConv := tendsto_eLpNorm_vecEuclideanNorm_sub_zero hgradConv fun n =>
    (uSeq n).gradMemL2.memLp_vecEuclideanNorm.aestronglyMeasurable.sub
      u.gradMemL2.memLp_vecEuclideanNorm.aestronglyMeasurable
  have hMagnitudeConvV : Tendsto (fun n => eLpNorm
      (fun x => vecEuclideanNorm ((uSeq n).grad x) - vecEuclideanNorm (u.grad x))
        2 (volumeOn V)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hMagnitudeConv
    · exact fun _ => bot_le
    · intro n
      exact eLpNorm_mono_measure _ (Measure.restrict_mono hVU le_rfl)
  have hMagnitudeMeanConv :=
    tendsto_eLpMeanNormOn_sub_zero_of_tendsto_eLpNormOn_sub_zero hVpos hVtop
      hMagnitudeConvV
  have hGradMeanTwo : MemLp (fun x => vecEuclideanNorm (u.grad x))
      2 (normalizedVolumeOn V) :=
    memLp_normalizedVolumeOn_of_memLpOn
      (u.gradMemL2.memLp_vecEuclideanNorm.mono_measure (Measure.restrict_mono hVU le_rfl))
      hVpos
  have hMeasureConv : TendstoInMeasure (normalizedVolumeOn V)
      (fun n x => vecEuclideanNorm ((uSeq n).grad x)) atTop
      (fun x => vecEuclideanNorm (u.grad x)) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hMagnitudeMeanConv
  let b : ℕ → ℝ := fun n => C *
    (Real.sqrt (integralAverage U (fun x => vecNormSq ((uSeq n).grad x))) +
      p * (eLpMeanNormOn U (ENNReal.ofReal p)
        (fun x => vecEuclideanNorm (FSeq n x))).toReal)
  let B : ℝ := C *
    (Real.sqrt (integralAverage U (fun x => vecNormSq (u.grad x))) +
      p * (eLpMeanNormOn U (ENNReal.ofReal p)
        (fun x => vecEuclideanNorm (F x))).toReal)
  have hb : Tendsto b atTop (𝓝 B) :=
    (hEnergyConv.add (hFNormConv.const_mul p)).const_mul C
  have hbound (n : ℕ) : eLpNorm
      (fun x => vecEuclideanNorm ((uSeq n).grad x)) (ENNReal.ofReal p)
        (normalizedVolumeOn V) ≤ ENNReal.ofReal (b n) := by
    have hn := (hHigh n).2.choose_spec
    change (eLpNorm (fun x => vecEuclideanNorm ((uSeq n).grad x))
      (ENNReal.ofReal p) (normalizedVolumeOn V)).toReal ≤ b n at hn
    rw [← ENNReal.ofReal_toReal (hGradMeanSeq n).eLpNorm_ne_top]
    exact ENNReal.ofReal_le_ofReal hn
  obtain ⟨hGradMean, hLimitBound⟩ := memLp_and_eLpNorm_le_of_tendstoInMeasure
    (fun n x => vecEuclideanNorm ((uSeq n).grad x))
    (fun x => vecEuclideanNorm (u.grad x)) hGradMeanSeq hMeasureConv
    (fun n => ENNReal.ofReal (b n)) (ENNReal.ofReal B) ENNReal.ofReal_ne_top
    (ENNReal.continuous_ofReal.tendsto B |>.comp hb) hbound
  have hGradRaw : MemLp (fun x => vecEuclideanNorm (u.grad x))
      (ENNReal.ofReal p) (volumeOn V) := by
    rw [← volume_smul_normalizedVolumeOn_eq_volumeOn hVpos hVtop]
    exact hGradMean.smul_measure hVtop.ne
  let v := u.restrict (isOpen_euclideanBall _ _) hVU
  have hcoord : GradMemLpOn V (ENNReal.ofReal p) v.grad := by
    intro i
    apply hGradRaw.of_le (v.gradMemL2 i).aestronglyMeasurable
    filter_upwards with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (vecEuclideanNorm_nonneg _)] using!
      abs_apply_le_vecEuclideanNorm (u.grad x) i
  have hw := (v.toW1pOfGradMemLp hd
    (isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) (by norm_num))
    hVpos p hpTwo hcoord).memW1p
  refine ⟨hw, hGradRaw, ?_⟩
  have hBnonneg : 0 ≤ B := by dsimp only [B]; positivity
  simpa only [ENNReal.toReal_ofReal hBnonneg] using!
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hLimitBound

end

end PDE
