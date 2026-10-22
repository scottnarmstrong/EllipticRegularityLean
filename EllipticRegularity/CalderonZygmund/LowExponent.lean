module

public import EllipticRegularity.CalderonZygmund.DirichletLowExponent
public import PDEFoundation.PDE.WeakDivergenceFormAlgebra
public import PDEFoundation.Measure.HalfBallLpBoundTransport
public import PDEFoundation.Measure.EuclideanFieldMeanLp
public import PDEFoundation.Sobolev.H1.MeanEnergyTriangle

/-! # The low-exponent CZ estimate for arbitrary weak solutions -/

@[expose] public section

namespace PDE
open MeasureTheory
open scoped _root_.ENNReal
noncomputable section

/-- Split the actual solution into a forced zero-boundary part and a homogeneous
part. Interpolation and the high-exponent theorem give a uniform estimate
for `2 ≤ p ≤ 4`, with every solution and norm premise discharged internally. -/
theorem exists_calderonZygmund_lowExponent_constants
    (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (p : ℝ), 2 ≤ p → p ≤ 4 →
      ∀ (a : CoeffField d),
      (∀ i j : Fin d,
        AEMeasurable (fun x => a x i j)
          (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
        IsMatrixPerturbationLE (1 / (4 * C)) (a x) (1 : Mat d)) →
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
                euclideanFieldLpMeanNormOn
                  (euclideanBall (0 : Vec d) 1) (ENNReal.ofReal p) F
                  (memLp_normalizedVolumeOn_of_memLpOn hF
                    (volume_euclideanBall_pos (0 : Vec d) (by norm_num)))) := by
  obtain ⟨H, hH, hHigh⟩ := exists_calderonZygmund_highExponent_constants d hd
  obtain ⟨L, hL, hLow⟩ := exists_dirichlet_lowExponent_raw_constants d hd
  let K : ℝ := (2 : ℝ)^((d : ℝ)/2) * ((d : ℝ)^2 * (6 * L))
  let C : ℝ := max H (max L (K + 3 * H))
  have hHC : H ≤ C := le_max_left _ _
  have hLC : L ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hKC : K + 3 * H ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hC : 1 ≤ C := hH.trans hHC
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨C, hC, ?_⟩
  intro p hp hpFour a ha hclose u F hFcoord hFp hsol
  let U := euclideanBall (0 : Vec d) 1
  let V := euclideanBall (0 : Vec d) (1 / 2)
  let delta : ℝ := 1 / (4 * C)
  have hdelta : 0 ≤ delta := by dsimp [delta]; positivity
  have hdeltaL : delta ≤ 1 / (4 * L) := by
    dsimp [delta]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  obtain ⟨w, hwsol, hwgrad, hwraw⟩ := hLow hp hpFour hdelta hdeltaL a ha hclose F hFcoord hFp
  have hwmean := lpMeanNormOn_halfBall_le_two_rpow_mul_of_eLpNorm_le hp
    (by positivity : 0 ≤ (d : ℝ)^2 * (6 * L))
    (fun x => vecEuclideanNorm (w.toH1Function.grad x))
    (fun x => vecEuclideanNorm (F x)) hwgrad hFp hwraw
  let h : H1Function U := u - w.toH1Function
  have hhsol : IsWeakDivergenceFormSolutionOn a U h 0 0 :=
    hsol.sub_isHarmonic_same_forcing hwsol
  have hcloseH : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE (1 / (H * 4)) (a x) 1 := by
    filter_upwards [hclose] with x hx
    intro xi
    apply (hx xi).trans
    apply mul_le_mul_of_nonneg_right _ (vecEuclideanNorm_nonneg xi)
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith only [hHC])
  have hzFour : MemLp (fun x => vecEuclideanNorm ((0 : Vec d → Vec d) x))
      (ENNReal.ofReal (4 : ℝ)) (volumeOn U) := by
    simp [vecEuclideanNorm, vecNormSq, vecDot]
  obtain ⟨_, hhgrad4, hhest⟩ := hHigh 4 (by norm_num) a ha hcloseH h 0
    (fun i => by simpa using! (aestronglyMeasurable_zero : AEStronglyMeasurable (0 : Vec d → ℝ) (volumeOn U)))
    hzFour hhsol
  have hdeltaHalf : delta ≤ 1 / 2 := by
    dsimp [delta]
    apply (div_le_iff₀ (by positivity : 0 < 4 * C)).2
    linarith only [hC]
  have henergyW := sqrt_integralAverage_gradient_h10_le_two_mul_forcingLpMean
    hp hdelta hdeltaHalf a ha hclose F hFcoord hFp w hwsol
  have hneg : MemVectorL2On U (fun x => -w.toH1Function.grad x) :=
    fun i => (w.toH1Function.gradMemL2 i).neg
  have htriangle := sqrt_integralAverage_vecNormSq_add_le u.gradMemL2 hneg
  have henergyH : Real.sqrt (integralAverage U (fun x => vecNormSq (h.grad x))) ≤
      Real.sqrt (integralAverage U (fun x => vecNormSq (u.grad x))) +
        2 * euclideanFieldLpMeanNormOn U (ENNReal.ofReal p) F
          (memLp_normalizedVolumeOn_of_memLpOn hFp (volume_euclideanBall_pos _ (by norm_num))) := by
    have ht : Real.sqrt (integralAverage U (fun x => vecNormSq (h.grad x))) ≤
        Real.sqrt (integralAverage U (fun x => vecNormSq (u.grad x))) +
          Real.sqrt (integralAverage U (fun x => vecNormSq (w.toH1Function.grad x))) := by
      change Real.sqrt (integralAverage U (fun x => vecNormSq (u.grad x - w.toH1Function.grad x))) ≤ _
      simpa only [sub_eq_add_neg, vecNormSq_neg] using htriangle
    exact ht.trans (add_le_add le_rfl henergyW)
  have hVpos : 0 < volume V := volume_euclideanBall_pos _ (by norm_num)
  have hVtop : volume V < ⊤ := lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top _ (by norm_num))
  obtain ⟨hhgrad, hhmono⟩ := exists_memLp_vecEuclideanNorm_of_exponent_le_and_lpMeanNorm_le
    (ENNReal.ofReal_le_ofReal hpFour) hVpos hVtop h.grad hhgrad4
  have hVU : V ⊆ U := euclideanBall_mono (by norm_num) (by norm_num)
  have hpOne : (1 : ENNReal) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr (by linarith)
  have hWcoord (i : Fin d) : AEStronglyMeasurable
      (fun x => w.toH1Function.grad x i) (volumeOn V) :=
    (w.toH1Function.gradMemL2 i).aestronglyMeasurable.mono_measure
      (Measure.restrict_mono hVU le_rfl)
  have hHcoord (i : Fin d) : AEStronglyMeasurable
      (fun x => h.grad x i) (volumeOn V) :=
    (h.gradMemL2 i).aestronglyMeasurable.mono_measure (Measure.restrict_mono hVU le_rfl)
  obtain ⟨hSumMean, hSumEst⟩ := exists_memLp_vecEuclideanNorm_add_and_lpMeanNorm_le
    hpOne hVpos w.toH1Function.grad h.grad hWcoord hHcoord hwgrad hhgrad
  have hGradIdentity : (fun x => w.toH1Function.grad x + h.grad x) = u.grad := by
    funext x
    simp only [h, H1Function.sub_grad]
    abel
  have hGradMean : MemLp (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
      (normalizedVolumeOn V) := by
    have he : (fun x => vecEuclideanNorm (w.toH1Function.grad x + h.grad x)) =
        fun x => vecEuclideanNorm (u.grad x) := congrArg (fun g : Vec d → Vec d => fun x => vecEuclideanNorm (g x)) hGradIdentity
    rw [he] at hSumMean
    exact hSumMean
  have hGradRaw : MemLp (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
      (volumeOn V) := by
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
    hVpos p hp hcoord).memW1p
  refine ⟨hw, hGradRaw, ?_⟩
  have hSumEstU : euclideanFieldLpMeanNormOn V (ENNReal.ofReal p) u.grad
      (memLp_normalizedVolumeOn_of_memLpOn hGradRaw hVpos) ≤
      euclideanFieldLpMeanNormOn V (ENNReal.ofReal p) w.toH1Function.grad
        (memLp_normalizedVolumeOn_of_memLpOn hwgrad hVpos) +
      euclideanFieldLpMeanNormOn V (ENNReal.ofReal p) h.grad
        (memLp_normalizedVolumeOn_of_memLpOn hhgrad hVpos) := by
    simpa only [hGradIdentity] using hSumEst
  have hhest' : euclideanFieldLpMeanNormOn V (ENNReal.ofReal (4 : ℝ)) h.grad
      (memLp_normalizedVolumeOn_of_memLpOn hhgrad4 hVpos) ≤
      H * Real.sqrt (integralAverage U (fun x => vecNormSq (h.grad x))) := by
    simpa [U, V, euclideanFieldLpMeanNormOn, lpMeanNormOn_eq_toReal, eLpMeanNormOn,
      vecEuclideanNorm, vecNormSq, vecDot] using hhest
  have hwmean' : euclideanFieldLpMeanNormOn V (ENNReal.ofReal p) w.toH1Function.grad
      (memLp_normalizedVolumeOn_of_memLpOn hwgrad hVpos) ≤
      K * euclideanFieldLpMeanNormOn U (ENNReal.ofReal p) F
        (memLp_normalizedVolumeOn_of_memLpOn hFp (volume_euclideanBall_pos _ (by norm_num))) := hwmean
  have hBound := hSumEstU.trans (add_le_add hwmean' (hhmono.trans hhest'))
  have hEnergy := mul_le_mul_of_nonneg_left henergyH (zero_le_one.trans hH)
  have hU0 := Real.sqrt_nonneg (integralAverage U (fun x => vecNormSq (u.grad x)))
  have hNF0 : 0 ≤ euclideanFieldLpMeanNormOn U (ENNReal.ofReal p) F
      (memLp_normalizedVolumeOn_of_memLpOn hFp (volume_euclideanBall_pos _ (by norm_num))) :=
    ENNReal.toReal_nonneg
  have hHC' : H ≤ C := hHC
  have hKHC : K + 2 * H ≤ C := by linarith only [hKC, hH]
  have hmulU := mul_le_mul_of_nonneg_right hHC' hU0
  have hmulF := mul_le_mul_of_nonneg_right hKHC hNF0
  nlinarith only [hBound, hEnergy, hmulU, hmulF]

end
end PDE
