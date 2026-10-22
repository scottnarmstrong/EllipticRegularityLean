module

public import PDEFoundation.Ambient.MatAppendEllipticity
public import PDEFoundation.Analysis.ClassicalDivergencePointRemoval
public import PDEFoundation.Analysis.RadialLogDivergence
public import PDEFoundation.Analysis.RadialModeGradient
public import PDEFoundation.Analysis.RadialModeSmooth
public import PDEFoundation.Measure.EuclideanFieldMeanLp
public import PDEFoundation.Measure.EuclideanFieldMeasurability
public import PDEFoundation.Measure.PlanarRadialLogEnergy
public import PDEFoundation.Measure.RadialLogMeanLowerBound
public import PDEFoundation.Measure.RadialLogUnbounded
public import PDEFoundation.Measure.VecAppendBallNormComparison
public import PDEFoundation.Measure.VecAppendBallNonLp
public import PDEFoundation.PDE.WeakDivergenceForm
public import PDEFoundation.PDE.WeakDivergenceFormProductLift
public import PDEFoundation.Sobolev.PuncturedClassicalWeakGradient
public import EllipticRegularity.CalderonZygmund.ForcingAsymptotic
public import CZStatements.ForcingSharpness

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

/-- The planar logarithmic witness, extended constantly in unused variables,
gives the forcing sharpness obstruction in every dimension at least two. -/
theorem exists_higherDimensional_logarithmic_forcing_violation (n : ℕ) :
    let B := euclideanBall (0 : Vec (2 + n)) 1
    let V := euclideanBall (0 : Vec (2 + n)) (1 / 2 : ℝ)
    let G : Vec (2 + n) → Vec (2 + n) := fun z =>
      (vecAppendEquiv 2 n).symm
        (radialLogGradientField 0 (vecAppendEquiv 2 n z).1, 0)
    let F : Vec (2 + n) → Vec (2 + n) := fun z =>
      (vecAppendEquiv 2 n).symm
        (radialForcing 0 (vecAppendEquiv 2 n z).1, 0)
    ∃ u : H1Function B,
      (∀ z, u.toFun z = (vecAppendEquiv 2 n z).1 0 *
        Real.log (vecEuclideanNorm (vecAppendEquiv 2 n z).1)) ∧
      (∀ z, u.grad z = G z) ∧
      (∀ i : Fin (2 + n),
        AEStronglyMeasurable (fun z => F z i) (volumeOn B)) ∧
      MemLp (fun z => vecEuclideanNorm (F z)) ⊤ (volumeOn B) ∧
      eLpNorm (fun z => vecEuclideanNorm (F z)) ⊤ (volumeOn B) ≤ 2 ∧
      IsWeakDivergenceFormSolutionOn
        (fun _ => (1 : Mat (2 + n))) B u 0 F ∧
      ¬MemLp (fun z => vecEuclideanNorm (u.grad z)) ⊤ (volumeOn V) ∧
      ∀ (A : ℝ), 0 ≤ A → ∀ (b : ℝ → ℝ),
        Filter.Tendsto (fun p : ℝ => b p / p) Filter.atTop (nhds 0) →
        (∀ p : ℝ, 2 ≤ p → 0 ≤ b p) →
        ∃ p : ℝ, 2 ≤ p ∧
          ∃ hgrad : MemLp (fun z => vecEuclideanNorm (u.grad z))
              (ENNReal.ofReal p) (volumeOn V),
            ∃ hforce : MemLp (fun z => vecEuclideanNorm (F z))
                (ENNReal.ofReal p) (volumeOn B),
              A * Real.sqrt
                    (integralAverage B (fun z => vecNormSq (u.grad z))) +
                  b p * euclideanFieldLpMeanNormOn B (ENNReal.ofReal p) F
                    (memLp_normalizedVolumeOn_of_memLpOn hforce
                      (volume_euclideanBall_pos (0 : Vec (2 + n)) (by norm_num))) <
                euclideanFieldLpMeanNormOn V (ENNReal.ofReal p) u.grad
                  (memLp_normalizedVolumeOn_of_memLpOn hgrad
                    (volume_euclideanBall_pos (0 : Vec (2 + n)) (by norm_num))) := by
  let U : Set (Vec 2) := euclideanBall (0 : Vec 2) 1
  let W : Set (Vec n) := euclideanBall (0 : Vec n) 1
  let E : Set (Vec (2 + n)) := vecAppendEquiv 2 n ⁻¹' (U ×ˢ W)
  let B : Set (Vec (2 + n)) := euclideanBall (0 : Vec (2 + n)) 1
  let V : Set (Vec (2 + n)) := euclideanBall (0 : Vec (2 + n)) (1 / 2 : ℝ)
  let G : Vec (2 + n) → Vec (2 + n) := fun z =>
    (vecAppendEquiv 2 n).symm
      (radialLogGradientField 0 (vecAppendEquiv 2 n z).1, 0)
  let F : Vec (2 + n) → Vec (2 + n) := fun z =>
    (vecAppendEquiv 2 n).symm
      (radialForcing 0 (vecAppendEquiv 2 n z).1, 0)
  rcases exists_planar_logarithmic_forcing_sharpness with
    ⟨u₂, hu₂, hgrad₂, hF₂coord, hF₂top, _hF₂topNorm, hsol₂,
      _henergy₂, _hlower₂, _hunbounded₂⟩
  have hgrad₂' (x : Vec 2) :
      u₂.grad x = radialLogGradientField 0 x := by
    funext i
    simpa only [radialLogGradientField] using hgrad₂ x i
  have hUOpen : IsOpen U := isOpen_euclideanBall _ _
  have hWOpen : IsOpen W := isOpen_euclideanBall _ _
  have hWfinite : volume W < ⊤ := by
    exact lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top _ (by norm_num))
  let : IsFiniteMeasure (volumeOn U) := by
    dsimp only [U]
    exact isFiniteMeasure_volumeOn_euclideanBall _ (by norm_num)
  have hF₂L2 : MemVectorL2On U (radialForcing 0) := by
    intro i
    have hiTop : MemLp (fun x => radialForcing 0 x i) ⊤ (volumeOn U) := by
      apply memLp_top_of_bound (hF₂coord i) 2
      filter_upwards with x
      rw [Real.norm_eq_abs]
      exact (abs_apply_le_vecEuclideanNorm (radialForcing 0 x) i).trans
        (vecEuclideanNorm_radialForcing_le_two 0 x)
    exact hiTop.mono_exponent (by norm_num)
  have hOneEll : IsEllipticFieldOn 1 1 U (fun _ => (1 : Mat 2)) := by
    refine ⟨?_, ?_⟩
    · refine (measurable_pi_iff).2 fun i => (measurable_pi_iff).2 fun j => ?_
      exact measurable_const.piecewise hUOpen.measurableSet measurable_const
    · intro x _hx
      simpa only [sub_zero, add_zero, zero_smul] using
        isEllipticMatrix_one_add_radialReflectionMatrix
          (delta := (0 : ℝ)) (by norm_num) (by norm_num) x
  have hsol₂L2 : IsWeakDivergenceFormL2SolutionOn
      (fun _ => (1 : Mat 2)) U u₂ 0 (radialForcing 0) :=
    hsol₂.toL2SolutionOn_of_isEllipticFieldOn hOneEll MemLp.zero hF₂L2
  have hsolEL2 := hsol₂L2.liftAppend hUOpen hWOpen hWfinite (1 : Mat n)
  have hsolE : IsWeakDivergenceFormSolutionOn
      (fun _ => (1 : Mat (2 + n))) E
      (u₂.liftAppend hUOpen hWOpen hWfinite) 0 F := by
    simpa only [E, F, Pi.one_apply, matAppend_one_one] using!
      hsolEL2.toIsWeakDivergenceFormSolutionOn
  have hEOpen : IsOpen E :=
    (hUOpen.prod hWOpen).preimage (vecAppendEquiv 2 n).continuous
  have hBOpen : IsOpen B := isOpen_euclideanBall _ _
  have hBE : B ⊆ E :=
    euclideanBall_subset_preimage_vecAppendEquiv_prod 2 n (by norm_num)
  let u : H1Function B :=
    (u₂.liftAppend hUOpen hWOpen hWfinite).restrict hBOpen hBE
  have hgradu (z : Vec (2 + n)) : u.grad z = G z := by
    rw [show u.grad = (u₂.liftAppend hUOpen hWOpen hWfinite).grad by rfl,
      H1Function.liftAppend_grad, hgrad₂']
  have hsol : IsWeakDivergenceFormSolutionOn
      (fun _ => (1 : Mat (2 + n))) B u 0 F :=
    hsolE.restrict hEOpen hBOpen hBE
  have hFB2 : MemVectorL2On B F := by
    intro i
    exact (hsolEL2.forcing_memL2 i).mono_measure
      (Measure.restrict_mono hBE le_rfl)
  have hFcoord (i : Fin (2 + n)) :
      AEStronglyMeasurable (fun z => F z i) (volumeOn B) :=
    (hFB2 i).aestronglyMeasurable
  have hFnorm (z : Vec (2 + n)) :
      vecEuclideanNorm (F z) =
        vecEuclideanNorm (radialForcing 0 (vecAppendEquiv 2 n z).1) := by
    unfold F vecEuclideanNorm
    rw [vecNormSq_vecAppendEquiv_symm]
    simp [vecNormSq, vecDot]
  have hFmagMeas : AEStronglyMeasurable
      (fun z => vecEuclideanNorm (F z)) (volumeOn B) :=
    aestronglyMeasurable_vecEuclideanNorm_of_coord hFcoord
  have hFbound : ∀ᵐ z ∂volumeOn B, ‖vecEuclideanNorm (F z)‖ ≤ 2 := by
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (vecEuclideanNorm_nonneg _), hFnorm]
    exact vecEuclideanNorm_radialForcing_le_two 0 _
  have hFtop : MemLp (fun z => vecEuclideanNorm (F z)) ⊤ (volumeOn B) :=
    memLp_top_of_bound hFmagMeas 2 hFbound
  have hFtopNorm : eLpNorm (fun z => vecEuclideanNorm (F z)) ⊤
      (volumeOn B) ≤ 2 := by
    rw [eLpNorm_exponent_top hFmagMeas]
    simpa only [ENNReal.ofReal_ofNat] using eLpNormEssSup_le_of_ae_bound hFbound
  have hPlanarMeas : AEStronglyMeasurable
      (fun x : Vec 2 => vecEuclideanNorm (radialLogGradientField 0 x))
      (volumeOn (euclideanBall (0 : Vec 2) ((1 / 2 : ℝ) / 2))) := by
    apply aestronglyMeasurable_vecEuclideanNorm_of_coord
    intro i
    apply Measurable.aestronglyMeasurable
    apply measurable_of_continuousOn_compl_singleton 0
    exact (contDiffOn_radialLogGradientField_apply (0 : Fin 2) i).continuousOn
  have hPlanarNot : ¬MemLp
      (fun x : Vec 2 => vecEuclideanNorm (radialLogGradientField 0 x)) ⊤
      (volumeOn (euclideanBall (0 : Vec 2) ((1 / 2 : ℝ) / 2))) :=
    not_memLp_top_vecEuclideanNorm_radialLogGradientField_euclideanBall
      (d := 2) (by norm_num) 0 (by norm_num)
  have hLiftNot : ¬MemLp
      (fun z : Vec (2 + n) =>
        vecEuclideanNorm (radialLogGradientField 0 (vecAppendEquiv 2 n z).1)) ⊤
      (volumeOn V) := by
    simpa only [V] using
      not_memLp_comp_fst_vecAppendEquiv_euclideanBall 2 n (by norm_num)
        hPlanarMeas hPlanarNot
  have hGnorm (z : Vec (2 + n)) :
      vecEuclideanNorm (G z) =
        vecEuclideanNorm (radialLogGradientField 0 (vecAppendEquiv 2 n z).1) := by
    unfold G vecEuclideanNorm
    rw [vecNormSq_vecAppendEquiv_symm]
    simp [vecNormSq, vecDot]
  have hunbounded : ¬MemLp (fun z => vecEuclideanNorm (u.grad z)) ⊤
      (volumeOn V) := by
    intro hmem
    apply hLiftNot
    apply hmem.ae_eq
    filter_upwards with z
    rw [hgradu, hGnorm]
  obtain ⟨K, hK, hcompare⟩ :=
    exists_uniform_lpMeanNormOn_comp_fst_le_on_euclideanBall
      2 n (R := (1 / 2 : ℝ)) (by norm_num)
  refine ⟨u, ?_, hgradu, hFcoord, hFtop, hFtopNorm, hsol, hunbounded, ?_⟩
  · intro z
    simpa only [u, H1Function.restrict_apply, H1Function.liftAppend_apply] using
      hu₂ (vecAppendEquiv 2 n z).1
  · intro A hA b hb hb_nonneg
    have hKb : Filter.Tendsto (fun p : ℝ => (K * b p) / p)
        Filter.atTop (nhds 0) := by
      have h := (tendsto_const_nhds (x := K)).mul hb
      simpa only [mul_zero, mul_div_assoc] using h
    let energy := Real.sqrt (integralAverage B (fun z => vecNormSq (u.grad z)))
    have hnot := not_forall_half_Gamma_le_constant_add_sublinear
      (K * A * energy) (fun p => K * b p) hKb
    push Not at hnot
    obtain ⟨p, hp, hpStrict⟩ := hnot
    obtain ⟨hPlanarP, hPlanarLower⟩ :=
      exists_memLp_radialLogGradientField_and_lpMeanNorm_lower_bound
        (d := 2) (by norm_num) 0 (R := ((1 / 2 : ℝ) / 2))
        (p := p) (by norm_num) (by norm_num) (by linarith only [hp])
    obtain ⟨hPlanarUnit, _hPlanarUnitLower⟩ :=
      exists_memLp_radialLogGradientField_and_lpMeanNorm_lower_bound
        (d := 2) (by norm_num) 0 (R := (1 : ℝ))
        (p := p) (by norm_num) (by norm_num) (by linarith only [hp])
    have hLiftCylinder : MemLp
        (fun z : Vec (2 + n) =>
          vecEuclideanNorm (radialLogGradientField 0 (vecAppendEquiv 2 n z).1))
        (ENNReal.ofReal p) (volumeOn E) := by
      simpa only [E, U, W] using
        memLp_comp_fst_vecAppendEquiv 2 n
          (measurableSet_euclideanBall _ _) (measurableSet_euclideanBall _ _)
          hWfinite hPlanarUnit
    have hVB : V ⊆ B := by
      dsimp only [V, B]
      exact euclideanBall_mono (by norm_num) (by norm_num)
    have hLiftP : MemLp
        (fun z : Vec (2 + n) =>
          vecEuclideanNorm (radialLogGradientField 0 (vecAppendEquiv 2 n z).1))
        (ENNReal.ofReal p) (volumeOn V) :=
      hLiftCylinder.mono_measure (Measure.restrict_mono
        (hVB.trans hBE) le_rfl)
    have hgrad : MemLp (fun z => vecEuclideanNorm (u.grad z))
        (ENNReal.ofReal p) (volumeOn V) := by
      apply hLiftP.ae_eq
      filter_upwards with z
      rw [hgradu, hGnorm]
    have hcomparison := hcompare p hp
      (fun x : Vec 2 => vecEuclideanNorm (radialLogGradientField 0 x))
      hPlanarMeas hLiftP
    have hGammaToGrad :
        (1 / 2 : ℝ) * Real.rpow (Real.Gamma (p + 1)) (1 / p) - 1 ≤
          K * euclideanFieldLpMeanNormOn V (ENNReal.ofReal p) u.grad
            (memLp_normalizedVolumeOn_of_memLpOn hgrad
              (volume_euclideanBall_pos (0 : Vec (2 + n)) (by norm_num))) := by
      calc
        _ ≤ euclideanFieldLpMeanNormOn
              (euclideanBall (0 : Vec 2) ((1 / 2 : ℝ) / 2))
              (ENNReal.ofReal p) (radialLogGradientField 0)
              (memLp_normalizedVolumeOn_of_memLpOn hPlanarP
                (volume_euclideanBall_pos (0 : Vec 2) (by norm_num))) := by
          simpa only [div_eq_mul_inv, one_mul, mul_comm] using! hPlanarLower
        _ ≤ K * euclideanFieldLpMeanNormOn V (ENNReal.ofReal p) u.grad
              (memLp_normalizedVolumeOn_of_memLpOn hgrad
                (volume_euclideanBall_pos (0 : Vec (2 + n)) (by norm_num))) := by
          rw [euclideanFieldLpMeanNormOn, lpMeanNormOn_eq_toReal]
          change _ ≤ K *
            (eLpNorm (fun z => vecEuclideanNorm (u.grad z))
              (ENNReal.ofReal p) (normalizedVolumeOn V)).toReal
          calc
            _ ≤ K * (eLpNorm (fun z : Vec (2 + n) =>
                vecEuclideanNorm (radialLogGradientField 0
                  (vecAppendEquiv 2 n z).1)) (ENNReal.ofReal p)
                (normalizedVolumeOn V)).toReal := hcomparison
            _ = _ := by
              have heq :
                  eLpNorm (fun z : Vec (2 + n) =>
                    vecEuclideanNorm (radialLogGradientField 0
                      (vecAppendEquiv 2 n z).1)) (ENNReal.ofReal p)
                      (normalizedVolumeOn V) =
                    eLpNorm (fun z => vecEuclideanNorm (u.grad z))
                      (ENNReal.ofReal p) (normalizedVolumeOn V) := by
                apply eLpNorm_congr_ae
                filter_upwards with z
                rw [hgradu, hGnorm]
              rw [heq]
    have hBPos : 0 < volume B := by
      simpa only [B] using
        volume_euclideanBall_pos (0 : Vec (2 + n)) (by norm_num : (0 : ℝ) < 1)
    have hBTop : volume B < ∞ := by
      simpa only [B] using lt_top_iff_ne_top.mpr
        (volume_euclideanBall_ne_top (0 : Vec (2 + n)) (by norm_num))
    obtain ⟨hforce, hforceMono⟩ :=
      exists_memLp_vecEuclideanNorm_of_exponent_le_and_lpMeanNorm_le
        (U := B) (q := ENNReal.ofReal p) (p := ⊤) le_top hBPos hBTop F hFtop
    have hFtopMean := memLp_normalizedVolumeOn_of_memLpOn hFtop hBPos
    have hFboundMean : ∀ᵐ z ∂normalizedVolumeOn B,
        ‖vecEuclideanNorm (F z)‖ ≤ 2 := by
      filter_upwards with z
      rw [Real.norm_eq_abs, abs_of_nonneg (vecEuclideanNorm_nonneg _), hFnorm]
      exact vecEuclideanNorm_radialForcing_le_two 0 _
    have hFmeanTopLe : euclideanFieldLpMeanNormOn B ⊤ F hFtopMean ≤ 2 := by
      rw [euclideanFieldLpMeanNormOn, lpMeanNormOn_eq_toReal]
      change (eLpNorm (fun z => vecEuclideanNorm (F z)) ⊤
        (normalizedVolumeOn B)).toReal ≤ 2
      rw [eLpNorm_exponent_top hFtopMean.aestronglyMeasurable]
      calc
        (eLpNormEssSup (fun z => vecEuclideanNorm (F z))
            (normalizedVolumeOn B)).toReal ≤ (ENNReal.ofReal 2).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top
            (eLpNormEssSup_le_of_ae_bound hFboundMean)
        _ = 2 := by norm_num
    have hFmeanLe : euclideanFieldLpMeanNormOn B (ENNReal.ofReal p) F
        (memLp_normalizedVolumeOn_of_memLpOn hforce hBPos) ≤ 2 :=
      hforceMono.trans hFmeanTopLe
    refine ⟨p, hp, hgrad, hforce, ?_⟩
    change A * energy +
        b p * euclideanFieldLpMeanNormOn B (ENNReal.ofReal p) F
          (memLp_normalizedVolumeOn_of_memLpOn hforce hBPos) <
      euclideanFieldLpMeanNormOn V (ENNReal.ofReal p) u.grad
        (memLp_normalizedVolumeOn_of_memLpOn hgrad
          (volume_euclideanBall_pos (0 : Vec (2 + n)) (by norm_num)))
    by_contra hfail
    have hestimate : euclideanFieldLpMeanNormOn V (ENNReal.ofReal p) u.grad
          (memLp_normalizedVolumeOn_of_memLpOn hgrad
            (volume_euclideanBall_pos (0 : Vec (2 + n)) (by norm_num))) ≤
        A * energy + b p * euclideanFieldLpMeanNormOn B (ENNReal.ofReal p) F
          (memLp_normalizedVolumeOn_of_memLpOn hforce hBPos) := by
      exact le_of_not_gt hfail
    have hK0 : 0 ≤ K := le_trans zero_le_one hK
    have hb0 : 0 ≤ b p := hb_nonneg p hp
    have hforcingLe :
        b p * euclideanFieldLpMeanNormOn B (ENNReal.ofReal p) F
            (memLp_normalizedVolumeOn_of_memLpOn hforce hBPos) ≤ b p * 2 :=
      mul_le_mul_of_nonneg_left hFmeanLe hb0
    have hupper : K * euclideanFieldLpMeanNormOn V (ENNReal.ofReal p) u.grad
          (memLp_normalizedVolumeOn_of_memLpOn hgrad
            (volume_euclideanBall_pos (0 : Vec (2 + n)) (by norm_num))) ≤
        K * A * energy + 2 * (K * b p) := by
      calc
        _ ≤ K * (A * energy + b p * euclideanFieldLpMeanNormOn B
              (ENNReal.ofReal p) F
              (memLp_normalizedVolumeOn_of_memLpOn hforce hBPos)) :=
          mul_le_mul_of_nonneg_left hestimate hK0
        _ ≤ K * (A * energy + b p * 2) :=
          mul_le_mul_of_nonneg_left
            (add_le_add_right hforcingLe (A * energy)) hK0
        _ = K * A * energy + 2 * (K * b p) := by ring
    exact (not_lt_of_ge (hGammaToGrad.trans hupper)) hpStrict

end

end PDE
