module

public import EllipticRegularity.CalderonZygmund.OscillationSharpness
public import PDEFoundation.Analysis.ClassicalDivergencePointRemoval
public import PDEFoundation.Analysis.RadialCoefficientDivergence
public import PDEFoundation.Analysis.RadialFluxSmooth
public import PDEFoundation.Analysis.RadialModeAsymptotic
public import PDEFoundation.Ambient.PlanarBlockRadialEllipticity
public import PDEFoundation.Ambient.PlanarBlockRadialMeasurability
public import PDEFoundation.Ambient.RadialNormalizedPerturbation
public import PDEFoundation.Ambient.RadialModeLp
public import PDEFoundation.Geometry.VecAppendBall
public import PDEFoundation.Measure.PlanarRadialAverage
public import PDEFoundation.Measure.PlanarBlockRadialAverage
public import PDEFoundation.Measure.EuclideanFieldMeasurability
public import PDEFoundation.Measure.RadialModeValueLp
public import PDEFoundation.Measure.VecAppendBallNonLp
public import PDEFoundation.PDE.WeakDivergenceFormProductLift
public import PDEFoundation.PDE.CoefficientForcingScale
public import PDEFoundation.Sobolev.PuncturedClassicalWeakGradient
public import PDEFoundation.Ambient.RadialPerturbationSize
public import PDEFoundation.PDE.WeakDivergenceForm

public import CZStatements.OscillationSharpness

@[expose] public section

namespace PDE

open MeasureTheory Set
open Filter
open scoped ENNReal Topology

noncomputable section

/-- The planar critical obstruction extends constantly through any finite
number of unused coordinates, while retaining the literal round-ball
coefficient geometry and the critical failure of gradient integrability. -/
theorem exists_higherDimensional_critical_radialMode_obstruction
    (n : ℕ) (p : ℝ) (hp : 2 < p) :
    let β := 1 - 2 / p
    let δ := (1 - β ^ 2) / (1 + β ^ 2)
    let B := euclideanBall (0 : Vec (2 + n)) 1
    let a : CoeffField (2 + n) := fun z =>
      matAppend
        ((1 : Mat 2) + δ • radialReflectionMatrix (vecAppendEquiv 2 n z).1)
        (1 : Mat n)
    let aNorm : CoeffField (2 + n) := fun z =>
      matAppend
        ((1 - δ)⁻¹ • ((1 : Mat 2) +
          δ • radialReflectionMatrix (vecAppendEquiv 2 n z).1))
        (1 : Mat n)
    ∃ u : H1Function B,
      (∀ z, u.toFun z =
        (vecAppendEquiv 2 n z).1 0 *
          Real.rpow (vecEuclideanNorm (vecAppendEquiv 2 n z).1) (β - 1)) ∧
      (∀ z, u.grad z = (vecAppendEquiv 2 n).symm
        (radialModePowerField 0 β (vecAppendEquiv 2 n z).1, 0)) ∧
      IsWeakDivergenceFormSolutionOn a B u 0 0 ∧
      (∀ z, IsEllipticMatrix (1 - δ) (1 + δ) (a z)) ∧
      (∀ z, IsEllipticMatrix 1 ((1 + δ) / (1 - δ))
        (aNorm z)) ∧
      IsWeakDivergenceFormSolutionOn aNorm B u 0 0 ∧
      ((fun i j => integralAverage B (fun z => a z i j)) =
        (1 : Mat (2 + n))) ∧
      (∀ (z : Vec (2 + n)) (ε : ℝ), 0 ≤ ε →
        (IsMatrixPerturbationLE ε (a z) (1 : Mat (2 + n)) ↔ δ ≤ ε)) ∧
      ((fun i j => integralAverage B (fun z => aNorm z i j)) =
        matAppend ((1 - δ)⁻¹ • (1 : Mat 2)) (1 : Mat n)) ∧
      (∀ (z : Vec (2 + n)) (ε : ℝ), 0 ≤ ε →
        (IsMatrixPerturbationLE ε (aNorm z)
          (matAppend ((1 - δ)⁻¹ • (1 : Mat 2)) (1 : Mat n)) ↔
            δ / (1 - δ) ≤ ε)) ∧
      ¬MemLp (fun z => vecEuclideanNorm (u.grad z)) (ENNReal.ofReal p)
        (volumeOn (euclideanBall (0 : Vec (2 + n)) (1 / 2 : ℝ))) ∧
      ¬MemLp (fun z => vecEuclideanNorm (u.grad z)) (ENNReal.ofReal p)
        (volumeOn B) := by
  dsimp only
  let β : ℝ := 1 - 2 / p
  let δ : ℝ := (1 - β ^ 2) / (1 + β ^ 2)
  let U : Set (Vec 2) := euclideanBall (0 : Vec 2) 1
  let V : Set (Vec n) := euclideanBall (0 : Vec n) 1
  let E : Set (Vec (2 + n)) := vecAppendEquiv 2 n ⁻¹' (U ×ˢ V)
  let B : Set (Vec (2 + n)) := euclideanBall (0 : Vec (2 + n)) 1
  let a₂ : CoeffField 2 := fun x => (1 : Mat 2) + δ • radialReflectionMatrix x
  let a : CoeffField (2 + n) := fun z =>
    matAppend (a₂ (vecAppendEquiv 2 n z).1) (1 : Mat n)
  let aNorm : CoeffField (2 + n) := fun z =>
    matAppend ((1 - δ)⁻¹ • a₂ (vecAppendEquiv 2 n z).1) (1 : Mat n)
  rcases radialMode_critical_parameter p hp with
    ⟨_hβ0, _hβ1, hδ0, hδ1, hβsqrt, _hδformula, hcritical⟩
  have hconstruction := exists_planar_radialMode_sharpness δ hδ0 hδ1
  dsimp only at hconstruction
  rcases hconstruction with
    ⟨u₂, hu₂, hgrad₂, hsol₂, hell₂, hnormalized₂, _haverage₂,
      _hperturbation₂, hLp₂⟩
  have hgrad₂' (x : Vec 2) :
      u₂.grad x = radialModePowerField 0 β x := by
    rw [hgrad₂ x, ← hβsqrt]
  have hUOpen : IsOpen U := isOpen_euclideanBall _ _
  have hVOpen : IsOpen V := isOpen_euclideanBall _ _
  have hVfinite : volume V < ⊤ := by
    exact lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top _ (by norm_num))
  have ha₂Ell : IsEllipticFieldOn (1 - δ) (1 + δ) U a₂ := by
    refine ⟨?_, fun x _ => hell₂ x⟩
    refine (measurable_pi_iff).2 fun i => (measurable_pi_iff).2 fun j => ?_
    have hm : Measurable (fun x : Vec 2 => a₂ x i j) := by
      dsimp only [a₂]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        radialReflectionMatrix, two_smul, Matrix.sub_apply,
        radialProjectionMatrix_apply]
      have hp := ((measurable_pi_apply i).mul (measurable_pi_apply j)).div
        continuous_vecNormSq.measurable
      exact measurable_const.add
        (((hp.add hp).sub measurable_const).const_mul δ)
    exact hm.piecewise hUOpen.measurableSet measurable_const
  have hsol₂L2 : IsWeakDivergenceFormL2SolutionOn a₂ U u₂ 0 0 :=
    hsol₂.toL2SolutionOn_of_isEllipticFieldOn ha₂Ell MeasureTheory.MemLp.zero
      (fun _ => MeasureTheory.MemLp.zero)
  have hsol₂Norm : IsWeakDivergenceFormSolutionOn
      (fun x => (1 - δ)⁻¹ • a₂ x) U u₂ 0 0 := by
    convert hsol₂.smul_coefficient_source_forcing (1 - δ)⁻¹ using 1
    · funext x
      simp only [Pi.zero_apply, mul_zero]
    · funext x
      simp only [Pi.zero_apply, smul_zero]
  have ha₂NormEll : IsEllipticFieldOn 1 ((1 + δ) / (1 - δ)) U
      (fun x => (1 - δ)⁻¹ • a₂ x) := by
    refine ⟨?_, fun x _ => hnormalized₂ x⟩
    refine (measurable_pi_iff).2 fun i => (measurable_pi_iff).2 fun j => ?_
    have hm : Measurable (fun x : Vec 2 => a₂ x i j) := by
      dsimp only [a₂]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        radialReflectionMatrix, two_smul, Matrix.sub_apply,
        radialProjectionMatrix_apply]
      have hp := ((measurable_pi_apply i).mul (measurable_pi_apply j)).div
        continuous_vecNormSq.measurable
      exact measurable_const.add
        (((hp.add hp).sub measurable_const).const_mul δ)
    have hscaled : Measurable (fun x : Vec 2 => ((1 - δ)⁻¹ • a₂ x) i j) := by
      simpa only [Matrix.smul_apply, smul_eq_mul] using!
        measurable_const.mul hm
    exact hscaled.piecewise hUOpen.measurableSet measurable_const
  have hsol₂NormL2 : IsWeakDivergenceFormL2SolutionOn
      (fun x => (1 - δ)⁻¹ • a₂ x) U u₂ 0 0 :=
    hsol₂Norm.toL2SolutionOn_of_isEllipticFieldOn ha₂NormEll
      MeasureTheory.MemLp.zero (fun _ => MeasureTheory.MemLp.zero)
  have hsolE : IsWeakDivergenceFormSolutionOn a E
      (u₂.liftAppend hUOpen hVOpen hVfinite) 0 0 := by
    convert
      (hsol₂L2.liftAppend hUOpen hVOpen hVfinite
        (1 : Mat n)).toIsWeakDivergenceFormSolutionOn using 1
    funext z k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [Pi.zero_apply, vecAppendEquiv_symm_apply_castAdd]
    · simp only [Pi.zero_apply, vecAppendEquiv_symm_apply_natAdd]
  have hsolNormE : IsWeakDivergenceFormSolutionOn aNorm E
      (u₂.liftAppend hUOpen hVOpen hVfinite) 0 0 := by
    convert
      (hsol₂NormL2.liftAppend hUOpen hVOpen hVfinite
        (1 : Mat n)).toIsWeakDivergenceFormSolutionOn using 1
    funext z k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [Pi.zero_apply, vecAppendEquiv_symm_apply_castAdd]
    · simp only [Pi.zero_apply, vecAppendEquiv_symm_apply_natAdd]
  have hEOpen : IsOpen E := by
    exact (hUOpen.prod hVOpen).preimage (vecAppendEquiv 2 n).continuous
  have hBOpen : IsOpen B := isOpen_euclideanBall _ _
  have hBE : B ⊆ E := by
    exact euclideanBall_subset_preimage_vecAppendEquiv_prod 2 n (by norm_num)
  let u : H1Function B :=
    (u₂.liftAppend hUOpen hVOpen hVfinite).restrict hBOpen hBE
  have hgradu (z : Vec (2 + n)) :
      u.grad z = (vecAppendEquiv 2 n).symm
        (radialModePowerField 0 β (vecAppendEquiv 2 n z).1, 0) := by
    rw [show u.grad = (u₂.liftAppend hUOpen hVOpen hVfinite).grad by rfl,
      H1Function.liftAppend_grad, hgrad₂']
  have hsol : IsWeakDivergenceFormSolutionOn a B u 0 0 := by
    exact hsolE.restrict hEOpen hBOpen hBE
  have hsolNorm : IsWeakDivergenceFormSolutionOn aNorm B u 0 0 := by
    exact hsolNormE.restrict hEOpen hBOpen hBE
  have hPlanarNot : ¬MemLp
      (fun x : Vec 2 => vecEuclideanNorm (radialModePowerField 0 β x))
      (ENNReal.ofReal p)
      (volumeOn (euclideanBall (0 : Vec 2) (1 / 2 : ℝ))) := by
    intro hmem
    have hp0 : 0 < p := lt_trans (by norm_num) hp
    have hmem' : MemLp (fun x => vecEuclideanNorm (u₂.grad x))
        (ENNReal.ofReal p)
        (volumeOn (euclideanBall (0 : Vec 2) (1 / 2 : ℝ))) := by
      simpa only [hgrad₂'] using hmem
    have hthreshold := (hLp₂ p (1 / 2) hp0 (by norm_num)).1 hmem'
    rw [← hβsqrt, hcritical] at hthreshold
    exact (lt_irrefl 2) hthreshold
  have hPlanarMeas : AEStronglyMeasurable
      (fun x : Vec 2 => vecEuclideanNorm (radialModePowerField 0 β x))
      (volumeOn (euclideanBall (0 : Vec 2) (1 / 2 : ℝ))) := by
    apply aestronglyMeasurable_vecEuclideanNorm_of_coord
    intro i
    apply Measurable.aestronglyMeasurable
    apply measurable_of_continuousOn_compl_singleton 0
    exact (contDiffOn_radialModePowerField_apply (0 : Fin 2) i β).continuousOn
  have hLiftNot : ¬MemLp
      (fun z : Vec (2 + n) =>
        vecEuclideanNorm (radialModePowerField 0 β (vecAppendEquiv 2 n z).1))
      (ENNReal.ofReal p) (volumeOn B) := by
    simpa only [B, one_div] using
      not_memLp_comp_fst_vecAppendEquiv_euclideanBall 2 n (by norm_num)
        hPlanarMeas hPlanarNot
  have hPlanarQuarterNot : ¬MemLp
      (fun x : Vec 2 => vecEuclideanNorm (radialModePowerField 0 β x))
      (ENNReal.ofReal p)
      (volumeOn (euclideanBall (0 : Vec 2) ((1 / 2 : ℝ) / 2))) := by
    intro hmem
    have hp0 : 0 < p := lt_trans (by norm_num) hp
    have hmem' : MemLp (fun x => vecEuclideanNorm (u₂.grad x))
        (ENNReal.ofReal p)
        (volumeOn (euclideanBall (0 : Vec 2) ((1 / 2 : ℝ) / 2))) := by
      simpa only [hgrad₂'] using hmem
    have hthreshold := (hLp₂ p ((1 / 2) / 2) hp0 (by norm_num)).1 hmem'
    rw [← hβsqrt, hcritical] at hthreshold
    exact (lt_irrefl 2) hthreshold
  have hPlanarQuarterMeas : AEStronglyMeasurable
      (fun x : Vec 2 => vecEuclideanNorm (radialModePowerField 0 β x))
      (volumeOn (euclideanBall (0 : Vec 2) ((1 / 2 : ℝ) / 2))) := by
    apply aestronglyMeasurable_vecEuclideanNorm_of_coord
    intro i
    apply Measurable.aestronglyMeasurable
    apply measurable_of_continuousOn_compl_singleton 0
    exact (contDiffOn_radialModePowerField_apply (0 : Fin 2) i β).continuousOn
  have hLiftHalfNot : ¬MemLp
      (fun z : Vec (2 + n) =>
        vecEuclideanNorm (radialModePowerField 0 β (vecAppendEquiv 2 n z).1))
      (ENNReal.ofReal p)
      (volumeOn (euclideanBall (0 : Vec (2 + n)) (1 / 2 : ℝ))) := by
    simpa only using
      not_memLp_comp_fst_vecAppendEquiv_euclideanBall 2 n
        (by norm_num : (0 : ℝ) < 1 / 2)
        hPlanarQuarterMeas hPlanarQuarterNot
  have hnorm (z : Vec (2 + n)) :
      vecEuclideanNorm ((vecAppendEquiv 2 n).symm
        (radialModePowerField 0 β (vecAppendEquiv 2 n z).1, 0)) =
      vecEuclideanNorm (radialModePowerField 0 β (vecAppendEquiv 2 n z).1) := by
    unfold vecEuclideanNorm
    rw [vecNormSq_vecAppendEquiv_symm]
    simp [vecNormSq, vecDot]
  refine ⟨u, ?_, ?_, hsol, ?_, ?_, hsolNorm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    rw [show u z = u₂ (vecAppendEquiv 2 n z).1 by rfl,
      hu₂ (vecAppendEquiv 2 n z).1, ← hβsqrt]
  · intro z
    exact hgradu z
  · intro z
    exact isEllipticMatrix_matAppend_one_add_planarRadialReflectionMatrix
      n hδ0.le hδ1 (vecAppendEquiv 2 n z).1
  · intro z
    exact isEllipticMatrix_matAppend_normalized_planarRadialReflectionMatrix
      n hδ0.le hδ1 (vecAppendEquiv 2 n z).1
  · exact integralAverage_matAppend_one_add_planarRadialReflectionMatrix
      n (by norm_num) δ
  · intro z ε hε
    rw [isMatrixPerturbationLE_matAppend_one_add_radialReflectionMatrix_iff
      n δ ε hε]
    rw [abs_of_pos hδ0]
  · exact integralAverage_matAppend_smul_one_add_planarRadialReflectionMatrix
      n (by norm_num) (1 - δ)⁻¹ δ
  · intro z ε hε
    exact isMatrixPerturbationLE_matAppend_normalized_radialReflectionMatrix_iff
      n hδ0.le hδ1 ε hε (vecAppendEquiv 2 n z).1
  · intro hmem
    apply hLiftHalfNot
    apply hmem.ae_eq
    filter_upwards [] with z
    rw [hgradu z]
    exact hnorm z
  · intro hmem
    apply hLiftNot
    apply hmem.ae_eq
    filter_upwards [] with z
    rw [hgradu z]
    exact hnorm z


end

end PDE
