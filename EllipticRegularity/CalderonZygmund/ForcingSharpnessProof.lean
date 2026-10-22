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

@[expose] public section

namespace PDE.CZForcingSharpnessProof

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

theorem result :
    let B := euclideanBall (0 : Vec 2) 1
    let V := euclideanBall (0 : Vec 2) (1 / 2 : ℝ)
    ∃ u : H1Function B,
      (∀ x, u.toFun x = x 0 * Real.log (vecEuclideanNorm x)) ∧
      (∀ x i, u.grad x i = basisVec 0 i * Real.log (vecEuclideanNorm x) +
        x 0 * x i / vecNormSq x) ∧
      (∀ i : Fin 2, AEStronglyMeasurable (fun x => radialForcing 0 x i) (volumeOn B)) ∧
      MemLp (fun x => vecEuclideanNorm (radialForcing 0 x)) ⊤ (volumeOn B) ∧
      eLpNorm (fun x => vecEuclideanNorm (radialForcing 0 x)) ⊤ (volumeOn B) ≤ 2 ∧
      IsWeakDivergenceFormSolutionOn (fun _ => (1 : Mat 2)) B u 0 (radialForcing 0) ∧
      Real.sqrt (integralAverage B (fun x => vecNormSq (u.grad x))) = Real.sqrt (1 / 2 : ℝ) ∧
      (∀ p : ℝ, 2 ≤ p →
        ∃ hgrad : MemLp (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p) (volumeOn V),
          (1 / 2 : ℝ) * Real.rpow (Real.Gamma (p + 1)) (1 / p) - 1 ≤
            euclideanFieldLpMeanNormOn V (ENNReal.ofReal p) u.grad
              (memLp_normalizedVolumeOn_of_memLpOn hgrad
                (volume_euclideanBall_pos (0 : Vec 2) (by norm_num)))) ∧
      ¬MemLp (fun x => vecEuclideanNorm (u.grad x)) ⊤ (volumeOn V) := by
  let B := euclideanBall (0 : Vec 2) 1
  let V := euclideanBall (0 : Vec 2) (1 / 2 : ℝ)
  let f : Vec 2 → ℝ := fun x => x 0 * Real.log (vecEuclideanNorm x)
  let G : Vec 2 → Vec 2 := radialLogGradientField 0
  let F : Vec 2 → Vec 2 := radialForcing 0
  have hf2 : MemLp f 2 (volumeOn B) := by
    simpa only [f, B, ENNReal.ofReal_ofNat] using
      memLp_coordinate_mul_log_vecEuclideanNorm_unitBall
        (d := 2) (by norm_num) 0 (p := 2) (by norm_num)
  have hG2 : ∀ i : Fin 2, MemLp (fun x => G x i) 2 (volumeOn B) := by
    intro i
    simpa only [G, B, ENNReal.ofReal_ofNat] using
      memLp_radialLogGradientField_apply_unitBall
        (d := 2) (by norm_num) 0 i (p := 2) (by norm_num)
  have hfSmooth : ContDiffOn ℝ 1 f (B \ {0}) := by
    apply ((contDiffOn_coordinate_mul_log_vecEuclideanNorm (d := 2) 0).of_le
      (by norm_num)).mono
    intro x hx
    exact hx.2
  have hfGrad : ∀ x ∈ B \ {0}, classicalGradient f x = G x := by
    intro x hx
    have hx0 : x ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx.2
    simpa only [f, G, radialLogGradientField] using!
      classicalGradient_coordinate_mul_log_vecEuclideanNorm 0 x hx0
  have hfWeak : HasWeakGradientOn B f G :=
    hasWeakGradientOn_of_punctured_classicalGradient
      (d := 2) (by norm_num) (isOpen_euclideanBall 0 1) hf2 hG2 hfSmooth hfGrad
  let u : H1Function B :=
    { toFun := f
      grad := G
      memL2 := hf2
      gradMemL2 := hG2
      hasWeakGradient := hfWeak }
  have hFcoord (i : Fin 2) :
      AEStronglyMeasurable (fun x => F x i) (volumeOn B) := by
    apply Measurable.aestronglyMeasurable
    apply measurable_of_continuousOn_compl_singleton 0
    exact (contDiffOn_radialForcing_apply (d := 2) 0 i).continuousOn
  have hFmagMeas :
      AEStronglyMeasurable (fun x => vecEuclideanNorm (F x)) (volumeOn B) :=
    aestronglyMeasurable_vecEuclideanNorm_of_coord hFcoord
  have hFbound : ∀ᵐ x ∂volumeOn B, ‖vecEuclideanNorm (F x)‖ ≤ 2 := by
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (vecEuclideanNorm_nonneg _)]
    exact vecEuclideanNorm_radialForcing_le_two 0 x
  have hFtop : MemLp (fun x => vecEuclideanNorm (F x)) ⊤ (volumeOn B) :=
    memLp_top_of_bound hFmagMeas 2 hFbound
  have hFtopNorm : eLpNorm (fun x => vecEuclideanNorm (F x)) ⊤ (volumeOn B) ≤ 2 := by
    rw [eLpNorm_exponent_top hFmagMeas]
    simpa only [ENNReal.ofReal_ofNat] using eLpNormEssSup_le_of_ae_bound hFbound
  let : IsFiniteMeasure (volumeOn B) := ⟨by
    simpa only [B, volumeOn, Measure.restrict_apply_univ] using
      lt_top_iff_ne_top.mpr
        (volume_euclideanBall_ne_top (0 : Vec 2) (by norm_num : (0 : ℝ) ≤ 1))⟩
  have hF2 : MemVectorL2On B F := by
    intro i
    have hiTop : MemLp (fun x => F x i) ⊤ (volumeOn B) := by
      apply memLp_top_of_bound (hFcoord i) 2
      filter_upwards with x
      rw [Real.norm_eq_abs]
      exact (abs_apply_le_vecEuclideanNorm (F x) i).trans
        (vecEuclideanNorm_radialForcing_le_two 0 x)
    exact hiTop.mono_exponent (by norm_num)
  let J : Vec 2 → Vec 2 := fun x => G x + F x
  have hJ2 : MemVectorL2On B J := fun i => by
    simpa only [J, Pi.add_apply] using! (hG2 i).add (hF2 i)
  have hJsmooth : ∀ i : Fin 2, ContDiffOn ℝ 1 (fun x => J x i) (B \ {0}) := by
    intro i
    apply (((contDiffOn_radialLogGradientField_apply (d := 2) 0 i).add
      (contDiffOn_radialForcing_apply (d := 2) 0 i)).of_le (by norm_num)).mono
    intro x hx
    exact hx.2
  have hJdiv : ∀ x ∈ B \ {0},
      (∑ i : Fin 2, classicalGradient (fun y => J y i) x i) = 0 := by
    intro x hx
    have hx0 : x ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx.2
    simpa only [J, G, F, Pi.add_apply] using
      sum_classicalGradient_radialLogGradientField_add_radialForcing_fin_two
        0 x hx0
  have hJweak : ∀ φ : WeakTestFunction B,
      ∫ x in B, vecDot (J x) (φ.grad x) = 0 :=
    integral_vecDot_grad_eq_zero_of_classical_divergence_punctured
      (d := 2) (by norm_num) (isOpen_euclideanBall 0 1) J hJ2 hJsmooth hJdiv
  have hsol :
      IsWeakDivergenceFormSolutionOn (fun _ => (1 : Mat 2)) B u 0 F := by
    have hone : (fun x => matVecMul (1 : Mat 2) (G x)) = G := by
      funext x
      exact Matrix.one_mulVec (G x)
    intro φ
    have hdata : DivergenceFormL2DataOn (fun _ => (1 : Mat 2)) B u 0 F := by
      refine ⟨?_, MemLp.zero, hF2⟩
      rw [show (fun x => matVecMul (1 : Mat 2) (u.grad x)) = G by
        simpa only [u] using hone]
      exact hG2
    refine ⟨hdata.testable φ, ?_⟩
    have hGInt : IntegrableOn (fun x => vecDot (G x) (φ.grad x)) B :=
      integrableOn_vecDot_of_memVectorL2On hG2 φ.grad_memVectorL2On
    have hFInt : IntegrableOn (fun x => vecDot (F x) (φ.grad x)) B :=
      integrableOn_vecDot_of_memVectorL2On hF2 φ.grad_memVectorL2On
    have hsplit :
        (∫ x in B, vecDot (J x) (φ.grad x)) =
          (∫ x in B, vecDot (G x) (φ.grad x)) +
            ∫ x in B, vecDot (F x) (φ.grad x) := by
      rw [← integral_add hGInt hFInt]
      apply integral_congr_ae
      filter_upwards with x
      simp only [J, vecDot, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    have hsum :
        (∫ x in B, vecDot (G x) (φ.grad x)) +
          ∫ x in B, vecDot (F x) (φ.grad x) = 0 := by
      rw [← hsplit]
      exact hJweak φ
    simp only [Pi.zero_apply, zero_mul, integral_zero, zero_sub]
    have honePoint (x : Vec 2) : matVecMul (1 : Mat 2) (u.grad x) = G x :=
      congrFun (show (fun x => matVecMul (1 : Mat 2) (u.grad x)) = G by
        simpa only [u] using hone) x
    simp only [honePoint]
    linarith only [hsum]
  have henergy :
      Real.sqrt (integralAverage B (fun x => vecNormSq (u.grad x))) =
        Real.sqrt (1 / 2 : ℝ) := by
    have h := (integralAverage_vecNormSq_radialLogGradientField_planar
      (R := 1) (by norm_num)).2
    simp only [B, u, G] at h ⊢
    rw [h]
    norm_num
  have hlower : ∀ p : ℝ, 2 ≤ p →
      ∃ hgrad : MemLp (fun x => vecEuclideanNorm (u.grad x))
          (ENNReal.ofReal p) (volumeOn V),
        (1 / 2 : ℝ) * Real.rpow (Real.Gamma (p + 1)) (1 / p) - 1 ≤
          euclideanFieldLpMeanNormOn V (ENNReal.ofReal p) u.grad
            (memLp_normalizedVolumeOn_of_memLpOn hgrad
              (volume_euclideanBall_pos (0 : Vec 2) (by norm_num))) := by
    intro p hp
    obtain ⟨hgrad, hbound⟩ :=
      exists_memLp_radialLogGradientField_and_lpMeanNorm_lower_bound
        (d := 2) (by norm_num) 0 (R := (1 / 2 : ℝ))
        (p := p) (by norm_num) (by norm_num) (by linarith only [hp])
    refine ⟨?_, ?_⟩
    · simpa only [u, G, V] using hgrad
    · simpa only [u, G, V, div_eq_mul_inv, one_mul, mul_comm] using! hbound
  have hunbounded :
      ¬MemLp (fun x => vecEuclideanNorm (u.grad x)) ⊤ (volumeOn V) := by
    simpa only [u, G, V] using
      not_memLp_top_vecEuclideanNorm_radialLogGradientField_euclideanBall
        (d := 2) (by norm_num) 0 (R := (1 / 2 : ℝ)) (by norm_num)
  refine ⟨u, ?_, ?_, ?_, ?_, ?_, ?_, henergy, hlower, hunbounded⟩
  · intro x
    rfl
  · intro x i
    rfl
  · intro i
    simpa only [F, B] using hFcoord i
  · simpa only [F, B] using hFtop
  · simpa only [F, B] using hFtopNorm
  · simpa only [F] using hsol

end

end PDE.CZForcingSharpnessProof
