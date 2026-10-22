module

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

@[expose] public section

namespace PDE.CZOscillationSharpnessProof

open MeasureTheory Set
open Filter
open scoped ENNReal Topology

noncomputable section

theorem result
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    let β := Real.sqrt ((1 - δ) / (1 + δ))
    let B := euclideanBall (0 : Vec 2) 1
    let a : CoeffField 2 := fun x => (1 : Mat 2) + δ • radialReflectionMatrix x
    ∃ u : H1Function B,
      (∀ x, u.toFun x = x 0 * Real.rpow (vecEuclideanNorm x) (β - 1)) ∧
      (∀ x, u.grad x = radialModePowerField 0 β x) ∧
      IsWeakDivergenceFormSolutionOn a B u 0 0 ∧
      (∀ x, IsEllipticMatrix (1 - δ) (1 + δ) (a x)) ∧
      (∀ x, IsEllipticMatrix 1 ((1 + δ) / (1 - δ)) ((1 - δ)⁻¹ • a x)) ∧
      ((fun i j => integralAverage B (fun x => a x i j)) = (1 : Mat 2)) ∧
      (∀ (x : Vec 2) (ε : ℝ), IsMatrixPerturbationLE ε (a x) (1 : Mat 2) ↔ δ ≤ ε) ∧
      ∀ (p R : ℝ), 0 < p → 0 < R →
        (MemLp (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
          (volumeOn (euclideanBall (0 : Vec 2) R)) ↔ p * (1 - β) < 2) := by
  dsimp only
  let β : ℝ := Real.sqrt ((1 - δ) / (1 + δ))
  let B : Set (Vec 2) := euclideanBall (0 : Vec 2) 1
  let a : CoeffField 2 := fun x => (1 : Mat 2) + δ • radialReflectionMatrix x
  have hden : 0 < 1 + δ := by linarith
  have hnum : 0 < 1 - δ := by linarith
  have hratio0 : 0 < (1 - δ) / (1 + δ) := div_pos hnum hden
  have hratio1 : (1 - δ) / (1 + δ) < 1 := by
    exact (div_lt_one hden).2 (by linarith)
  have hβ0 : 0 < β := Real.sqrt_pos.2 hratio0
  have hβ1 : β < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by norm_num]
    exact Real.sqrt_lt_sqrt hratio0.le hratio1
  have hf : MemLp
      (fun x : Vec 2 => x 0 * Real.rpow (vecEuclideanNorm x) (β - 1)) 2
      (volume.restrict B) := by
    simpa only [B, ENNReal.ofReal_ofNat] using
      (memLp_coordinate_mul_vecEuclideanNorm_rpow_euclideanBall
        (d := 2) (by norm_num) (0 : Fin 2) hβ0 (by norm_num) (by norm_num : (0 : ℝ) < 2))
  have hGnorm : MemLp
      (fun x : Vec 2 => vecEuclideanNorm (radialModePowerField 0 β x)) 2
      (volume.restrict B) := by
    have hExp : -(2 : ℝ) < (β - 1) * 2 := by
      linarith only [hβ0]
    simpa only [B, ENNReal.ofReal_ofNat] using
      (memLp_vecEuclideanNorm_radialModePowerField_euclideanBall_iff
        (d := 2) (by norm_num) (0 : Fin 2) hβ0 hβ1.le (by norm_num)
          (by norm_num : (0 : ℝ) < 2)).2 hExp
  have hG : ∀ i : Fin 2, MemLp (fun x : Vec 2 => radialModePowerField 0 β x i) 2
      (volume.restrict B) := by
    intro i
    have hmeas : Measurable (fun x : Vec 2 => radialModePowerField 0 β x i) := by
      apply measurable_of_continuousOn_compl_singleton 0
      exact (contDiffOn_radialModePowerField_apply (0 : Fin 2) i β).continuousOn
    apply hGnorm.mono hmeas.aestronglyMeasurable
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (vecEuclideanNorm_nonneg (radialModePowerField 0 β x))] using
      (abs_apply_le_vecEuclideanNorm (radialModePowerField 0 β x) i)
  have hweak : HasWeakGradientOn B
      (fun x : Vec 2 => x 0 * Real.rpow (vecEuclideanNorm x) (β - 1))
      (radialModePowerField 0 β) := by
    apply hasWeakGradientOn_of_punctured_classicalGradient (d := 2) (by norm_num)
      (isOpen_euclideanBall _ _) hf hG
    · exact (contDiffOn_coordinate_mul_vecEuclideanNorm_rpow (0 : Fin 2) β).of_le
        (by norm_num) |>.mono (fun _ hx => hx.2)
    · intro x hx
      have hx0 : x ≠ 0 := by
        simpa only [Set.mem_singleton_iff] using hx.2
      exact classicalGradient_coordinate_mul_vecEuclideanNorm_rpow 0 β x
        hx0
  let u : H1Function B :=
    { toFun := fun x => x 0 * Real.rpow (vecEuclideanNorm x) (β - 1)
      grad := radialModePowerField 0 β
      memL2 := hf
      gradMemL2 := hG
      hasWeakGradient := hweak }
  have haEll : IsEllipticFieldOn (1 - δ) (1 + δ) B a := by
    refine ⟨?_, fun x _ => isEllipticMatrix_one_add_radialReflectionMatrix hδ0.le hδ1 x⟩
    refine (measurable_pi_iff).2 fun i => (measurable_pi_iff).2 fun j => ?_
    have hm : Measurable (fun x : Vec 2 => a x i j) := by
      dsimp only [a]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        radialReflectionMatrix, two_smul, Matrix.sub_apply,
        radialProjectionMatrix_apply]
      have hp := ((measurable_pi_apply i).mul (measurable_pi_apply j)).div
        continuous_vecNormSq.measurable
      exact measurable_const.add
        (((hp.add hp).sub measurable_const).const_mul δ)
    exact hm.piecewise (isOpen_euclideanBall _ _).measurableSet measurable_const
  have hdata : DivergenceFormL2DataOn a B u 0 0 :=
    DivergenceFormL2DataOn.of_isEllipticFieldOn haEll MeasureTheory.MemLp.zero
      (fun _ => MeasureTheory.MemLp.zero)
  have hflux : (fun x => matVecMul (a x) (u.grad x)) =
      radialCoefficientFlux δ 0 β := by
    rfl
  have hzeroFlux : ∀ φ : WeakTestFunction B,
      ∫ x in B, vecDot (radialCoefficientFlux δ 0 β x) (φ.grad x) = 0 := by
    apply integral_vecDot_grad_eq_zero_of_classical_divergence_punctured
      (d := 2) (by norm_num) (isOpen_euclideanBall _ _) _
    · simpa only [← hflux] using! hdata.flux_memL2
    · intro i
      exact (contDiffOn_radialCoefficientFlux_apply δ β 0 i).of_le (by norm_num) |>.mono
        (fun _ hx => hx.2)
    · intro x hx
      have hx0 : x ≠ 0 := by
        simpa only [Set.mem_singleton_iff] using hx.2
      exact sum_classicalGradient_radialCoefficientFlux_sqrt_eq_zero
        δ hδ0.le hδ1 0 x hx0
  have hsol : IsWeakDivergenceFormSolutionOn a B u 0 0 := by
    intro φ
    refine ⟨hdata.testable φ, ?_⟩
    change (∫ x in B, vecDot (radialCoefficientFlux δ 0 β x) (φ.grad x)) = _
    rw [hzeroFlux φ]
    simp [vecDot]
  refine ⟨u, ?_, ?_, hsol, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rfl
  · intro x
    rfl
  · intro x
    exact isEllipticMatrix_one_add_radialReflectionMatrix hδ0.le hδ1 x
  · intro x
    exact isEllipticMatrix_normalized_radialReflectionMatrix hδ0.le hδ1 x
  · exact integralAverage_one_add_planarRadialReflectionMatrix (by norm_num) δ
  · intro x ε
    rw [isMatrixPerturbationLE_one_add_radialReflectionMatrix_iff (by norm_num)]
    rw [abs_of_pos hδ0]
  · intro p R hp hR
    rw [show (fun x => vecEuclideanNorm (u.grad x)) =
        (fun x => vecEuclideanNorm (radialModePowerField 0 β x)) by rfl]
    rw [memLp_vecEuclideanNorm_radialModePowerField_euclideanBall_iff
      (d := 2) (by norm_num) (0 : Fin 2) hβ0 hβ1.le hR hp]
    change (-2 < (β - 1) * p) ↔ p * (1 - β) < 2
    constructor <;> intro h <;> nlinarith only [h]

end

end PDE.CZOscillationSharpnessProof
