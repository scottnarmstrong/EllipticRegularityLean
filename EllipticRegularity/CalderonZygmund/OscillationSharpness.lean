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

public import CZStatements.OscillationSharpness

@[expose] public section

namespace PDE

open MeasureTheory Set
open Filter
open scoped ENNReal Topology

noncomputable section

/-- At every exponent above two, the critical planar radial mode is an actual
weak solution whose gradient fails to belong to the critical `Lᵖ` space. -/
theorem exists_planar_critical_radialMode_obstruction (p : ℝ) (hp : 2 < p) :
    let β := 1 - 2 / p
    let δ := (1 - β ^ 2) / (1 + β ^ 2)
    let B := euclideanBall (0 : Vec 2) 1
    let a : CoeffField 2 := fun x => (1 : Mat 2) + δ • radialReflectionMatrix x
    ∃ u : H1Function B,
      (∀ x, u.toFun x = x 0 * Real.rpow (vecEuclideanNorm x) (β - 1)) ∧
      (∀ x, u.grad x = radialModePowerField 0 β x) ∧
      IsWeakDivergenceFormSolutionOn a B u 0 0 ∧
      ((fun i j => integralAverage B (fun x => a x i j)) = (1 : Mat 2)) ∧
      (∀ (x : Vec 2) (ε : ℝ),
        IsMatrixPerturbationLE ε (a x) (1 : Mat 2) ↔ δ ≤ ε) ∧
      (∀ x, IsEllipticMatrix 1 ((1 + δ) / (1 - δ)) ((1 - δ)⁻¹ • a x)) ∧
      ¬MemLp (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
        (volumeOn B) := by
  dsimp only
  let β : ℝ := 1 - 2 / p
  let δ : ℝ := (1 - β ^ 2) / (1 + β ^ 2)
  let B : Set (Vec 2) := euclideanBall (0 : Vec 2) 1
  let a : CoeffField 2 := fun x => (1 : Mat 2) + δ • radialReflectionMatrix x
  rcases radialMode_critical_parameter p hp with
    ⟨_hβ0, _hβ1, hδ0, hδ1, hβsqrt, _hδformula, hcritical⟩
  have hconstruction := exists_planar_radialMode_sharpness δ hδ0 hδ1
  dsimp only at hconstruction
  rcases hconstruction with
    ⟨u, hu, hgrad, hsol, _hell, hnormalized, haverage, hperturbation, hLp⟩
  refine ⟨u, ?_, ?_, hsol, haverage, hperturbation, hnormalized, ?_⟩
  · intro x
    rw [hu x, ← hβsqrt]
  · intro x
    rw [hgrad x, ← hβsqrt]
  · intro hmem
    have hp0 : 0 < p := lt_trans (by norm_num) hp
    have hthreshold := (hLp p 1 hp0 (by norm_num)).1 hmem
    rw [← hβsqrt, hcritical] at hthreshold
    exact (lt_irrefl 2) hthreshold

/-- The critical coefficient oscillation has the exact asymptotic size `2/p`. -/
theorem tendsto_mul_critical_oscillation_parameter :
    Tendsto
      (fun p : ℝ =>
        p * ((1 - (1 - 2 / p) ^ 2) / (1 + (1 - 2 / p) ^ 2)))
      atTop (𝓝 2) := by
  apply tendsto_mul_radialMode_critical_parameter.congr'
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with p hp
  rcases radialMode_critical_parameter p hp with
    ⟨_hβ0, _hβ1, _hδ0, _hδ1, _hβsqrt, hδformula, _hcritical⟩
  rw [hδformula]

/-- For critical exponents at least four, normalization by the lower
ellipticity constant keeps the upper ellipticity ratio bounded by four. -/
theorem critical_normalized_ellipticity_ratio_le_four
    (p : ℝ) (hp : 4 ≤ p) :
    let β := 1 - 2 / p
    let δ := (1 - β ^ 2) / (1 + β ^ 2)
    (1 + δ) / (1 - δ) ≤ 4 := by
  dsimp only
  let β : ℝ := 1 - 2 / p
  let δ : ℝ := (1 - β ^ 2) / (1 + β ^ 2)
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have htwoDiv : 2 / p ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hp0).2
    nlinarith
  have hβhalf : (1 / 2 : ℝ) ≤ β := by
    dsimp only [β]
    linarith
  have hβsq : (1 / 2 : ℝ) ^ 2 ≤ β ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self (by norm_num) hβhalf
  have hβsqPos : 0 < β ^ 2 := sq_pos_of_pos (lt_of_lt_of_le (by norm_num) hβhalf)
  have hbaseDen : 0 < 1 + β ^ 2 := by positivity
  have hratio : (1 + δ) / (1 - δ) = 1 / β ^ 2 := by
    dsimp only [δ]
    field_simp [hβsqPos.ne', hbaseDen.ne']
    ring
  rw [hratio]
  apply (div_le_iff₀ hβsqPos).2
  nlinarith

/-- After normalization by the lower ellipticity constant, the critical
oscillation threshold still has sharp asymptotic size `2/p`. -/
theorem tendsto_mul_critical_normalized_oscillation_parameter :
    Tendsto
      (fun p : ℝ =>
        let δ := (1 - (1 - 2 / p) ^ 2) / (1 + (1 - 2 / p) ^ 2)
        p * δ / (1 - δ))
      atTop (𝓝 2) := by
  let δ : ℝ → ℝ := fun p =>
    (1 - (1 - 2 / p) ^ 2) / (1 + (1 - 2 / p) ^ 2)
  have hscaled : Tendsto (fun p => p * δ p) atTop (𝓝 2) := by
    simpa only [δ] using tendsto_mul_critical_oscillation_parameter
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have hproduct : Tendsto (fun p => (p * δ p) * p⁻¹) atTop (𝓝 0) := by
      simpa only [mul_zero] using hscaled.mul tendsto_inv_atTop_zero
    apply hproduct.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with p hp
    have hpne : p ≠ 0 := ne_of_gt hp
    field_simp [hpne]
  have hden : Tendsto (fun p => 1 - δ p) atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hδ
  change Tendsto (fun p => (p * δ p) / (1 - δ p)) atTop (𝓝 2)
  convert hscaled.div hden (by norm_num : (1 : ℝ) ≠ 0) using 1
  norm_num


end

end PDE
