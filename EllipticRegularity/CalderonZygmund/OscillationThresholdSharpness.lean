module

public import EllipticRegularity.CalderonZygmund.OscillationSharpness
public import EllipticRegularity.CalderonZygmund.HigherDimensionalOscillationSharpness
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

/-- Any proposed normalized coefficient-smallness threshold asymptotically
larger than order `1/p` admits arbitrarily large critical counterexamples. -/
theorem exists_normalized_critical_obstruction_below_threshold
    (n : ℕ) (ε : ℝ → ℝ)
    (hε : Tendsto (fun p => p * ε p) atTop atTop) (P : ℝ) :
    ∃ p : ℝ, P ≤ p ∧ 4 ≤ p ∧
      let β := 1 - 2 / p
      let δ := (1 - β ^ 2) / (1 + β ^ 2)
      let B := euclideanBall (0 : Vec (2 + n)) 1
      let a : CoeffField (2 + n) := fun z =>
        matAppend
          ((1 - δ)⁻¹ • ((1 : Mat 2) +
            δ • radialReflectionMatrix (vecAppendEquiv 2 n z).1))
          (1 : Mat n)
      ∃ u : H1Function B,
        (∀ i j, AEMeasurable (fun z => a z i j) (volumeOn B)) ∧
        (∀ z, IsEllipticMatrix 1 4 (a z)) ∧
        IsWeakDivergenceFormSolutionOn a B u 0 0 ∧
        (∀ z, IsMatrixPerturbationLE (ε p) (a z)
          (fun i j => integralAverage B (fun y => a y i j))) ∧
        ¬MemLp (fun z => vecEuclideanNorm (u.grad z)) (ENNReal.ofReal p)
          (volumeOn (euclideanBall (0 : Vec (2 + n)) (1 / 2 : ℝ))) := by
  have hupper : ∀ᶠ p : ℝ in atTop,
      p * ((1 - (1 - 2 / p) ^ 2) / (1 + (1 - 2 / p) ^ 2)) /
        (1 - ((1 - (1 - 2 / p) ^ 2) / (1 + (1 - 2 / p) ^ 2))) < 3 :=
    tendsto_mul_critical_normalized_oscillation_parameter.eventually_lt_const
      (by norm_num)
  have hlower : ∀ᶠ p : ℝ in atTop, 3 ≤ p * ε p :=
    hε.eventually_ge_atTop 3
  have hlarge : ∀ᶠ p : ℝ in atTop,
      (p * ((1 - (1 - 2 / p) ^ 2) / (1 + (1 - 2 / p) ^ 2)) /
          (1 - ((1 - (1 - 2 / p) ^ 2) / (1 + (1 - 2 / p) ^ 2))) < 3) ∧
        3 ≤ p * ε p ∧ 4 ≤ p ∧ P ≤ p := by
    filter_upwards [hupper, hlower, eventually_ge_atTop (4 : ℝ),
      eventually_ge_atTop P] with p hup hlo hp4 hpP
    exact ⟨hup, hlo, hp4, hpP⟩
  obtain ⟨p, hscaledUpper, hscaledLower, hp4, hpP⟩ := hlarge.exists
  have hp2 : 2 < p := lt_of_lt_of_le (by norm_num) hp4
  let β : ℝ := 1 - 2 / p
  let δ : ℝ := (1 - β ^ 2) / (1 + β ^ 2)
  rcases radialMode_critical_parameter p hp2 with
    ⟨_hβ0, _hβ1, hδ0, hδ1, _hβsqrt, _hδformula, _hcritical⟩
  have hp0 : 0 < p := lt_trans (by norm_num) hp2
  have hscaledUpper' : p * (δ / (1 - δ)) < 3 := by
    calc
      p * (δ / (1 - δ)) = p * δ / (1 - δ) := by ring
      _ < 3 := by simpa only [β, δ] using hscaledUpper
  have hδeps : δ / (1 - δ) ≤ ε p := by
    exact le_of_mul_le_mul_left (hscaledUpper'.le.trans hscaledLower) hp0
  have hε0 : 0 ≤ ε p := by
    have hδnorm0 : 0 < δ / (1 - δ) := div_pos hδ0 (by linarith)
    exact hδnorm0.le.trans hδeps
  rcases exists_higherDimensional_critical_radialMode_obstruction n p hp2 with
    ⟨u, _hu, _hgrad, _hsolBase, _hellBase, hellNorm, hsolNorm,
      _haverageBase, _hperturbBase, havgNorm, hpertNorm, hhalfNot, _hballNot⟩
  refine ⟨p, hpP, hp4, u, ?_, ?_, hsolNorm, ?_, hhalfNot⟩
  · intro i j
    exact (measurable_matAppend_smul_one_add_planarRadialReflectionMatrix_apply
      n (1 - δ)⁻¹ δ i j).aemeasurable
  · intro z
    exact (hellNorm z).mono (by norm_num) le_rfl
      (critical_normalized_ellipticity_ratio_le_four p hp4)
  · intro z
    rw [havgNorm]
    exact (hpertNorm z (ε p) hε0).2 hδeps

end

end PDE
