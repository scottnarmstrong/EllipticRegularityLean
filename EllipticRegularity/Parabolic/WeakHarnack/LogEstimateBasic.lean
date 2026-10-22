module

public import EllipticRegularity.Parabolic.WeakHarnack.MeasuresLogTail
public import EllipticRegularity.Parabolic.WeakHarnack.WeightedPoincareCutoff
public import EllipticRegularity.Parabolic.WeakSlice.Flux

/-!
# Basic facts about the weighted measure `ν = ζ² dx / ∫ζ²` used in the logarithmic estimate

* `cutoffZ d = ∫_{B₁} ζ²`, with `cutoffMass d = ofReal (cutoffZ d)`;
* `integral_cutoffMeasure`: `∫ f dν = (∫_{B₁} f ζ²) / ∫_{B₁} ζ²`;
* `cutoffMeasure_le_smul`: `ν ≤ (cutoffMass)⁻¹ • vol|_{B₁}` and consequent `L²` transfer;
* a gradient bound `|∇ζ|² ≤ logGradBound d`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Parabolic.WeakHarnack

variable {d : ℕ}

/-- `∫_{B₁} ζ²`. -/
noncomputable def cutoffZ (d : ℕ) : ℝ := ∫ x in euclideanBall (0 : Vec d) 1, radialCutoff d x ^ 2

theorem cutoffMass_eq_ofReal (d : ℕ) : cutoffMass d = ENNReal.ofReal (cutoffZ d) := by
  unfold cutoffMass cutoffZ
  rw [ofReal_integral_eq_lintegral_ofReal]
  · have hfin : IsFiniteMeasure (volume.restrict (euclideanBall (0 : Vec d) 1)) :=
      isFiniteMeasure_restrict.mpr (volume_euclideanBall_ne_top 0 zero_le_one)
    refine Integrable.mono' (g := fun _ => (1 : ℝ)) (integrable_const _)
      ((measurable_radialCutoff d).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    have h0 := radialCutoff_nonneg (d := d) x
    have h1 := radialCutoff_le_one (d := d) x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith
  · exact Filter.Eventually.of_forall fun x => sq_nonneg _

theorem cutoffZ_pos (d : ℕ) : 0 < cutoffZ d := by
  have h := cutoffMass_pos d
  rw [cutoffMass_eq_ofReal] at h
  by_contra hle
  exact h (ENNReal.ofReal_eq_zero.2 (not_lt.1 hle))

theorem integral_cutoffMeasure (f : Vec d → ℝ) :
    ∫ x, f x ∂(cutoffMeasure d) =
      (cutoffZ d)⁻¹ * ∫ x in euclideanBall (0 : Vec d) 1, radialCutoff d x ^ 2 * f x := by
  have hmeas : Measurable fun x : Vec d => ENNReal.ofReal (radialCutoff d x ^ 2) :=
    ENNReal.measurable_ofReal.comp ((measurable_radialCutoff d).pow_const 2)
  have h1 := integral_withDensity_eq_integral_toReal_smul (μ := volume.restrict
    (euclideanBall (0 : Vec d) 1)) hmeas
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top) f
  unfold cutoffMeasure
  rw [integral_smul_measure (G := ℝ), h1, cutoffMass_eq_ofReal, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (cutoffZ_pos d).le, smul_eq_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (sq_nonneg _)]

theorem cutoffMeasure_le_smul (d : ℕ) :
    cutoffMeasure d ≤ (cutoffMass d)⁻¹ • volume.restrict (euclideanBall (0 : Vec d) 1) := by
  unfold cutoffMeasure
  have hle : (volume.restrict (euclideanBall (0 : Vec d) 1)).withDensity
      (fun x => ENNReal.ofReal (radialCutoff d x ^ 2)) ≤
      volume.restrict (euclideanBall (0 : Vec d) 1) := by
    refine Measure.le_iff.2 fun s hs => ?_
    rw [withDensity_apply _ hs]
    refine (lintegral_mono fun x => ?_).trans_eq (by rw [lintegral_const, Measure.restrict_apply_univ, one_mul])
    have h0 := radialCutoff_nonneg (d := d) x
    have h1 := radialCutoff_le_one (d := d) x
    calc ENNReal.ofReal (radialCutoff d x ^ 2) ≤ ENNReal.ofReal 1 :=
          ENNReal.ofReal_le_ofReal (by nlinarith)
      _ = 1 := by simp
  intro s
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul' le_rfl (hle s)

theorem memLp_cutoffMeasure {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict (euclideanBall (0 : Vec d) 1))) :
    MemLp f 2 (cutoffMeasure d) :=
  (hf.of_measure_le_smul (by simpa using cutoffMass_pos d) (cutoffMeasure_le_smul d))

theorem cutoffMeasure_ac (d : ℕ) :
    cutoffMeasure d ≪ volume.restrict (euclideanBall (0 : Vec d) 1) := by
  refine Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_
  have := cutoffMeasure_le_smul d s
  simp only [Measure.smul_apply, h0, smul_zero, nonpos_iff_eq_zero] at this
  exact this

end PDE.Parabolic.WeakHarnack
