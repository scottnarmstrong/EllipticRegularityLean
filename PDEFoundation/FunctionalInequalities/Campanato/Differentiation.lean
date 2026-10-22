module

public import PDEFoundation.FunctionalInequalities.Campanato.Averages
public import PDEFoundation.Measure.AxisBoxVolume
public import PDEFoundation.Geometry.EuclideanBall
public import Mathlib.MeasureTheory.Covering.DensityTheorem

/-!
# Lebesgue differentiation along round balls

Mathlib's differentiation theorem uses supremum-norm balls on `Vec d`. A round ball of radius `δ`
sits inside the supremum ball of radius `δ`, with volume ratio independent of `δ`, so the round
averages also converge at almost every point.
-/

@[expose] public section

namespace PDE.CampanatoProof

open MeasureTheory Filter Topology

variable {d : ℕ}

/-- A round ball is contained in the supremum ball of the same radius. -/
theorem euclideanBall_subset_closedBall {x : Vec d} {δ : ℝ} (hδ : 0 < δ) :
    euclideanBall x δ ⊆ Metric.closedBall x δ :=
  (euclideanBall_subset_supBall hδ).trans Metric.ball_subset_closedBall

/-- **Lebesgue differentiation on round balls.** -/
theorem ae_tendsto_integralAverage_euclideanBall {u : Vec d → ℝ}
    (hu : LocallyIntegrable u volume) :
    ∀ᵐ x ∂(volume : Measure (Vec d)),
      Tendsto (fun ρ : ℝ => integralAverage (euclideanBall x ρ) u) (𝓝[>] 0) (𝓝 (u x)) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub
    (μ := (volume : Measure (Vec d))) hu 1] with x hx
  have hlim := hx (l := 𝓝[>] (0 : ℝ)) (fun _ => x) id tendsto_id
    (by
      filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
      exact Metric.mem_closedBall_self (by simp only [id, one_mul]; linarith))
  set ω : ℝ := (volume (euclideanBall (0 : Vec d) 1)).toReal with hω
  have hωpos : 0 < ω := volume_euclideanBall_toReal_pos _ (by norm_num)
  set C : ℝ := 2 ^ d / ω with hC
  have hbound : ∀ δ : ℝ, 0 < δ →
      |integralAverage (euclideanBall x δ) u - u x| ≤
        C * ⨍ y in Metric.closedBall x δ, ‖u y - u x‖ ∂volume := by
    intro δ hδ
    have hQint : IntegrableOn (fun y => |u y - u x|) (Metric.closedBall x δ) volume :=
      ((hu.integrableOn_isCompact (isCompact_closedBall x δ)).sub
        (integrableOn_const (measure_closedBall_lt_top (x := x) (r := δ)).ne)).abs
    have hQfin : volume (Metric.closedBall x δ) ≠ ⊤ := measure_closedBall_lt_top.ne
    have hsub := euclideanBall_subset_closedBall (x := x) hδ
    have hEint : IntegrableOn u (euclideanBall x δ) volume :=
      (hu.integrableOn_isCompact (isCompact_closedBall x δ)).mono_set hsub
    have h1 := abs_integralAverage_sub_le (u x) hEint (volume_euclideanBall_pos x hδ)
      (volume_euclideanBall_ne_top x hδ.le)
    have h2 := integralAverage_le_of_subset hsub (volume_euclideanBall_pos x hδ) hQfin hQint
      (h := fun y => |u y - u x|) (fun _ => abs_nonneg _)
    have hcube := closedCenteredAxisCube_eq_metric_closedBall x hδ.le
    have hvQ : (volume (Metric.closedBall x δ)).toReal = (2 * δ) ^ d := by
      rw [← hcube]; exact volume_closedCenteredAxisCube_toReal x hδ.le
    have hvE := volume_euclideanBall_toReal_eq_unit_mul_of_pos x hδ
    have hratio : (volume (Metric.closedBall x δ)).toReal / (volume (euclideanBall x δ)).toReal
        = C := by
      rw [hvQ, hvE, ← hω, hC, mul_pow]
      have : 0 < δ ^ d := by positivity
      field_simp
    rw [hratio] at h2
    have h3 : integralAverage (Metric.closedBall x δ) (fun y => |u y - u x|) =
        ⨍ y in Metric.closedBall x δ, ‖u y - u x‖ ∂volume := by
      simp only [integralAverage, setAverage_eq, Measure.real, smul_eq_mul, Real.norm_eq_abs]
    rw [h3] at h2
    exact h1.trans h2
  have hT : Tendsto (fun δ : ℝ => |integralAverage (euclideanBall x δ) u - u x|) (𝓝[>] 0)
      (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ (by
      simpa using (hlim.const_mul C))
    filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ) using hbound δ hδ
  exact tendsto_iff_norm_sub_tendsto_zero.2 (by simpa only [Real.norm_eq_abs] using hT)

end PDE.CampanatoProof
