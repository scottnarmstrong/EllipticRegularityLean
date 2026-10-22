module

public import PDEFoundation.Analysis.Gehring.CubeMaximal
public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Measure.Doubling
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Lebesgue differentiation for the cube maximal function

For a locally integrable `k`, `‖k x‖ₑ ≤ cubeMaximal k x` for almost every `x`.
-/

@[expose] public section

namespace PDE.Gehring

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- **Lebesgue differentiation** (`x.lebesgueDiff`): a locally integrable function is
almost everywhere dominated by its uncentered cube maximal function. -/
theorem ae_enorm_le_cubeMaximal {d : ℕ} {k : Vec d → ℝ}
    (hk : LocallyIntegrable k volume) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), ‖k x‖ₑ ≤ cubeMaximal k x := by
  have hkn : LocallyIntegrable (fun y => ‖k y‖) volume := fun x => (hk x).norm
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average (μ := (volume : Measure (Vec d)))
    hkn 1] with x hx
  have hlim := hx (l := 𝓝[>] (0 : ℝ)) (fun _ => x) id tendsto_id
    (by
      filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
      exact Metric.mem_closedBall_self (by simp only [id, one_mul]; linarith))
  have hle : ∀ δ : ℝ, 0 < δ →
      ENNReal.ofReal (⨍ y in Metric.closedBall x δ, ‖k y‖ ∂volume) ≤ cubeMaximal k x := by
    intro δ hδ
    have hcube : closedCenteredAxisCube x δ = Metric.closedBall x δ :=
      closedCenteredAxisCube_eq_metric_closedBall x hδ.le
    have hint : IntegrableOn (fun y => ‖k y‖) (Metric.closedBall x δ) volume :=
      hkn.integrableOn_isCompact (isCompact_closedBall x δ)
    refine le_trans ?_ (cubeAvg_le_cubeMaximal k (c := x) (r := δ) hδ
      (Metric.mem_closedBall_self hδ.le |> fun h => hcube ▸ h))
    unfold cubeAvg
    have hvol : (volume (Metric.closedBall x δ)).toReal = (2 * δ) ^ d := by
      rw [← hcube]; exact volume_closedCenteredAxisCube_toReal x hδ.le
    have hvol' : volume (Metric.closedBall x δ) = ENNReal.ofReal ((2 * δ) ^ d) := by
      rw [← hcube]; exact volume_closedCenteredAxisCube x hδ.le
    have hpos : 0 < (2 * δ) ^ d := by positivity
    rw [hcube, setAverage_eq, smul_eq_mul, Measure.real, hvol, hvol',
      ENNReal.ofReal_mul (inv_nonneg.2 hpos.le), ENNReal.ofReal_inv_of_pos hpos,
      ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => norm_nonneg _),
      div_eq_mul_inv, mul_comm]
    simp only [ofReal_norm, le_refl]
  have h2 : Tendsto (fun δ : ℝ => ENNReal.ofReal (⨍ y in Metric.closedBall x δ, ‖k y‖ ∂volume))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal ‖k x‖)) :=
    ENNReal.tendsto_ofReal hlim
  have h3 := le_of_tendsto h2 (eventually_nhdsWithin_of_forall fun δ (hδ : 0 < δ) => hle δ hδ)
  rwa [ofReal_norm] at h3

end PDE.Gehring
