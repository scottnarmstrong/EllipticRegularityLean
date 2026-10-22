module

public import PDEFoundation.Sobolev.W1p.LevelSets
public import PDEFoundation.Sobolev.W1p.Clamps
public import PDEFoundation.Sobolev.W1p.Mean

/-!
# Dyadic layers of a `W^{1,1}` function and measurable sets carrying half the volume

The layer `min ((v - a)_+, a)` of a nonnegative `W^{1,1}` function is built from the interval
truncation and a constant shift; its gradient is the indicator of `{a < v < 2 a}` times `∇ v`.
A set of at least half of the volume on which `v` vanishes contains a measurable subset with the
same property.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE

variable {d : ℕ} {W : Set (Vec d)}

namespace W1pFunction

/-- The Euclidean gradient magnitude of a `W^{1,p}` function is a.e. measurable. -/
theorem aemeasurable_vecEuclideanNorm_grad {p : ℝ≥0∞} (u : W1pFunction W p) :
    AEMeasurable (fun y => vecEuclideanNorm (u.grad y)) (volumeOn W) :=
  continuous_vecEuclideanNorm.measurable.comp_aemeasurable
    (aemeasurable_pi_iff.2 fun i => (u.grad_memLp i).aestronglyMeasurable.aemeasurable)

/-- The dyadic layer `min ((v - a)_+, a)` of a `W^{1,1}` function, as the interval truncation
`min (max v a) (2 a)` shifted by `-a`. -/
noncomputable def layer (hW : IsOpenBoundedConvexDomain W) (v : W1pFunction W 1) (a : ℝ) :
    W1pFunction W 1 :=
  letI : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩
  letI := hW.isFiniteMeasure_volumeOn
  (v.clampConst hW le_rfl ENNReal.one_ne_top a (2 * a)).addConst (-a)

theorem layer_toFun (hW : IsOpenBoundedConvexDomain W) (v : W1pFunction W 1) (a : ℝ) (x : Vec d) :
    (v.layer hW a).toFun x = min (max (v.toFun x) a) (2 * a) - a := by
  change (v.clampConst hW le_rfl ENNReal.one_ne_top a (2 * a)).toFun x + -a = _
  rw [clampConst_toFun]
  ring

theorem layer_grad (hW : IsOpenBoundedConvexDomain W) (v : W1pFunction W 1) (a : ℝ) (x : Vec d) :
    (v.layer hW a).grad x = {y | a < v.toFun y ∧ v.toFun y < 2 * a}.indicator v.grad x := by
  let : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩
  let := hW.isFiniteMeasure_volumeOn
  change ((v.clampConst hW le_rfl ENNReal.one_ne_top a (2 * a)).addConst (-a)).grad x = _
  rw [addConst_grad, clampConst_grad]

theorem layer_nonneg (hW : IsOpenBoundedConvexDomain W) (v : W1pFunction W 1) {a : ℝ}
    (ha : 0 ≤ a) (x : Vec d) : 0 ≤ (v.layer hW a).toFun x := by
  rw [layer_toFun]
  have : a ≤ min (max (v.toFun x) a) (2 * a) :=
    le_min (le_max_right _ _) (by linarith)
  linarith

theorem layer_eq_zero (hW : IsOpenBoundedConvexDomain W) (v : W1pFunction W 1) {a : ℝ}
    (ha : 0 ≤ a) {x : Vec d} (hx : v.toFun x = 0) : (v.layer hW a).toFun x = 0 := by
  rw [layer_toFun, hx, max_eq_right ha, min_eq_left (by linarith)]
  ring

theorem layer_eq_of_le (hW : IsOpenBoundedConvexDomain W) (v : W1pFunction W 1) {a : ℝ}
    {x : Vec d} (hx : 2 * a ≤ v.toFun x) (ha : 0 ≤ a) : (v.layer hW a).toFun x = a := by
  rw [layer_toFun, max_eq_left (by linarith), min_eq_right hx]
  ring

end W1pFunction

/-- A measurable subset of the zero set carrying half of the volume of `W`. -/
theorem exists_measurable_zero_set (hW : MeasurableSet W) {v : Vec d → ℝ} (hv : AEMeasurable v (volumeOn W))
    (hhalf : volume W ≤ 2 * volumeOn W {x | v x = 0}) :
    ∃ S : Set (Vec d), MeasurableSet S ∧ S ⊆ W ∧ (∀ x ∈ S, v x = 0) ∧
      volume W ≤ 2 * volume S := by
  have hnull : NullMeasurableSet {x | v x = 0} (volumeOn W) :=
    hv.nullMeasurable (measurableSet_singleton 0)
  obtain ⟨t, htA, htm, hte⟩ := hnull.exists_measurable_subset_ae_eq
  refine ⟨t ∩ W, ?_, inter_subset_right, ?_, ?_⟩
  · exact htm.inter hW
  · intro x hx
    exact htA hx.1
  · have : volume (t ∩ W) = volumeOn W {x | v x = 0} := by
      rw [← measure_congr hte, Measure.restrict_apply htm]
    rw [this]; exact hhalf

end PDE
