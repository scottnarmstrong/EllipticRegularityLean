module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Passing to the limit `δ → 0` in an `ℝ≥0∞` inequality
-/

@[expose] public section

open Filter Topology
open scoped ENNReal

namespace PDE.DGNMMoser

/-- If `S ≤ K (E + δ W)` for every `δ > 0` and `W < ∞`, then `S ≤ K E`. -/
theorem le_mul_of_forall_delta {S E W : ℝ≥0∞} {K : ℝ} (hW : W ≠ ⊤)
    (h : ∀ δ : ℝ, 0 < δ → S ≤ ENNReal.ofReal K * (E + ENNReal.ofReal δ * W)) :
    S ≤ ENNReal.ofReal K * E := by
  have h0 : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using this
  have h1 : Tendsto (fun n : ℕ => ENNReal.ofReal K *
      (E + ENNReal.ofReal (1 / ((n : ℝ) + 1)) * W)) atTop
      (𝓝 (ENNReal.ofReal K * (E + 0 * W))) := by
    refine ENNReal.Tendsto.const_mul (tendsto_const_nhds.add
      (ENNReal.Tendsto.mul_const h0 (Or.inr hW))) (Or.inr ENNReal.ofReal_ne_top)
  simp only [zero_mul, add_zero] at h1
  exact ge_of_tendsto' h1 fun n => h _ (by positivity)

end PDE.DGNMMoser
