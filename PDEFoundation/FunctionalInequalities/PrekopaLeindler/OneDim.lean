module

public import PDEFoundation.FunctionalInequalities.PrekopaLeindler.OneDimBounded
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# One-dimensional Prékopa--Leindler for `[0,∞]`-valued measurable functions

Truncation of the bounded case.
-/

@[expose] public section

namespace PDE.PrekopaLeindlerProof

open MeasureTheory Set Filter
open scoped ENNReal Pointwise Topology

/-- The truncations `min (f x) n` increase to `f`, and so do their integrals. -/
theorem tendsto_lintegral_truncate {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    Tendsto (fun n : ℕ => ∫⁻ x, min (f x) n) atTop (𝓝 (∫⁻ x, f x)) := by
  have hmono : Monotone fun (n : ℕ) (x : ℝ) => min (f x) (n : ℝ≥0∞) := fun m n hmn x =>
    min_le_min le_rfl (by exact_mod_cast hmn)
  have hsup : ∀ x, (⨆ n : ℕ, min (f x) (n : ℝ≥0∞)) = f x := fun x => by
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  have := lintegral_iSup (μ := volume) (fun n => hf.min measurable_const) hmono
  simp only [hsup] at this
  rw [this]
  exact tendsto_atTop_iSup fun m n hmn => lintegral_mono fun x => hmono hmn x

/-- One-dimensional Prékopa--Leindler for measurable `[0,∞]`-valued functions. -/
theorem oneDim {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) {f g k : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hk : Measurable k)
    (hyp : ∀ x y, f x ^ l * g y ^ (1 - l) ≤ k (l • x + (1 - l) • y)) :
    (∫⁻ x, f x) ^ l * (∫⁻ x, g x) ^ (1 - l) ≤ ∫⁻ x, k x := by
  have hl' : 0 < 1 - l := sub_pos.2 hl1
  by_cases hF : ∫⁻ x, f x = 0
  · simp [hF, ENNReal.zero_rpow_of_pos hl0]
  by_cases hG : ∫⁻ x, g x = 0
  · simp [hG, ENNReal.zero_rpow_of_pos hl']
  have hbound : ∀ n : ℕ, (∫⁻ x, min (f x) n) ^ l * (∫⁻ x, min (g x) n) ^ (1 - l) ≤ ∫⁻ x, k x :=
    fun n => oneDim_bounded hl0 hl1 (hf.min measurable_const) (hg.min measurable_const) hk
      (ENNReal.natCast_ne_top n) (ENNReal.natCast_ne_top n) (fun x => min_le_right _ _)
      (fun x => min_le_right _ _) fun x y => by
        calc _ ≤ f x ^ l * g y ^ (1 - l) := by
              gcongr <;> exact min_le_left _ _
          _ ≤ _ := hyp x y
  have hFl : (∫⁻ x, f x) ^ l ≠ 0 := by
    rw [Ne, ENNReal.rpow_eq_zero_iff]
    rintro (⟨h, _⟩ | ⟨_, h⟩)
    · exact hF h
    · linarith
  have hGl : (∫⁻ x, g x) ^ (1 - l) ≠ 0 := by
    rw [Ne, ENNReal.rpow_eq_zero_iff]
    rintro (⟨h, _⟩ | ⟨_, h⟩)
    · exact hG h
    · linarith
  have hlim := ENNReal.Tendsto.mul
    (((ENNReal.continuous_rpow_const (y := l)).tendsto _).comp (tendsto_lintegral_truncate hf))
    (Or.inl hFl)
    (((ENNReal.continuous_rpow_const (y := 1 - l)).tendsto _).comp (tendsto_lintegral_truncate hg))
    (Or.inl hGl)
  exact le_of_tendsto' hlim hbound

end PDE.PrekopaLeindlerProof
