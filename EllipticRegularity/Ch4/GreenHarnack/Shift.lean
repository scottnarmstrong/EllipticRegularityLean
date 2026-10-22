module

public import Mathlib.MeasureTheory.Function.EssSup
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Essential extrema of shifted functions and the `δ → 0` limit

Elementary `ℝ≥0∞` facts used to pass from the Harnack inequality for `u + δ` to the Harnack
inequality for `u`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4GreenHarnack

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem essSup_add_const_le [NeZero μ] (f : α → ℝ≥0∞) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    essSup f μ + c ≤ essSup (fun x => f x + c) μ := by
  set b := essSup (fun x => f x + c) μ
  have hae : ∀ᵐ x ∂μ, f x + c ≤ b := ENNReal.ae_le_essSup _
  have hcb : c ≤ b := by
    obtain ⟨_, hx⟩ := hae.exists
    exact le_add_self.trans hx
  have h1 : essSup f μ ≤ b - c :=
    essSup_le_of_ae_le _ (hae.mono fun x hx => ENNReal.le_sub_of_add_le_right hc hx)
  calc essSup f μ + c ≤ b - c + c := by gcongr
    _ = b := tsub_add_cancel_of_le hcb

theorem essInf_add_const_le (f : α → ℝ≥0∞) {c : ℝ≥0∞} :
    essInf (fun x => f x + c) μ ≤ essInf f μ + c := by
  set a := essInf (fun x => f x + c) μ
  have hae : ∀ᵐ x ∂μ, a ≤ f x + c := ae_essInf_le
  have h1 : a - c ≤ essInf f μ :=
    le_essInf_of_ae_le _ (hae.mono fun x hx => tsub_le_iff_right.mpr hx)
  exact tsub_le_iff_right.mp h1

/-- Limit `δ → 0`: if `M + δ ≤ H (m + δ)` for all `δ > 0` with `H` finite and `≥ 1`, then
`M ≤ H m`. -/
theorem le_of_add_pos_le_mul {M m : ℝ≥0∞} {H : ℝ} (hH : 0 < H)
    (h : ∀ δ : ℝ, 0 < δ → M + ENNReal.ofReal δ ≤ ENNReal.ofReal H * (m + ENNReal.ofReal δ)) :
    M ≤ ENNReal.ofReal H * m := by
  by_cases hm : m = ∞
  · rw [hm, ENNReal.mul_top (by simpa using hH)]; exact le_top
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hδ : 0 < (ε : ℝ) / H := div_pos (by exact_mod_cast hε) hH
  have := h _ hδ
  calc M ≤ M + ENNReal.ofReal (ε / H) := le_self_add
    _ ≤ _ := this
    _ = ENNReal.ofReal H * m + ε := by
      rw [mul_add, ← ENNReal.ofReal_mul hH.le, mul_div_cancel₀ _ hH.ne']
      simp

end PDE.Ch4GreenHarnack
