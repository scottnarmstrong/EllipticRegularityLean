module

public import PDEFoundation.Sobolev.Trace.Model.ExtKernel

/-!
# The normal cutoff of the model extension operator

Elementary properties of `extCutoff`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology

theorem extCutoff_contDiff : ContDiff ℝ 1 extCutoff :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul contDiff_id))

theorem extCutoff_nonneg (t : ℝ) : 0 ≤ extCutoff t := Real.smoothTransition.nonneg _

theorem extCutoff_le_one (t : ℝ) : extCutoff t ≤ 1 := Real.smoothTransition.le_one _

theorem extCutoff_eq_one {t : ℝ} (ht : t ≤ 1 / 2) : extCutoff t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem extCutoff_eq_zero {t : ℝ} (ht : 1 ≤ t) : extCutoff t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem deriv_extCutoff_eq_zero {t : ℝ} (ht : 1 < t) : deriv extCutoff t = 0 := by
  have : extCutoff =ᶠ[𝓝 t] fun _ => 0 :=
    Filter.Eventually.mono (Ioi_mem_nhds ht) fun s hs => extCutoff_eq_zero (le_of_lt hs)
  rw [this.deriv_eq]
  simp

theorem deriv_extCutoff_eq_zero_of_lt {t : ℝ} (ht : t < 1 / 2) : deriv extCutoff t = 0 := by
  have : extCutoff =ᶠ[𝓝 t] fun _ => 1 :=
    Filter.Eventually.mono (Iio_mem_nhds ht) fun s hs => extCutoff_eq_one (le_of_lt hs)
  rw [this.deriv_eq]
  simp

theorem exists_deriv_extCutoff_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |deriv extCutoff t| ≤ C := by
  have hc : Continuous (deriv extCutoff) := extCutoff_contDiff.continuous_deriv le_rfl
  have hs : HasCompactSupport (deriv extCutoff) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (1 / 2 : ℝ)) (b := 1)) ?_
    intro t ht
    simp only [mem_Icc, not_and_or, not_le] at ht
    rcases ht with h | h
    · exact deriv_extCutoff_eq_zero_of_lt h
    · exact deriv_extCutoff_eq_zero h
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨C, (norm_nonneg _).trans (hC 0), fun t => by simpa using hC t⟩

end PDE.TraceLane
