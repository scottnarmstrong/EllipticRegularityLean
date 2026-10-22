module

public import PDEFoundation.Ambient.Basis
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Continuity of translation in `L^p(ℝ^d)`

For `1 ≤ q < ∞` and `f ∈ L^q(ℝ^d)`, the translates `f (· + h)` converge to `f` in `L^q` as
`h → 0`.  The proof approximates `f` by a continuous compactly supported function, for which
uniform continuity gives uniform convergence on a fixed compact set.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Filter Topology Set
open scoped ENNReal

variable {d : ℕ}

/-- Translation preserves the `L^q` seminorm on `ℝ^d`. -/
theorem eLpNorm_comp_add_right {q : ℝ≥0∞} {g : Vec d → ℝ}
    (hg : AEStronglyMeasurable g volume) (t : Vec d) :
    eLpNorm (fun x => g (x + t)) q volume = eLpNorm g q volume :=
  eLpNorm_comp_measurePreserving (f := fun x : Vec d => x + t) hg
    (measurePreserving_add_right volume t)

/-- Continuity of translation in `L^q(ℝ^d)`, `1 ≤ q < ∞`. -/
theorem tendsto_eLpNorm_comp_add_sub {q : ℝ≥0∞} (hq : 1 ≤ q) (hqTop : q ≠ ∞)
    {f : Vec d → ℝ} (hf : MemLp f q volume) :
    Tendsto (fun h : Vec d => eLpNorm (fun x => f (x + h) - f x) q volume) (𝓝 0) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ∞ with rfl | hεTop
  · exact Eventually.of_forall fun _ => le_top
  have hδ : ε / 3 ≠ 0 := (ENNReal.div_pos_iff.2 ⟨hε.ne', ENNReal.ofNat_ne_top⟩).ne'
  obtain ⟨h, hhc, hfh, hhcont, hhmem⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le hqTop hδ
  set S := Metric.cthickening 1 (tsupport h) with hS
  have hSc : IsCompact S := hhc.isCompact.cthickening
  have hSvol : volume S ≠ ∞ := hSc.measure_lt_top.ne
  have hvolpow : volume S ^ (1 / q.toReal) ≠ ∞ :=
    (ENNReal.rpow_lt_top_of_nonneg (by positivity) hSvol).ne
  have hpt : 0 < q.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le hq).ne' hqTop
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℝ, 0 < c ∧
      ENNReal.ofReal c * volume S ^ (1 / q.toReal) ≤ ε / 3 := by
    set V := volume S ^ (1 / q.toReal)
    have hE : ε / 3 ≠ ∞ := ENNReal.div_ne_top hεTop (by norm_num)
    have hεpos : (0 : ℝ) < (ε / 3).toReal := ENNReal.toReal_pos hδ hE
    have hV : 0 ≤ V.toReal := ENNReal.toReal_nonneg
    refine ⟨(ε / 3).toReal / (V.toReal + 1), by positivity, ?_⟩
    calc ENNReal.ofReal ((ε / 3).toReal / (V.toReal + 1)) * V
        = ENNReal.ofReal ((ε / 3).toReal / (V.toReal + 1) * V.toReal) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hvolpow]
      _ ≤ ENNReal.ofReal (ε / 3).toReal := by
          apply ENNReal.ofReal_le_ofReal
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith
      _ = ε / 3 := ENNReal.ofReal_toReal hE
  obtain ⟨η, hη, hηh⟩ := Metric.uniformContinuous_iff.mp
    (hhc.uniformContinuous_of_continuous hhcont) c hc0
  have hfh' : AEStronglyMeasurable (f - h) volume := (hf.sub hhmem).aestronglyMeasurable
  have hfm : AEStronglyMeasurable f volume := hf.aestronglyMeasurable
  have hhm : AEStronglyMeasurable h volume := hhcont.aestronglyMeasurable
  filter_upwards [Metric.ball_mem_nhds (0 : Vec d) (lt_min hη one_pos)] with t ht
  have htn : ‖t‖ < min η 1 := by simpa using ht
  have htη : ‖t‖ < η := htn.trans_le (min_le_left _ _)
  have ht1 : ‖t‖ ≤ 1 := htn.le.trans (min_le_right _ _)
  have hshift : AEStronglyMeasurable (fun x => h (x + t)) volume :=
    (hhcont.comp (continuous_id.add continuous_const)).aestronglyMeasurable
  have h1 : eLpNorm (fun x => h (x + t) - h x) q volume ≤ ε / 3 := by
    refine le_trans ?_ hc
    refine eLpNorm_sub_le_of_dist_bdd (f := fun x => h (x + t)) (g := h) volume hqTop
      hSc.measurableSet.nullMeasurableSet hc0.le (hshift.sub hhm) (fun x => ?_) ?_ ?_
    · have : dist (x + t) x < η := by
        rw [dist_eq_norm, add_sub_cancel_left]; exact htη
      exact (hηh this).le
    · intro x hx
      refine Metric.mem_cthickening_of_dist_le x (x + t) 1 _
        (subset_tsupport h hx) ?_
      rw [dist_eq_norm, sub_add_cancel_left, norm_neg]; exact ht1
    · exact subset_tsupport h |>.trans (Metric.self_subset_cthickening _)
  have h2 : eLpNorm (fun x => (f - h) (x + t)) q volume ≤ ε / 3 := by
    rw [eLpNorm_comp_add_right hfh' t]
    simpa using hfh
  have h3 : eLpNorm (f - h) q volume ≤ ε / 3 := by simpa using hfh
  have hdecomp : (fun x => f (x + t) - f x) =
      (fun x => (f - h) (x + t)) + (fun x => h (x + t) - h x) - (f - h) := by
    funext x; simp only [Pi.add_apply, Pi.sub_apply]; ring
  rw [hdecomp]
  calc eLpNorm _ q volume ≤ eLpNorm ((fun x => (f - h) (x + t)) + (fun x => h (x + t) - h x)) q
        volume + eLpNorm (f - h) q volume := by
        exact eLpNorm_sub_le hq
    _ ≤ (eLpNorm (fun x => (f - h) (x + t)) q volume +
          eLpNorm (fun x => h (x + t) - h x) q volume) + eLpNorm (f - h) q volume := by
        gcongr; exact eLpNorm_add_le hq
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by gcongr
    _ = ε := ENNReal.add_thirds ε

end PDE.TraceLane
