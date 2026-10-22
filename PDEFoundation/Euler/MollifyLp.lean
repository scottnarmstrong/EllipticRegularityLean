module

public import PDEFoundation.Euler.MollifyLocal
public import PDEFoundation.Euler.MollifyPairing
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# `L²(cube)` convergence of periodic mollification

For `f` periodic and square integrable on the cube, `mollify (aₙ) f → f` in `L²(cube)` for any sequence
`aₙ ∈ (0,1]` tending to `0`.  The proof windows `f` to the box `[-2,3]²`, where it is globally `L²`, and
applies the repo's whole-space `L^p` approximate-identity theorem.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PDE

theorem IsTorusPeriodic.memLp_window {f : Vec 2 → ℝ} (hf : IsTorusPeriodic f)
    (hL2 : MemLp f 2 (volume.restrict torusCube)) : MemLp ((mollBox 1).indicator f) 2 volume := by
  have : IsFiniteMeasure (volume.restrict torusCube) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (isCompact_Icc : IsCompact torusCube).measure_lt_top⟩
  have hsq : IntegrableOn (fun x => f x ^ 2) torusCube := MemLp.integrable_sq hL2
  have hsqloc : LocallyIntegrable (fun x => f x ^ 2) volume :=
    IsTorusPeriodic.locallyIntegrable (hf.comp (fun y => y ^ 2)) hsq
  have h1 : IntegrableOn f torusCube := hL2.integrable (by norm_num)
  have hloc : LocallyIntegrable f volume := IsTorusPeriodic.locallyIntegrable hf h1
  have hms : AEStronglyMeasurable ((mollBox 1).indicator f) volume :=
    (hloc.aestronglyMeasurable).indicator measurableSet_Icc
  rw [memLp_two_iff_integrable_sq hms]
  have : (fun x => ((mollBox 1).indicator f x) ^ 2) = (mollBox 1).indicator (fun x => f x ^ 2) := by
    funext x
    by_cases hx : x ∈ mollBox 1
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  rw [this]
  exact (hsqloc.integrableOn_isCompact isCompact_Icc).integrable_indicator measurableSet_Icc

theorem mollify_eq_window {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (f : Vec 2 → ℝ) {x : Vec 2}
    (hx : x ∈ torusCube) : mollify a f x = mollify a ((mollBox 1).indicator f) x := by
  rw [mollify_apply, mollify_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  by_cases ht : a < ‖t‖
  · rw [molK_eq_zero ha ht]; simp
  · have hti : ∀ i, |t i| ≤ a := fun i => (norm_le_pi_norm t i).trans (not_lt.mp ht)
    have hx0 : ∀ i, 0 ≤ x i := fun i => hx.1 i
    have hx1 : ∀ i, x i ≤ 1 := fun i => hx.2 i
    have hmem : x - t ∈ mollBox 1 := by
      constructor <;> intro i <;> simp only [Pi.sub_apply] <;>
        linarith [hx0 i, hx1 i, abs_le.mp (hti i)]
    rw [Set.indicator_of_mem hmem]

theorem tendsto_eLpNorm_mollify_cube {f : Vec 2 → ℝ} (hf : IsTorusPeriodic f)
    (hL2 : MemLp f 2 (volume.restrict torusCube)) {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) (ha1 : ∀ n, a n ≤ 1)
    (ha0 : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => mollify (a n) f x - f x) 2 (volume.restrict torusCube))
      atTop (𝓝 0) := by
  have hW := hf.memLp_window hL2
  have hconv := tendsto_eLpNorm_wholeSpaceMollify_sub (p := 2) (by norm_num) (by simp) hW ha ha1 ha0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv
    (fun _ => bot_le) (fun n => ?_)
  have hae : (fun x => mollify (a n) f x - f x) =ᵐ[volume.restrict torusCube]
      (wholeSpaceMollify (a n) ((mollBox 1).indicator f) - (mollBox 1).indicator f) := by
    filter_upwards [ae_restrict_mem measurableSet_torusCube] with x hx
    have hxW : x ∈ mollBox 1 := by
      have hx0 : ∀ i, 0 ≤ x i := fun i => hx.1 i
      have hx1 : ∀ i, x i ≤ 1 := fun i => hx.2 i
      constructor <;> intro i <;> linarith [hx0 i, hx1 i]
    simp only [Pi.sub_apply]
    rw [mollify_eq_window (ha n) (ha1 n) f hx, Set.indicator_of_mem hxW]
    rfl
  rw [eLpNorm_congr_ae hae]
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

end PDE
