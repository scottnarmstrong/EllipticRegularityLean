module

public import PDEFoundation.Measure.RestrictedVolume
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A measurable set carrying the nonzero values of `(-log (u + δ))_+`
-/

@[expose] public section

namespace PDE.DGNMLog

open MeasureTheory

/-- If `u ≥ 1` on a set of density at least `1 - θ` in `B`, and `w = (-log (u + δ))_+` a.e. on `B`,
then `w` vanishes on `B \ t` for a measurable `t` with `|t ∩ B| ≤ θ |B|`. -/
theorem exists_measurable_zero_set {d : ℕ} {B : Set (Vec d)} (hBmeas : MeasurableSet B)
    (hBfin : volume B < ⊤) {u w : Vec d → ℝ} (hu : AEStronglyMeasurable u (volumeOn B))
    {θ δ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hδ : 0 < δ)
    (hdens : ENNReal.ofReal (1 - θ) * volume B ≤ volume {x ∈ B | 1 ≤ u x})
    (hw : ∀ᵐ x ∂(volumeOn B), w x = max (-Real.log (u x + δ)) 0) :
    ∃ t : Set (Vec d), MeasurableSet t ∧ (∀ x ∈ B, x ∉ t → w x = 0) ∧
      volume (t ∩ B) ≤ ENNReal.ofReal θ * volume B := by
  set ũ := hu.mk u with hũ
  have hmeas : Measurable ũ := hu.stronglyMeasurable_mk.measurable
  have hae : ∀ᵐ x ∂(volumeOn B), u x = ũ x := hu.ae_eq_mk
  have hP : ∀ᵐ x ∂volume, x ∈ B → (w x = max (-Real.log (u x + δ)) 0 ∧ u x = ũ x) := by
    have := (ae_restrict_iff' hBmeas).mp (hw.and hae)
    exact this
  obtain ⟨N, hNsub, hNmeas, hNzero⟩ := exists_measurable_superset_of_null
    (s := {x | ¬ (x ∈ B → (w x = max (-Real.log (u x + δ)) 0 ∧ u x = ũ x))})
    (by simpa [ae_iff] using hP)
  set t : Set (Vec d) := N ∪ {x | ũ x + δ < 1} with ht
  refine ⟨t, hNmeas.union (measurableSet_lt (hmeas.add_const δ) measurable_const), ?_, ?_⟩
  · intro x hxB hxt
    have hxN : x ∉ N := fun h => hxt (Or.inl h)
    have hxP : w x = max (-Real.log (u x + δ)) 0 ∧ u x = ũ x := by
      by_contra hcon
      exact hxN (hNsub (fun h => hcon (h hxB)))
    have h1 : 1 ≤ ũ x + δ := by
      by_contra h; exact hxt (Or.inr (not_le.mp h))
    have h2 : 0 ≤ Real.log (u x + δ) := Real.log_nonneg (by rw [hxP.2]; exact h1)
    rw [hxP.1]
    exact max_eq_right (by linarith)
  · set S' : Set (Vec d) := {x | 1 ≤ ũ x} ∩ B with hS'
    set T' : Set (Vec d) := {x | ũ x < 1} ∩ B with hT'
    have hS'meas : MeasurableSet S' := (measurableSet_le measurable_const hmeas).inter hBmeas
    have hT'meas : MeasurableSet T' := (measurableSet_lt hmeas measurable_const).inter hBmeas
    have hsum : volume S' + volume T' = volume B := by
      rw [← measure_union _ hT'meas]
      · congr 1
        ext x; constructor
        · rintro (h | h) <;> exact h.2
        · intro hx
          by_cases h : 1 ≤ ũ x
          · exact Or.inl ⟨h, hx⟩
          · exact Or.inr ⟨not_le.mp h, hx⟩
      · rw [Set.disjoint_left]
        rintro x ⟨h1, _⟩ ⟨h2, _⟩
        exact absurd (show ũ x < 1 from h2) (not_lt.mpr h1)
    have hSeq : volume S' = volume {x ∈ B | 1 ≤ u x} := by
      refine measure_congr ?_
      filter_upwards [hP] with x hx
      by_cases hxB : x ∈ B
      · have := (hx hxB).2
        simp only [hS', Set.mem_inter_iff, Set.mem_ofPred_eq, eq_iff_iff]
        rw [this]; tauto
      · simp [hS', hxB]
    have hSfin : ENNReal.ofReal (1 - θ) * volume B ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBfin.ne
    have hT'le : volume T' ≤ ENNReal.ofReal θ * volume B := by
      have hB : volume B = ENNReal.ofReal (1 - θ) * volume B + ENNReal.ofReal θ * volume B := by
        rw [← add_mul, ← ENNReal.ofReal_add (by linarith) hθ0]; simp
      refine ENNReal.le_of_add_le_add_left hSfin ?_
      rw [← hB]
      calc ENNReal.ofReal (1 - θ) * volume B + volume T' ≤ volume S' + volume T' := by
            gcongr; rw [hSeq]; exact hdens
        _ = volume B := hsum
    calc volume (t ∩ B) ≤ volume (N ∪ T') := by
          refine measure_mono ?_
          rintro x ⟨hxt, hxB⟩
          rcases hxt with hx | hx
          · exact Or.inl hx
          · exact Or.inr ⟨by simp only [Set.mem_ofPred_eq] at hx ⊢; linarith, hxB⟩
      _ ≤ volume N + volume T' := measure_union_le _ _
      _ ≤ ENNReal.ofReal θ * volume B := by rw [hNzero, zero_add]; exact hT'le

end PDE.DGNMLog
