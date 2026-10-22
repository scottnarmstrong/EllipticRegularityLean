module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# One-dimensional Brunn--Minkowski for measurable sets

For nonempty measurable `A, B ⊆ ℝ` we show `|A| + |B| ≤ |A + B|` (outer measure of the sum),
first for compact sets by translating `K` and `L` so that they touch at one point, then for
measurable sets by inner regularity, and finally the weighted form for `l • A + (1 - l) • B`.
-/

@[expose] public section

namespace PDE.PrekopaLeindlerProof

open MeasureTheory Set
open scoped ENNReal Pointwise

/-- One-dimensional Brunn--Minkowski for compact sets. -/
theorem volume_add_compact {K L : Set ℝ} (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty) :
    volume K + volume L ≤ volume (K + L) := by
  have ha : sSup K ∈ K := hK.sSup_mem hKne
  have hb : sInf L ∈ L := hL.sInf_mem hLne
  set a := sSup K
  set b := sInf L
  have hX : IsCompact (b +ᵥ K) := hK.vadd b
  have hY : IsCompact (a +ᵥ L) := hL.vadd a
  have hXs : b +ᵥ K ⊆ K + L := by
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨k, hk, b, hb, by simp [add_comm]⟩
  have hYs : a +ᵥ L ⊆ K + L := by
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨a, ha, k, hk, rfl⟩
  have hint : volume ((b +ᵥ K) ∩ (a +ᵥ L)) = 0 := by
    refine measure_mono_null (t := {a + b}) ?_ (measure_singleton _)
    rintro z ⟨⟨k, hk, rfl⟩, ⟨l, hl, hz⟩⟩
    have h1 : k ≤ a := le_csSup hK.bddAbove hk
    have h2 : b ≤ l := csInf_le hL.bddBelow hl
    have : a + l = b + k := hz
    have : k = a := by simp only [vadd_eq_add] at *; linarith
    simp only [mem_singleton_iff, vadd_eq_add]
    rw [this, add_comm]
  have hu := measure_union_add_inter (μ := volume) (b +ᵥ K) hY.isClosed.measurableSet
  rw [hint, add_zero, measure_vadd, measure_vadd] at hu
  rw [← hu]
  exact measure_mono (union_subset hXs hYs)

/-- One-dimensional Brunn--Minkowski for nonempty measurable sets (outer measure of the sum). -/
theorem volume_add_measurable {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAne : A.Nonempty) (hBne : B.Nonempty) :
    volume A + volume B ≤ volume (A + B) := by
  obtain ⟨a0, ha0⟩ := hAne
  obtain ⟨b0, hb0⟩ := hBne
  have key : ∀ K, IsCompact K → K ⊆ A → ∀ L, IsCompact L → L ⊆ B →
      volume K + volume L ≤ volume (A + B) := by
    intro K hK hKA L hL hLB
    have h := volume_add_compact (hK.union (isCompact_singleton (x := a0)))
      (hL.union (isCompact_singleton (x := b0))) (by simp) (by simp)
    calc volume K + volume L ≤ volume (K ∪ {a0}) + volume (L ∪ {b0}) :=
          add_le_add (measure_mono subset_union_left) (measure_mono subset_union_left)
      _ ≤ volume ((K ∪ {a0}) + (L ∪ {b0})) := h
      _ ≤ _ := measure_mono (add_subset_add (union_subset hKA (by simpa))
          (union_subset hLB (by simpa)))
  have hA' : volume A = ⨆ K, ⨆ (_ : K ⊆ A ∧ IsCompact K), volume K := by
    rw [hA.measure_eq_iSup_isCompact]; simp only [iSup_and]
  have hB' : volume B = ⨆ K, ⨆ (_ : K ⊆ B ∧ IsCompact K), volume K := by
    rw [hB.measure_eq_iSup_isCompact]; simp only [iSup_and]
  rw [hA', hB']
  refine ENNReal.biSup_add_biSup_le' (p := fun K : Set ℝ => K ⊆ A ∧ IsCompact K)
    (q := fun K : Set ℝ => K ⊆ B ∧ IsCompact K) ⟨∅, empty_subset _, isCompact_empty⟩
    ⟨∅, empty_subset _, isCompact_empty⟩ ?_
  rintro K ⟨hKA, hK⟩ L ⟨hLB, hL⟩
  exact key K hK hKA L hL hLB

/-- Weighted one-dimensional Brunn--Minkowski: `l |A| + (1 - l) |B| ≤ |l A + (1 - l) B|`. -/
theorem volume_smul_add_smul {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) {A B : Set ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAne : A.Nonempty) (hBne : B.Nonempty) :
    ENNReal.ofReal l * volume A + ENNReal.ofReal (1 - l) * volume B ≤
      volume (l • A + (1 - l) • B) := by
  have h := volume_add_measurable (hA.const_smul₀ l) (hB.const_smul₀ (1 - l))
    (hAne.smul_set) (hBne.smul_set)
  have e1 : volume (l • A) = ENNReal.ofReal l * volume A := by
    rw [Measure.addHaar_smul]; simp [abs_of_pos hl0]
  have e2 : volume ((1 - l) • B) = ENNReal.ofReal (1 - l) * volume B := by
    rw [Measure.addHaar_smul]; simp [abs_of_pos (sub_pos.2 hl1)]
  rwa [e1, e2] at h

end PDE.PrekopaLeindlerProof
