module

public import PDEFoundation.Measure.VecAppendVolume
public import Mathlib.MeasureTheory.Measure.Prod

/-! # Nullity of a zero coordinate block -/

@[expose] public section

namespace PDE

open MeasureTheory Set

/-- In positive first-block dimension, the vectors whose entire first block
vanishes form a volume-null set, independently of the second-block dimension. -/
theorem volume_vecAppendEquiv_fst_eq_zero
    {m n : ℕ} (hm : 0 < m) :
    volume {z : Vec (m + n) | (vecAppendEquiv m n z).1 = 0} = 0 := by
  let : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  let e : Vec (m + n) ≃ᵐ (Vec m × Vec n) :=
    (vecAppendEquiv m n).toHomeomorph.toMeasurableEquiv
  have he : MeasurePreserving e
      (volume : Measure (Vec (m + n))) (volume : Measure (Vec m × Vec n)) := by
    simpa only [e] using! measurePreserving_vecAppendEquiv m n
  have hpre : e ⁻¹' (({0} : Set (Vec m)) ×ˢ (Set.univ : Set (Vec n))) =
      {z : Vec (m + n) | (vecAppendEquiv m n z).1 = 0} := by
    ext z
    simp only [mem_preimage, mem_prod, mem_singleton_iff, mem_univ, and_true,
      mem_ofPred_eq]
    rfl
  rw [← hpre, he.measure_preimage]
  · rw [Measure.volume_eq_prod (Vec m) (Vec n),
      Measure.prod_prod ({0} : Set (Vec m)) (Set.univ : Set (Vec n)),
      measure_singleton, zero_mul]
  · exact (measurableSet_singleton 0).prod MeasurableSet.univ |>.nullMeasurableSet

/-- Almost every native appended vector has nonzero first block when that
block has positive dimension. -/
theorem ae_vecAppendEquiv_fst_ne_zero
    {m n : ℕ} (hm : 0 < m) :
    ∀ᵐ z : Vec (m + n) ∂volume, (vecAppendEquiv m n z).1 ≠ 0 := by
  rw [ae_iff]
  simpa only [not_ne_iff] using volume_vecAppendEquiv_fst_eq_zero (n := n) hm

/-- The same nonvanishing statement holds after restricting volume to any
set. -/
theorem ae_vecAppendEquiv_fst_ne_zero_restrict
    {m n : ℕ} (hm : 0 < m) (S : Set (Vec (m + n))) :
    ∀ᵐ z ∂volume.restrict S, (vecAppendEquiv m n z).1 ≠ 0 :=
  (ae_vecAppendEquiv_fst_ne_zero (n := n) hm).filter_mono
    (ae_mono Measure.restrict_le_self)

end PDE
