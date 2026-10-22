module

public import PDEFoundation.Measure.VecAppendVolume
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

@[expose] public section

namespace PDE
open MeasureTheory Set
open scoped ENNReal

/-- Coordinate splitting carries volume on a product cylinder to the product
of the two restricted native volumes. -/
theorem measurePreserving_vecAppendEquiv_restrict
    (m n : ℕ) {U : Set (Vec m)} {V : Set (Vec n)}
    (hU : MeasurableSet U) (hV : MeasurableSet V) :
    MeasurePreserving (vecAppendEquiv m n)
      (volume.restrict (vecAppendEquiv m n ⁻¹' (U ×ˢ V)))
      ((volume.restrict U).prod (volume.restrict V)) := by
  have h := (measurePreserving_vecAppendEquiv m n).restrict_preimage (hU.prod hV)
  rw [Measure.volume_eq_prod (Vec m) (Vec n), ← Measure.prod_restrict] at h
  exact h

/-- A finite-volume unused factor preserves scalar `Lᵖ` membership under
literal coordinate lifting. -/
theorem memLp_comp_fst_vecAppendEquiv
    (m n : ℕ) {U : Set (Vec m)} {V : Set (Vec n)}
    (hU : MeasurableSet U) (hV : MeasurableSet V) (hVfinite : volume V < ⊤)
    {p : ℝ≥0∞} {f : Vec m → ℝ} (hf : MemLp f p (volume.restrict U)) :
    MemLp (fun x : Vec (m + n) => f (vecAppendEquiv m n x).1) p
      (volume.restrict (vecAppendEquiv m n ⁻¹' (U ×ˢ V))) := by
  let : IsFiniteMeasure (volume.restrict V) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hVfinite⟩
  exact (hf.comp_fst (volume.restrict V)).comp_measurePreserving
    (measurePreserving_vecAppendEquiv_restrict m n hU hV)

end PDE
