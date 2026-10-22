module

public import PDEFoundation.Measure.GoodSquareRadiusFubini
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# `L²` slices of planar axis boxes

This module records the genuine one-dimensional `L²` regularity supplied by
Fubini for functions on a two-dimensional open axis box.  The conclusions are
stated on the native `Vec 2` carrier and use the coordinate constructor
`squarePoint`.
-/

@[expose] public section

namespace PDE

open MeasureTheory Set

noncomputable section

/-- An `L²` function on a planar axis box has `L²` vertical-coordinate slices
for almost every horizontal coordinate in the box. -/
theorem memLp_axisBox_slice_second_ae
    {f : Vec 2 → ℝ} {a b c d : ℝ}
    (hf : MemL2On (axisBox ![a, c] ![b, d]) f) :
    ∀ᵐ s ∂(volume.restrict (Ioo a b)),
      MemLp (fun t => f (squarePoint s t)) 2 (volume.restrict (Ioo c d)) := by
  let Q : Set (Vec 2) := axisBox ![a, c] ![b, d]
  have hQ : MeasurableSet Q := (isOpen_axisBox _ _).measurableSet
  have hglobal : MemLp (Q.indicator f) 2 (volume : Measure (Vec 2)) :=
    (memLp_indicator_iff_restrict hQ).2 hf
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  have hprod : MemLp (fun p : ℝ × ℝ => Q.indicator f (e.symm p)) 2
      (volume : Measure (ℝ × ℝ)) := by
    simpa only [Function.comp_apply] using! hglobal.comp_measurePreserving
      (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).symm
  have hmeas := hprod.aestronglyMeasurable.prodMk_left
  have hint := hprod.integrable_sq
  have hslices := hint.prod_right_ae
  filter_upwards [ae_restrict_of_ae hmeas, ae_restrict_of_ae hslices,
    ae_restrict_mem measurableSet_Ioo] with s hsmeas hsint hs
  have hg : MemLp (fun t => Q.indicator f (e.symm (s, t))) 2
      (volume.restrict (Ioo c d)) :=
    (memLp_two_iff_integrable_sq hsmeas.restrict).2 hsint.restrict
  apply (memLp_congr_ae ?_).1 hg
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have he : e.symm (s, t) = squarePoint s t := by
    funext i
    fin_cases i <;> simp [e, MeasurableEquiv.piFinTwo_symm_apply, squarePoint]
  have hpoint : squarePoint s t ∈ Q := by
    change squarePoint s t ∈ axisBox ![a, c] ![b, d]
    exact (squarePoint_mem_axisBox_iff a b c d s t).mpr ⟨hs, ht⟩
  rw [he, Set.indicator_of_mem hpoint]

/-- An `L²` function on a planar axis box has `L²` horizontal-coordinate
slices for almost every vertical coordinate in the box. -/
theorem memLp_axisBox_slice_first_ae
    {f : Vec 2 → ℝ} {a b c d : ℝ}
    (hf : MemL2On (axisBox ![a, c] ![b, d]) f) :
    ∀ᵐ t ∂(volume.restrict (Ioo c d)),
      MemLp (fun s => f (squarePoint s t)) 2 (volume.restrict (Ioo a b)) := by
  let Q : Set (Vec 2) := axisBox ![a, c] ![b, d]
  have hQ : MeasurableSet Q := (isOpen_axisBox _ _).measurableSet
  have hglobal : MemLp (Q.indicator f) 2 (volume : Measure (Vec 2)) :=
    (memLp_indicator_iff_restrict hQ).2 hf
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  have hprod : MemLp (fun p : ℝ × ℝ => Q.indicator f (e.symm p)) 2
      (volume : Measure (ℝ × ℝ)) := by
    simpa only [Function.comp_apply] using! hglobal.comp_measurePreserving
      (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).symm
  have hmeas := hprod.aestronglyMeasurable.prodMk_right
  have hint := hprod.integrable_sq
  have hslices := hint.prod_left_ae
  filter_upwards [ae_restrict_of_ae hmeas, ae_restrict_of_ae hslices,
    ae_restrict_mem measurableSet_Ioo] with t htmeas htint ht
  have hg : MemLp (fun s => Q.indicator f (e.symm (s, t))) 2
      (volume.restrict (Ioo a b)) :=
    (memLp_two_iff_integrable_sq htmeas.restrict).2 htint.restrict
  apply (memLp_congr_ae ?_).1 hg
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have he : e.symm (s, t) = squarePoint s t := by
    funext i
    fin_cases i <;> simp [e, MeasurableEquiv.piFinTwo_symm_apply, squarePoint]
  have hpoint : squarePoint s t ∈ Q := by
    change squarePoint s t ∈ axisBox ![a, c] ![b, d]
    exact (squarePoint_mem_axisBox_iff a b c d s t).mpr ⟨hs, ht⟩
  rw [he, Set.indicator_of_mem hpoint]

end

end PDE
