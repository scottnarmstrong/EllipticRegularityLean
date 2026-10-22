module

public import PDEFoundation.Measure.VecAppendLp

@[expose] public section

namespace PDE
open MeasureTheory Set
open scoped ENNReal

/-- Positive finite volume of the unused factor allows membership of a lifted
scalar field to be reflected back to its original factor. -/
theorem memLp_of_comp_fst_vecAppendEquiv
    (m n : ℕ) {U : Set (Vec m)} {V : Set (Vec n)}
    (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hVpos : 0 < volume V) (hVfinite : volume V < ⊤)
    {p : ℝ≥0∞} {f : Vec m → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict U))
    (hLift : MemLp (fun z : Vec (m + n) => f (vecAppendEquiv m n z).1) p
      (volume.restrict (vecAppendEquiv m n ⁻¹' (U ×ˢ V)))) :
    MemLp f p (volume.restrict U) := by
  let e : Vec (m + n) ≃ᵐ (Vec m × Vec n) :=
    (vecAppendEquiv m n).toHomeomorph.toMeasurableEquiv
  have he : MeasurePreserving e
      (volume.restrict (vecAppendEquiv m n ⁻¹' (U ×ˢ V)))
      ((volume.restrict U).prod (volume.restrict V)) :=
    measurePreserving_vecAppendEquiv_restrict m n hU hV
  have hProd : MemLp (fun z : Vec m × Vec n => f z.1) p
      ((volume.restrict U).prod (volume.restrict V)) := by
    have h := hLift.comp_measurePreserving (MeasurePreserving.symm e he)
    simpa [e, Function.comp_def] using h
  have hfMap : AEStronglyMeasurable f
      (Measure.map Prod.fst ((volume.restrict U).prod (volume.restrict V))) := by
    rw [Measure.map_fst_prod]
    exact hf.smul_measure _
  have hScaled := (memLp_map_measure_iff hfMap measurable_fst.aemeasurable).mpr hProd
  rw [Measure.map_fst_prod, Measure.restrict_apply_univ] at hScaled
  have hReflect := hScaled.smul_measure (ENNReal.inv_ne_top.mpr hVpos.ne')
  rw [smul_smul, ENNReal.inv_mul_cancel hVpos.ne' hVfinite.ne, one_smul] at hReflect
  exact hReflect

end PDE
