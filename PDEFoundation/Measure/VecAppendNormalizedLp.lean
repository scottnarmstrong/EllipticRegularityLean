module

public import PDEFoundation.Measure.VecAppendLp
public import PDEFoundation.Measure.NormalizedLp

@[expose] public section

namespace PDE
open MeasureTheory Set
open scoped ENNReal

/-- A scalar field independent of the unused variables has exactly its
original normalized seminorm on a positive finite-volume product cylinder. -/
theorem eLpNorm_comp_fst_vecAppendEquiv_normalizedVolumeOn
    (m n : ℕ) {U : Set (Vec m)} {V : Set (Vec n)}
    (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hUpos : 0 < volume U) (hUfinite : volume U < ⊤)
    (hVpos : 0 < volume V) (hVfinite : volume V < ⊤)
    {p : ℝ≥0∞} {f : Vec m → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict U)) :
    eLpNorm (fun z : Vec (m + n) => f (vecAppendEquiv m n z).1) p
        (normalizedVolumeOn (vecAppendEquiv m n ⁻¹' (U ×ˢ V))) =
      eLpNorm f p (normalizedVolumeOn U) := by
  let E := vecAppendEquiv m n ⁻¹' (U ×ˢ V)
  let μE := volume.restrict E
  let μU := volume.restrict U
  let μV := volume.restrict V
  let e : Vec (m + n) ≃ᵐ (Vec m × Vec n) :=
    (vecAppendEquiv m n).toHomeomorph.toMeasurableEquiv
  have he : MeasurePreserving e μE (μU.prod μV) :=
    measurePreserving_vecAppendEquiv_restrict m n hU hV
  have hEvol : volume E = volume U * volume V := by
    have h := he.measure_preimage (MeasurableSet.univ.nullMeasurableSet : NullMeasurableSet (Set.univ : Set (Vec m × Vec n)) (μU.prod μV))
    simpa only [μE, μU, μV, preimage_univ, Measure.restrict_apply_univ,
      Measure.prod_apply, MeasurableSet.univ, Measure.restrict_apply_univ,
      lintegral_const, Measure.restrict_apply_univ, mul_comm] using h
  have hfst : MeasurePreserving (fun q : Vec m × Vec n => q.1)
      (μU.prod μV) ((volume V) • μU) := by
    refine ⟨measurable_fst, ?_⟩
    rw [Measure.map_fst_prod]
    simp only [μV, Measure.restrict_apply_univ]
  have hRaw := hfst.comp he
  have hMap : Measure.map (fun z : Vec (m + n) => (vecAppendEquiv m n z).1) μE =
      (volume V) • μU := hRaw.map_eq
  have hcoef : (volume E)⁻¹ * volume V = (volume U)⁻¹ := by
    rw [hEvol, ENNReal.mul_inv (Or.inl hUpos.ne') (Or.inl hUfinite.ne),
      mul_assoc, ENNReal.inv_mul_cancel hVpos.ne' hVfinite.ne, mul_one]
  have hNorm : MeasurePreserving (fun z : Vec (m + n) => (vecAppendEquiv m n z).1)
      (normalizedVolumeOn E) (normalizedVolumeOn U) := by
    have hmeas : Measurable (fun z : Vec (m + n) => (vecAppendEquiv m n z).1) :=
      measurable_fst.comp (vecAppendEquiv m n).continuous.measurable
    refine ⟨hmeas, ?_⟩
    rw [normalizedVolumeOn, normalizedVolumeOn, Measure.map_smul _ hmeas.aemeasurable]
    change (volume E)⁻¹ • Measure.map (fun z => (vecAppendEquiv m n z).1) μE = _
    rw [hMap, smul_smul, hcoef]
  have hfNorm : AEStronglyMeasurable f (normalizedVolumeOn U) := hf.smul_measure _
  exact eLpNorm_comp_measurePreserving hfNorm hNorm

end PDE
