module

public import PDEFoundation.Measure.VecAppendLp
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-! # Exact `Lᵖ` norm of scalar coordinate lifts -/

@[expose] public section

namespace PDE

open MeasureTheory Set
open scoped ENNReal

/-- Exact raw-cylinder `Lᵖ` seminorm of a scalar field lifted through the first
coordinate block. The formula includes Mathlib's conventions at `p = 0` and
`p = ∞`. -/
theorem eLpNorm_comp_fst_vecAppendEquiv
    (m n : ℕ) {U : Set (Vec m)} {V : Set (Vec n)}
    (hU : MeasurableSet U) (hV : MeasurableSet V) (hVpos : 0 < volume V)
    {p : ℝ≥0∞} {f : Vec m → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict U)) :
    eLpNorm (fun z : Vec (m + n) => f (vecAppendEquiv m n z).1) p
        (volume.restrict (vecAppendEquiv m n ⁻¹' (U ×ˢ V))) =
      (volume V) ^ (1 / p).toReal *
        eLpNorm f p (volume.restrict U) := by
  let μE := volume.restrict (vecAppendEquiv m n ⁻¹' (U ×ˢ V))
  let μU := volume.restrict U
  let μV := volume.restrict V
  let e : Vec (m + n) ≃ᵐ (Vec m × Vec n) :=
    (vecAppendEquiv m n).toHomeomorph.toMeasurableEquiv
  have he : MeasurePreserving e μE (μU.prod μV) := by
    simpa only [μE, μU, μV, e] using!
      measurePreserving_vecAppendEquiv_restrict m n hU hV
  have hVuniv : μV Set.univ = volume V := by
    simp only [μV, Measure.restrict_apply_univ]
  have hfst : MeasurePreserving (fun q : Vec m × Vec n => q.1)
      (μU.prod μV) ((volume V) • μU) := by
    refine ⟨measurable_fst, ?_⟩
    rw [Measure.map_fst_prod, hVuniv]
  have hfScaled : AEStronglyMeasurable f ((volume V) • μU) :=
    hf.smul_measure (volume V)
  have hprodAES : AEStronglyMeasurable (fun q : Vec m × Vec n => f q.1)
      (μU.prod μV) :=
    (hfst.map_eq ▸ hfScaled).comp_aemeasurable hfst.aemeasurable
  have hchange := eLpNorm_comp_measurePreserving (p := p) hprodAES he
  have hfstNorm := eLpNorm_comp_measurePreserving (p := p) hfScaled hfst
  have hscale := eLpNorm_smul_measure_of_ne_zero hVpos.ne' f p μU
  calc
    eLpNorm (fun z : Vec (m + n) => f (vecAppendEquiv m n z).1) p
        (volume.restrict (vecAppendEquiv m n ⁻¹' (U ×ˢ V))) =
        eLpNorm (fun q : Vec m × Vec n => f q.1) p (μU.prod μV) := by
      change eLpNorm ((fun q : Vec m × Vec n => f q.1) ∘ e) p μE = _
      exact hchange
    _ = eLpNorm f p ((volume V) • μU) := by
      change eLpNorm (f ∘ fun q : Vec m × Vec n => q.1) p (μU.prod μV) = _
      exact hfstNorm
    _ = (volume V) ^ (1 / p).toReal * eLpNorm f p μU := by
      simpa only [smul_eq_mul] using hscale


end PDE
