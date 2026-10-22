module

public import PDEFoundation.Measure.LpSpace

/-! # Restriction of `Lᵖ` classes to a smaller measure -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  [NormedSpace ℝ E] {p : ENNReal} [Fact (1 ≤ p)]

/-- The literal linear restriction of an `Lᵖ(μ)` class to a dominated measure
`ν`, using the same representative and `MemLp.mono_measure`. -/
noncomputable def lpMonoMeasureLinearMap (μ ν : Measure α) (hνμ : ν ≤ μ) :
    Lp E p μ →ₗ[ℝ] Lp E p ν where
  toFun f := ((Lp.memLp f).mono_measure hνμ).toLp (f : α → E)
  map_add' f g := by
    apply Lp.ext
    have hsource : (⇑(f + g) : α → E) =ᵐ[ν] fun x => f x + g x :=
      (Lp.coeFn_add f g).filter_mono (ae_mono hνμ)
    filter_upwards
      [((Lp.memLp (f + g)).mono_measure hνμ).coeFn_toLp,
       Lp.coeFn_add
        (((Lp.memLp f).mono_measure hνμ).toLp (f : α → E))
        (((Lp.memLp g).mono_measure hνμ).toLp (g : α → E)),
       ((Lp.memLp f).mono_measure hνμ).coeFn_toLp,
       ((Lp.memLp g).mono_measure hνμ).coeFn_toLp,
       hsource] with x hleft hadd hf hg hsrc
    calc
      _ = ((f + g : Lp E p μ) : α → E) x := hleft
      _ = f x + g x := hsrc
      _ = (((Lp.memLp f).mono_measure hνμ).toLp (f : α → E)) x +
          (((Lp.memLp g).mono_measure hνμ).toLp (g : α → E)) x := by
        rw [hf, hg]
      _ = _ := hadd.symm
  map_smul' c f := by
    apply Lp.ext
    have hsource : (⇑(c • f) : α → E) =ᵐ[ν] fun x => c • f x :=
      (Lp.coeFn_smul c f).filter_mono (ae_mono hνμ)
    filter_upwards
      [((Lp.memLp (c • f)).mono_measure hνμ).coeFn_toLp,
       Lp.coeFn_smul c (((Lp.memLp f).mono_measure hνμ).toLp (f : α → E)),
       ((Lp.memLp f).mono_measure hνμ).coeFn_toLp,
       hsource] with x hleft hsmul hf hsrc
    calc
      _ = ((c • f : Lp E p μ) : α → E) x := hleft
      _ = c • f x := hsrc
      _ = c • (((Lp.memLp f).mono_measure hνμ).toLp (f : α → E)) x := by rw [hf]
      _ = _ := hsmul.symm

omit [Fact (1 ≤ p)] in
/-- The restriction map has operator norm at most one. -/
theorem norm_lpMonoMeasureLinearMap_le
    (μ ν : Measure α) (hνμ : ν ≤ μ) (f : Lp E p μ) :
    ‖lpMonoMeasureLinearMap μ ν hνμ f‖ ≤ ‖f‖ := by
  change ‖((Lp.memLp f).mono_measure hνμ).toLp (f : α → E)‖ ≤ ‖f‖
  rw [Lp.norm_toLp]
  rw [show ‖f‖ = (eLpNorm (f : α → E) p μ).toReal by
    simpa using Lp.norm_toLp (f : α → E) (Lp.memLp f)]
  exact ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top
    (eLpNorm_mono_measure (f : α → E) hνμ)

/-- Continuous contractive restriction from `Lᵖ(μ)` to `Lᵖ(ν)` for `ν ≤ μ`. -/
noncomputable def lpMonoMeasure (μ ν : Measure α) (hνμ : ν ≤ μ) :
    Lp E p μ →L[ℝ] Lp E p ν :=
  LinearMap.mkContinuous (lpMonoMeasureLinearMap μ ν hνμ) 1 (fun f => by
    simpa only [one_mul] using norm_lpMonoMeasureLinearMap_le μ ν hνμ f)

/-- The restriction map is represented almost everywhere by the original
`Lᵖ(μ)` representative. -/
theorem coeFn_lpMonoMeasure_ae
    (μ ν : Measure α) (hνμ : ν ≤ μ) (f : Lp E p μ) :
    ⇑(lpMonoMeasure μ ν hνμ f) =ᵐ[ν] (f : α → E) := by
  exact ((Lp.memLp f).mono_measure hνμ).coeFn_toLp

/-- The continuous restriction map contracts the quotient norm. -/
theorem norm_lpMonoMeasure_le
    (μ ν : Measure α) (hνμ : ν ≤ μ) (f : Lp E p μ) :
    ‖lpMonoMeasure μ ν hνμ f‖ ≤ ‖f‖ :=
  norm_lpMonoMeasureLinearMap_le μ ν hνμ f

/-- The representative seminorm contracts under the dominated measure. -/
theorem eLpNorm_coeFn_lpMonoMeasure_le
    (μ ν : Measure α) (hνμ : ν ≤ μ) (f : Lp E p μ) :
    eLpNorm (lpMonoMeasure μ ν hνμ f : α → E) p ν ≤
      eLpNorm (f : α → E) p μ := by
  rw [eLpNorm_congr_ae (coeFn_lpMonoMeasure_ae μ ν hνμ f)]
  exact eLpNorm_mono_measure (f : α → E) hνμ

end

end PDE
