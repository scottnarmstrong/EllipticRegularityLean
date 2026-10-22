module

public import PDEFoundation.Sobolev.Trace.Model.ExtBound

/-!
# Almost-everywhere invariance

`modelExt n g`, the `L^p` norm and the Gagliardo integral only depend on the almost-everywhere class
of `g`, so measurable representatives may be used.  This gives the `W^{1,p}` bound for
every `g ∈ L^p`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

variable {n : ℕ}

theorem modelExt_congr_ae {g h : Vec n → ℝ} (hgh : g =ᵐ[volume] h) :
    modelExt n g = modelExt n h := by
  funext z
  unfold modelExt dilConv
  split_ifs with ht
  · have : (∫ y, dil n (extKernel n) (z.1 - y) z.2 * g y) =
        ∫ y, dil n (extKernel n) (z.1 - y) z.2 * h y :=
      integral_congr_ae (hgh.mono fun y hy => by simp [hy])
    rw [this]
  · rfl

theorem flatGagliardo_congr_ae (q p : ℝ) {g h : Vec n → ℝ} (hgh : g =ᵐ[volume] h) :
    flatGagliardo n q p g = flatGagliardo n q p h := by
  unfold flatGagliardo
  refine lintegral_congr_ae (hgh.mono fun x hx => ?_)
  refine lintegral_congr_ae (hgh.mono fun y hy => ?_)
  simp [hx, hy]

theorem memLp_ae_measurable_rep {p : ℝ} {g : Vec n → ℝ}
    (hg : MemLp g (ENNReal.ofReal p) volume) :
    ∃ g' : Vec n → ℝ, Measurable g' ∧ g =ᵐ[volume] g' ∧ MemLp g' (ENNReal.ofReal p) volume :=
  ⟨hg.aestronglyMeasurable.mk g, hg.aestronglyMeasurable.stronglyMeasurable_mk.measurable,
    hg.aestronglyMeasurable.ae_eq_mk, hg.ae_eq hg.aestronglyMeasurable.ae_eq_mk⟩

/-- The `W^{1,p}` bound for the extension operator. -/
theorem modelExt_bound {p : ℝ} (n : ℕ) (hp : 1 < p) :
    ∃ C : ℝ≥0, ∀ g : Vec n → ℝ, MemLp g (ENNReal.ofReal p) volume →
      ∫⁻ z in upperHalf n, (ENNReal.ofReal (|modelExt n g z| ^ p) +
          ENNReal.ofReal (modelGradNorm (modelExt n g) z ^ p)) ≤
        C * ((∫⁻ x', ENNReal.ofReal (|g x'| ^ p)) + flatGagliardo n ((n : ℝ) + p - 1) p g) := by
  have hq : 1 ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp.le
  obtain ⟨C, hC⟩ := modelExt_bound_aux hp n
  refine ⟨C, fun g hg => ?_⟩
  obtain ⟨g', hgm, hgg', hg'⟩ := memLp_ae_measurable_rep hg
  rw [modelExt_congr_ae hgg', flatGagliardo_congr_ae _ _ hgg']
  have h1 : ∫⁻ x', ENNReal.ofReal (|g x'| ^ p) = ∫⁻ x', ENNReal.ofReal (|g' x'| ^ p) :=
    lintegral_congr_ae (hgg'.mono fun x hx => by simp [hx])
  rw [h1]
  exact hC g' hgm (hg'.locallyIntegrable hq)

end PDE.TraceLane
