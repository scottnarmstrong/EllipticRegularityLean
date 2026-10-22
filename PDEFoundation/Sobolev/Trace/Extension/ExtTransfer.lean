module

public import PDEFoundation.Sobolev.Trace.Extension.ExtPtBound
import PDEFoundation.Sobolev.Trace.Smooth.Transfer

/-!
# Transfer of integrals from `Ω` to the half-space, and measurability of the majorants

The chart map preserves Lebesgue measure, so the `p`-th power integral over `Ω` of a function of
the form `u ∘ Ψⱼ⁻¹` supported on the chart cylinder is at most the `p`-th power integral of `u`
over the half-space.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

theorem ext_isOpen_inter_dom (φ : GraphChart Ω) : IsOpen (Ω ∩ φ.dom) := by
  have : Ω ∩ φ.dom = φ.homeo '' (euclideanBall φ.c φ.r ×ˢ Ioo 0 φ.a) := φ.inter_eq
  rw [this]
  exact φ.homeo.isOpenMap _ ((isOpen_euclideanBall _ _).prod isOpen_Ioo)

theorem ext_continuousOn_modelGradNorm {F : Vec n × ℝ → ℝ} (hF : ContDiffOn ℝ 1 F (upperHalf n)) :
    ContinuousOn (modelGradNorm F) (upperHalf n) := by
  have hcont : ContinuousOn (fderiv ℝ F) (upperHalf n) :=
    hF.continuousOn_fderiv_of_isOpen (isOpen_upperHalf n) le_rfl
  have h1 : ContinuousOn (tanGrad F) (upperHalf n) :=
    continuousOn_pi.2 fun i => hcont.clm_apply continuousOn_const
  have h2 : ContinuousOn (normDeriv F) (upperHalf n) := hcont.clm_apply continuousOn_const
  have h3 : ContinuousOn (fun z => vecEuclideanNorm (tanGrad F z)) (upperHalf n) :=
    (continuous_vecEuclideanNorm n).comp_continuousOn h1
  unfold modelGradNorm
  refine Real.continuous_sqrt.comp_continuousOn ?_
  have : ∀ z, vecNormSq (tanGrad F z) = vecEuclideanNorm (tanGrad F z) ^ 2 := fun z =>
    (vecEuclideanNorm_sq _).symm
  simp_rw [this]
  exact (h3.pow 2).add (h2.pow 2)

theorem ExtData.aestronglyMeasurable_majorant (D : ExtData Ω) (j : Fin D.A.N) (K : ℝ)
    {F : Vec n × ℝ → ℝ} (hF : ContDiffOn ℝ 1 F (upperHalf n)) :
    AEStronglyMeasurable (D.majorant j K F) (volume.restrict Ω) := by
  set φ := D.A.chart j with hφ
  have hWo : IsOpen (Ω ∩ φ.dom) := ext_isOpen_inter_dom φ
  have hmaps : MapsTo φ.inv (Ω ∩ φ.dom) (upperHalf n) := fun y hy =>
    ext_inv_mem_upperHalf φ hy.1 hy.2
  have hinv : ContinuousOn φ.inv (Ω ∩ φ.dom) := φ.contDiff_inv.continuous.continuousOn
  have hf : ContinuousOn (fun y => K * (|F (φ.inv y)| + modelGradNorm F (φ.inv y)))
      (Ω ∩ φ.dom) := by
    refine continuousOn_const.mul ?_
    refine ContinuousOn.add ?_ ?_
    · exact (hF.continuousOn.comp hinv hmaps).abs
    · exact (ext_continuousOn_modelGradNorm hF).comp hinv hmaps
  unfold ExtData.majorant
  rw [aestronglyMeasurable_indicator_iff hWo.measurableSet]
  exact (hf.aestronglyMeasurable hWo.measurableSet).mono_measure
    (by
      rw [Measure.restrict_restrict hWo.measurableSet])

/-- Transfer of the `p`-th power integral of a function supported on the chart cylinder. -/
theorem ext_lintegral_majorant_le (φ : GraphChart Ω) {p : ℝ} (hp : 0 < p) (u : Vec n × ℝ → ℝ) :
    ∫⁻ x in Ω, ENNReal.ofReal ((Ω ∩ φ.dom).indicator (fun y => u (φ.inv y)) x ^ p) ≤
      ∫⁻ z in upperHalf n, ENNReal.ofReal (u z ^ p) := by
  set W := Ω ∩ φ.dom with hW
  set G : Vec (n + 1) → ℝ≥0∞ := W.indicator (fun y => ENNReal.ofReal (u (φ.inv y) ^ p)) with hG
  have h1 : ∀ x, ENNReal.ofReal ((W.indicator (fun y => u (φ.inv y)) x) ^ p) = G x := by
    intro x
    by_cases hx : x ∈ W
    · simp [hG, indicator_of_mem hx]
    · simp [hG, indicator_of_notMem hx, Real.zero_rpow hp.ne']
  simp_rw [h1]
  have h2 : ∫⁻ x in Ω, G x ≤ ∫⁻ x, G x := lintegral_mono' Measure.restrict_le_self le_rfl
  have h3 : ∫⁻ z, G (φ.map z) = ∫⁻ y, G y :=
    φ.measurePreserving_map.lintegral_comp_emb φ.homeo.measurableEmbedding G
  have h4 : ∀ z, G (φ.map z) ≤ (upperHalf n).indicator (fun z => ENNReal.ofReal (u z ^ p)) z := by
    intro z
    by_cases hz : φ.map z ∈ W
    · have hinv : φ.inv (φ.map z) = z := graphMapInv_graphMap φ.sgn_sq z
      have hzu : z ∈ upperHalf n := by
        have := ext_inv_mem_upperHalf φ hz.1 hz.2
        rwa [hinv] at this
      rw [hG, indicator_of_mem hz, indicator_of_mem hzu]
      have : φ.inv (φ.map z) = z := hinv
      simp only [this, le_refl]
    · rw [hG, indicator_of_notMem hz]; exact bot_le
  calc ∫⁻ x in Ω, G x ≤ ∫⁻ x, G x := h2
    _ = ∫⁻ z, G (φ.map z) := h3.symm
    _ ≤ ∫⁻ z, (upperHalf n).indicator (fun z => ENNReal.ofReal (u z ^ p)) z := lintegral_mono h4
    _ = _ := lintegral_indicator (measurableSet_upperHalf n) _

end PDE.TraceLane
