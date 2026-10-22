module

public import PDEFoundation.Sobolev.W1p.ConvexApprox.SmoothRepresentative
public import PDEFoundation.Sobolev.WeakDerivative.Affine
public import PDEFoundation.Sobolev.WeakDerivative.Algebra
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Weak derivatives of convex-domain smoothing: integrability helpers

This file proves that convex approximation commutes with weak partial
derivatives up to the exact affine factor `1 - ε`. The proof first transports
weak derivatives through each fixed affine sampling map, then uses compact
local integrability and Fubini to average over the smoothing kernel.

## Main results

* `PDE.HasWeakPartialDerivOn.comp_convexApproxSample`: exact weak derivative
  under a fixed convex-approximation sampling map.
* `PDE.HasWeakPartialDerivOn.convexApproxSmoothing`: exact distributional
  derivative identity for the smoothing operator.
* `PDE.HasWeakGradientOn.convexApproxSmoothing`: coordinate-gradient form.
-/

@[expose] public section

open scoped Pointwise

namespace PDE

namespace HasWeakPartialDerivOn

/-- Precomposition by the affine convex-approximation sample multiplies a
weak partial derivative by the exact linear factor `1 - ε`. -/
theorem comp_convexApproxSample
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {i : Fin d} {u gi : Vec d → ℝ}
    (hu : HasWeakPartialDerivOn U i u gi)
    {x0 z : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    HasWeakPartialDerivOn U i
      (fun x => u (convexApproxSample x0 z r ε x))
      (fun x =>
        (1 - ε) * gi (convexApproxSample x0 z r ε x)) := by
  let a : ℝ := 1 - ε
  let b : Vec d := ε • (x0 - r • z)
  let V : Set (Vec d) := translateSet b (a • U)
  have ha : 0 < a := by
    dsimp only [a]
    linarith
  have hmap :
      Set.MapsTo (convexApproxSample x0 z r ε) U U :=
    convexApproxSample_mapsTo_of_isOpenBoundedConvexDomain
      hU hball hr hz hε0 hε1.le
  have hVU : V ⊆ U := by
    exact
      translateSet_smul_subset_of_convexApproxSample_mapsTo
        (x0 := x0) (z := z) (r := r) (ε := ε) hmap
  have hV :
      IsOpenBoundedConvexDomain V := by
    simpa only [V] using
      (hU.smul_of_pos ha).translateSet b
  have hRestricted :
      HasWeakPartialDerivOn V i u gi :=
    hu.restrict hV.isOpen hVU
  have hTranslated :
      HasWeakPartialDerivOn (a • U) i
        (fun x => u (x + b)) (fun x => gi (x + b)) := by
    simpa only [V, translateSet_translateSet, add_neg_cancel,
      translateSet_zero, sub_neg_eq_add] using
      hRestricted.translate (-b)
  have hDilated :
      HasWeakPartialDerivOn U i
        (fun x => a⁻¹ * u (a • x + b))
        (fun x => gi (a • x + b)) := by
    have h :=
      hTranslated.dilate_of_pos (inv_pos.mpr ha)
    simpa only [inv_inv, smul_smul,
      inv_mul_cancel₀ ha.ne', one_smul] using h
  have hScaled := hDilated.smul a
  change
    HasWeakPartialDerivOn U i
      (fun x => a * (a⁻¹ * u (a • x + b)))
      (fun x => a * gi (a • x + b)) at hScaled
  simpa only [Pi.smul_apply, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ ha.ne', one_mul, a, b,
    convexApproxSample] using hScaled

end HasWeakPartialDerivOn

namespace HasWeakGradientOn

/-- Coordinate-gradient form of
`HasWeakPartialDerivOn.comp_convexApproxSample`. -/
theorem comp_convexApproxSample
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : HasWeakGradientOn U u Du)
    {x0 z : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    HasWeakGradientOn U
      (fun x => u (convexApproxSample x0 z r ε x))
      (fun x i =>
        (1 - ε) * Du (convexApproxSample x0 z r ε x) i) := by
  intro i
  exact
    (hu i).comp_convexApproxSample
      hU hball hr hz hε0 hε1

end HasWeakGradientOn

private theorem integrableOn_comp_smul_add_for_weakSmoothing
    {d : ℕ} {K : Set (Vec d)} {u : Vec d → ℝ}
    {a : ℝ} (ha : 0 < a) (b : Vec d)
    (hK : MeasurableSet K)
    (hu : MeasureTheory.IntegrableOn u
      (translateSet b (a • K)) MeasureTheory.volume) :
    MeasureTheory.IntegrableOn
      (fun x => u (a • x + b)) K MeasureTheory.volume := by
  have haNe : a ≠ 0 := ha.ne'
  let V : Set (Vec d) := translateSet b (a • K)
  have hV : MeasurableSet V := by
    have hpre :
        ⇑(Homeomorph.subRight b) ⁻¹' (a • K) = V := by
      ext x
      simp [V, mem_translateSet_iff_sub_mem]
    rw [← hpre]
    have haK : MeasurableSet (a • K) :=
      ((Homeomorph.smulOfNeZero a haNe).toMeasurableEquiv.measurableSet_image).2
        hK
    exact
      ((Homeomorph.subRight b).toMeasurableEquiv.measurableSet_preimage).2
        haK
  have hIndicator :
      MeasureTheory.Integrable
        (Set.indicator V u) MeasureTheory.volume :=
    hu.integrable_indicator hV
  have hTranslated :
      MeasureTheory.Integrable
        (fun x => Set.indicator V u (x + b))
        MeasureTheory.volume := by
    exact
      (MeasureTheory.measurePreserving_add_right
        (MeasureTheory.volume :
          MeasureTheory.Measure (Vec d)) b).integrable_comp_of_integrable
            hIndicator
  have hScaled :
      MeasureTheory.Integrable
        (fun x => Set.indicator V u (a • x + b))
        MeasureTheory.volume := by
    let g : Vec d → ℝ :=
      fun x => Set.indicator V u (x + b)
    have hg :
        MeasureTheory.Integrable g MeasureTheory.volume := by
      simpa only [g] using hTranslated
    simpa only [g, Function.comp_apply] using
      hg.comp_smul haNe
  have hIndicatorEq :
      Set.indicator K (fun x => u (a • x + b)) =
        fun x => Set.indicator V u (a • x + b) := by
    funext x
    by_cases hx : x ∈ K
    · have hyV : a • x + b ∈ V :=
        ⟨a • x, Set.smul_mem_smul_set hx, rfl⟩
      simp only [Set.indicator_of_mem hx,
        Set.indicator_of_mem hyV]
    · have hyV : a • x + b ∉ V := by
        intro hyV
        rcases hyV with ⟨w, hw, hyw⟩
        rcases Set.mem_smul_set.mp hw with
          ⟨x', hx', rfl⟩
        have hxx' : x = x' := by
          have h :=
            congrArg
              (fun q : Vec d => a⁻¹ • (q - b)) hyw
          simpa only [add_sub_cancel_right, smul_smul,
            inv_mul_cancel₀ haNe, one_smul] using h
        exact hx (hxx' ▸ hx')
      simp only [Set.indicator_of_notMem hx,
        Set.indicator_of_notMem hyV]
  refine
    (MeasureTheory.integrable_indicator_iff hK).1 ?_
  exact hIndicatorEq ▸ hScaled

private theorem
    integrableOn_comp_convexApproxSample_of_locallyIntegrableOn_for_weakSmoothing
    {d : ℕ} {U K : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {u : Vec d → ℝ}
    (hu : MeasureTheory.LocallyIntegrableOn
      u U MeasureTheory.volume)
    (hKU : K ⊆ U) (hK : IsCompact K)
    {x0 z : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    MeasureTheory.IntegrableOn
      (fun x => u (convexApproxSample x0 z r ε x))
      K MeasureTheory.volume := by
  let a : ℝ := 1 - ε
  let b : Vec d := ε • (x0 - r • z)
  let V : Set (Vec d) := translateSet b (a • K)
  have ha : 0 < a := by
    dsimp only [a]
    linarith
  have hmap :
      Set.MapsTo (convexApproxSample x0 z r ε) U U :=
    convexApproxSample_mapsTo_of_isOpenBoundedConvexDomain
      hU hball hr hz hε0 hε1.le
  have hVU : V ⊆ U := by
    intro y hy
    rcases hy with ⟨w, hw, hyw⟩
    rcases Set.mem_smul_set.mp hw with ⟨x, hx, rfl⟩
    have hyU :
        convexApproxSample x0 z r ε x ∈ U :=
      hmap (hKU hx)
    rw [hyw]
    simpa only [convexApproxSample, a, b] using hyU
  have hV : IsCompact V := by
    have hImage :
        (fun x : Vec d => a • x + b) '' K = V := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact
          ⟨a • x, Set.smul_mem_smul_set hx, rfl⟩
      · rintro ⟨w, hw, hyw⟩
        rcases Set.mem_smul_set.mp hw with
          ⟨x, hx, rfl⟩
        exact ⟨x, hx, hyw.symm⟩
    rw [← hImage]
    exact
      hK.image (by fun_prop)
  have huV :
      MeasureTheory.IntegrableOn u V
        MeasureTheory.volume :=
    hu.integrableOn_compact_subset hVU hV
  simpa only [convexApproxSample, a, b, V] using
    (integrableOn_comp_smul_add_for_weakSmoothing
      (d := d) (u := u) (a := a) ha b
      hK.measurableSet huV)

private theorem
    integrableOn_kernel_mul_indicator_comp_convexApproxSample_mul
    {d : ℕ} {U K : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {u ρ ψ : Vec d → ℝ}
    (hu : MeasureTheory.LocallyIntegrableOn
      u U MeasureTheory.volume)
    (hψ : Continuous ψ) (hKU : K ⊆ U)
    (hK : IsCompact K)
    {x0 z : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    MeasureTheory.IntegrableOn
      (fun x =>
        ρ z *
          Set.indicator U u
            (convexApproxSample x0 z r ε x) *
          ψ x)
      K MeasureTheory.volume := by
  have hcomp :
      MeasureTheory.IntegrableOn
        (fun x =>
          u (convexApproxSample x0 z r ε x))
        K MeasureTheory.volume :=
    integrableOn_comp_convexApproxSample_of_locallyIntegrableOn_for_weakSmoothing
      hU hu hKU hK hball hr hz hε0 hε1
  have hmap :
      Set.MapsTo (convexApproxSample x0 z r ε) U U :=
    convexApproxSample_mapsTo_of_isOpenBoundedConvexDomain
      hU hball hr hz hε0 hε1.le
  have hmul :
      MeasureTheory.IntegrableOn
        (fun x =>
          u (convexApproxSample x0 z r ε x) * ψ x)
        K MeasureTheory.volume :=
    hcomp.mul_continuousOn hψ.continuousOn hK
  have hIndicator :
      MeasureTheory.IntegrableOn
        (fun x =>
          Set.indicator U u
              (convexApproxSample x0 z r ε x) *
            ψ x)
        K MeasureTheory.volume := by
    rw [MeasureTheory.IntegrableOn] at hmul ⊢
    refine hmul.congr ?_
    filter_upwards
      [MeasureTheory.ae_restrict_mem hK.measurableSet]
        with x hx
    rw [Set.indicator_of_mem (hmap (hKU hx))]
  rw [MeasureTheory.IntegrableOn]
  simpa only [mul_assoc] using
    hIndicator.integrable.const_mul (ρ z)

private theorem quasiMeasurePreserving_convexApproxSample_prod
    {d : ℕ} {U : Set (Vec d)}
    {ρ : Vec d → ℝ} (x0 : Vec d)
    (r ε : ℝ) (hε1 : ε < 1) :
    MeasureTheory.Measure.QuasiMeasurePreserving
      (fun p : Vec d × Vec d =>
        convexApproxSample x0 p.2 r ε p.1)
      ((MeasureTheory.volume.restrict U).prod
        (MeasureTheory.volume.restrict (tsupport ρ)))
      MeasureTheory.volume := by
  refine
    MeasureTheory.QuasiMeasurePreserving.prod_of_left
      ?_ ?_
  · unfold convexApproxSample
    fun_prop
  · refine Filter.Eventually.of_forall ?_
    intro z
    let a : ℝ := 1 - ε
    let b : Vec d := ε • (x0 - r • z)
    have haNe : a ≠ 0 := by
      dsimp only [a]
      linarith
    have hsmul :
        MeasureTheory.Measure.QuasiMeasurePreserving
          (fun x : Vec d => a • x)
          MeasureTheory.volume MeasureTheory.volume :=
      MeasureTheory.Measure.quasiMeasurePreserving_smul
        (μ := MeasureTheory.volume) haNe
    have hadd :
        MeasureTheory.MeasurePreserving
          (fun x : Vec d => x + b)
          MeasureTheory.volume MeasureTheory.volume :=
      MeasureTheory.measurePreserving_add_right
        MeasureTheory.volume b
    have hsample :
        MeasureTheory.Measure.QuasiMeasurePreserving
          (convexApproxSample x0 z r ε)
          MeasureTheory.volume MeasureTheory.volume := by
      have h := hadd.quasiMeasurePreserving.comp hsmul
      convert h using 1
      funext x
      rfl
    exact
      hsample.mono_left
        MeasureTheory.Measure.absolutelyContinuous_restrict

private theorem
    aestronglyMeasurable_kernel_mul_indicator_comp_convexApproxSample_prod_mul
    {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U)
    {u ρ ψ : Vec d → ℝ}
    (hu : MeasureTheory.LocallyIntegrableOn
      u U MeasureTheory.volume)
    (hρ : IsConvexApproxKernel ρ)
    (hψ : Continuous ψ) (hψU : tsupport ψ ⊆ U)
    {x0 : Vec d} {r ε : ℝ} (hε1 : ε < 1) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : Vec d × Vec d =>
        ρ p.2 *
          Set.indicator U u
            (convexApproxSample x0 p.2 r ε p.1) *
          ψ p.1)
      ((MeasureTheory.volume.restrict (tsupport ψ)).prod
        (MeasureTheory.volume.restrict (tsupport ρ))) := by
  let μψ : MeasureTheory.Measure (Vec d) :=
    MeasureTheory.volume.restrict (tsupport ψ)
  let μρ : MeasureTheory.Measure (Vec d) :=
    MeasureTheory.volume.restrict (tsupport ρ)
  have huIndicator :
      MeasureTheory.AEStronglyMeasurable
        (Set.indicator U u) MeasureTheory.volume := by
    exact
      (aestronglyMeasurable_indicator_iff
        hU).2 hu.aestronglyMeasurable
  have hbase :
      MeasureTheory.AEStronglyMeasurable
        (fun p : Vec d × Vec d =>
          Set.indicator U u
            (convexApproxSample x0 p.2 r ε p.1))
        ((MeasureTheory.volume.restrict U).prod μρ) := by
    exact
      huIndicator.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_convexApproxSample_prod
          (U := U) (ρ := ρ) x0 r ε hε1)
  have hμψ :
      μψ ≤ MeasureTheory.volume.restrict U :=
    MeasureTheory.Measure.restrict_mono_set
      MeasureTheory.volume hψU
  have hprod :
      μψ.prod μρ ≤
        (MeasureTheory.volume.restrict U).prod μρ := by
    refine MeasureTheory.Measure.le_iff.2 ?_
    intro s hs
    rw [MeasureTheory.Measure.prod_apply hs,
      MeasureTheory.Measure.prod_apply hs]
    exact MeasureTheory.lintegral_mono' hμψ le_rfl
  have hcomp :
      MeasureTheory.AEStronglyMeasurable
        (fun p : Vec d × Vec d =>
          Set.indicator U u
            (convexApproxSample x0 p.2 r ε p.1))
        (μψ.prod μρ) :=
    hbase.mono_measure hprod
  have hρMeas :
      MeasureTheory.AEStronglyMeasurable
        (fun p : Vec d × Vec d => ρ p.2)
        (μψ.prod μρ) :=
    (hρ.continuous.comp continuous_snd).aestronglyMeasurable
  have hψMeas :
      MeasureTheory.AEStronglyMeasurable
        (fun p : Vec d × Vec d => ψ p.1)
        (μψ.prod μρ) :=
    (hψ.comp continuous_fst).aestronglyMeasurable
  have h := hρMeas.mul (hcomp.mul hψMeas)
  convert h using 1
  funext p
  simp only [Pi.mul_apply, mul_assoc]

private theorem integrableOn_comp_convexApproxSample_for_weakSmoothing
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {u : Vec d → ℝ}
    (hu : MeasureTheory.IntegrableOn
      u U MeasureTheory.volume)
    {x0 z : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    MeasureTheory.IntegrableOn
      (fun x => u (convexApproxSample x0 z r ε x))
      U MeasureTheory.volume := by
  let a : ℝ := 1 - ε
  let b : Vec d := ε • (x0 - r • z)
  let V : Set (Vec d) := translateSet b (a • U)
  have ha : 0 < a := by
    dsimp only [a]
    linarith
  have hmap :
      Set.MapsTo (convexApproxSample x0 z r ε) U U :=
    convexApproxSample_mapsTo_of_isOpenBoundedConvexDomain
      hU hball hr hz hε0 hε1.le
  have hVU : V ⊆ U :=
    translateSet_smul_subset_of_convexApproxSample_mapsTo
      (x0 := x0) (z := z) (r := r) (ε := ε) hmap
  have huV :
      MeasureTheory.IntegrableOn u V
        MeasureTheory.volume :=
    hu.mono_set hVU
  simpa only [convexApproxSample, a, b, V] using
    (integrableOn_comp_smul_add_for_weakSmoothing
      (d := d) (u := u) (a := a) ha b
      hU.measurableSet huV)

private theorem
    integrable_kernel_mul_indicator_comp_convexApproxSample_prod_mul_of_integrableOn
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {u ρ ψ : Vec d → ℝ}
    (hu : MeasureTheory.IntegrableOn
      u U MeasureTheory.volume)
    (hρ : IsConvexApproxKernel ρ)
    (hψ : Continuous ψ)
    (hψCompact : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ U)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) :
    MeasureTheory.Integrable
      (fun p : Vec d × Vec d =>
        ρ p.2 *
          Set.indicator U u
            (convexApproxSample x0 p.2 r ε p.1) *
          ψ p.1)
      ((MeasureTheory.volume.restrict (tsupport ψ)).prod
        (MeasureTheory.volume.restrict (tsupport ρ))) := by
  let μψ : MeasureTheory.Measure (Vec d) :=
    MeasureTheory.volume.restrict (tsupport ψ)
  let μρ : MeasureTheory.Measure (Vec d) :=
    MeasureTheory.volume.restrict (tsupport ρ)
  let a : ℝ := 1 - ε
  have ha : 0 < a := by
    dsimp only [a]
    linarith
  have huLoc :
      MeasureTheory.LocallyIntegrableOn
        u U MeasureTheory.volume :=
    hu.locallyIntegrableOn
  have hmeas :
      MeasureTheory.AEStronglyMeasurable
        (fun p : Vec d × Vec d =>
          ρ p.2 *
            Set.indicator U u
              (convexApproxSample x0 p.2 r ε p.1) *
            ψ p.1)
        (μψ.prod μρ) := by
    simpa only [μψ, μρ] using
      aestronglyMeasurable_kernel_mul_indicator_comp_convexApproxSample_prod_mul
        hU.measurableSet huLoc hρ hψ hψU hε1
  refine (MeasureTheory.integrable_prod_iff' hmeas).2 ?_
  constructor
  · filter_upwards
      [MeasureTheory.ae_restrict_mem
        hρ.compactSupport.isCompact.measurableSet]
        with z hz
    have hzNorm : ‖z‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall,
        dist_zero_right] using
          hρ.support_subset_closedBall hz
    simpa only [μψ, MeasureTheory.Integrable] using
      (integrableOn_kernel_mul_indicator_comp_convexApproxSample_mul
        hU huLoc hψ hψU hψCompact.isCompact
        hball hr hzNorm hε0 hε1).integrable
  · obtain ⟨C0, hC0⟩ :=
      hψCompact.exists_bound_of_continuous hψ
    let Cψ : ℝ := max C0 0
    have hCψNonneg : 0 ≤ Cψ := by
      dsimp only [Cψ]
      positivity
    have hψBound : ∀ x, ‖ψ x‖ ≤ Cψ := by
      intro x
      exact (hC0 x).trans (le_max_left _ _)
    let Cu : ℝ :=
      ∫ y in U, |u y| ∂MeasureTheory.volume
    have hCuNonneg : 0 ≤ Cu := by
      dsimp only [Cu]
      exact MeasureTheory.integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun y => abs_nonneg _)
    let bound : Vec d → ℝ :=
      fun z => ρ z * (Cψ * ((a ^ d)⁻¹ * Cu))
    have hbound :
        MeasureTheory.Integrable bound μρ := by
      have hboundVolume :
          MeasureTheory.Integrable
            bound MeasureTheory.volume := by
        have hcont : Continuous bound := by
          dsimp only [bound]
          exact hρ.continuous.mul continuous_const
        have hcompact : HasCompactSupport bound := by
          exact hρ.compactSupport.mul_right
        exact
          hcont.integrable_of_hasCompactSupport hcompact
      simpa only [μρ] using
        (MeasureTheory.Integrable.restrict
          (s := tsupport ρ) hboundVolume)
    have hinnerMeas :
        MeasureTheory.AEStronglyMeasurable
          (fun z =>
            ∫ x,
              ‖ρ z *
                Set.indicator U u
                  (convexApproxSample x0 z r ε x) *
                ψ x‖ ∂μψ)
          μρ := by
      exact hmeas.norm.prod_swap.integral_prod_right'
    refine
      MeasureTheory.Integrable.mono
        hbound hinnerMeas ?_
    filter_upwards with z
    by_cases hzρ : z ∈ tsupport ρ
    · let V : Set (Vec d) :=
        translateSet
          (ε • (x0 - r • z)) (a • U)
      have hzNorm : ‖z‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall,
          dist_zero_right] using
            hρ.support_subset_closedBall hzρ
      have hmap :
          Set.MapsTo
            (convexApproxSample x0 z r ε) U U :=
        convexApproxSample_mapsTo_of_isOpenBoundedConvexDomain
          hU hball hr hzNorm hε0 hε1.le
      have hsampleψ :
          MeasureTheory.IntegrableOn
            (fun x =>
              |u (convexApproxSample x0 z r ε x)|)
            (tsupport ψ) MeasureTheory.volume := by
        have huNorm :
            MeasureTheory.IntegrableOn
              (fun y => ‖u y‖) U
              MeasureTheory.volume :=
          hu.norm
        simpa only [Real.norm_eq_abs] using
          integrableOn_comp_convexApproxSample_of_locallyIntegrableOn_for_weakSmoothing
            hU huNorm.locallyIntegrableOn hψU
            hψCompact.isCompact hball hr hzNorm
            hε0 hε1
      have hsampleU :
          MeasureTheory.IntegrableOn
            (fun x =>
              |u (convexApproxSample x0 z r ε x)|)
            U MeasureTheory.volume := by
        have huNorm :
            MeasureTheory.IntegrableOn
              (fun y => ‖u y‖) U
              MeasureTheory.volume :=
          hu.norm
        simpa only [Real.norm_eq_abs] using
          integrableOn_comp_convexApproxSample_for_weakSmoothing
            hU huNorm hball hr hzNorm hε0 hε1
      have hdom :
          MeasureTheory.Integrable
            (fun x =>
              ρ z *
                (|u (convexApproxSample x0 z r ε x)| *
                  Cψ))
            μψ := by
        simpa only [μψ, MeasureTheory.Integrable,
          mul_assoc, mul_left_comm, mul_comm] using
          ((hsampleψ.integrable.mul_const Cψ).const_mul
            (ρ z))
      have hinner :
          MeasureTheory.Integrable
            (fun x =>
              ρ z *
                Set.indicator U u
                  (convexApproxSample x0 z r ε x) *
                ψ x)
            μψ := by
        simpa only [μψ, MeasureTheory.Integrable] using
          (integrableOn_kernel_mul_indicator_comp_convexApproxSample_mul
            hU huLoc hψ hψU hψCompact.isCompact
            hball hr hzNorm hε0 hε1).integrable
      have hpointwise :
          (fun x =>
            ‖ρ z *
              Set.indicator U u
                (convexApproxSample x0 z r ε x) *
              ψ x‖) ≤ᵐ[μψ]
            (fun x =>
              ρ z *
                (|u (convexApproxSample x0 z r ε x)| *
                  Cψ)) := by
        filter_upwards
          [MeasureTheory.ae_restrict_mem
            hψCompact.isCompact.measurableSet]
            with x hx
        have hxU : x ∈ U := hψU hx
        have hsampleU :
            convexApproxSample x0 z r ε x ∈ U :=
          hmap hxU
        calc
          ‖ρ z *
              Set.indicator U u
                (convexApproxSample x0 z r ε x) *
              ψ x‖ =
              ρ z *
                (|u (convexApproxSample x0 z r ε x)| *
                  ‖ψ x‖) := by
            rw [Set.indicator_of_mem hsampleU]
            simp only [Real.norm_eq_abs, norm_mul,
              abs_of_nonneg (hρ.nonneg z)]
            ring
          _ ≤ ρ z *
              (|u (convexApproxSample x0 z r ε x)| *
                Cψ) := by
            refine mul_le_mul_of_nonneg_left ?_
              (hρ.nonneg z)
            exact mul_le_mul_of_nonneg_left
              (hψBound x) (abs_nonneg _)
      have hsampleBound :
          ∫ x,
              |u (convexApproxSample x0 z r ε x)|
              ∂μψ ≤
            (a ^ d)⁻¹ * Cu := by
        have hmono :
            (∫ x in tsupport ψ,
                |u (convexApproxSample x0 z r ε x)|
                ∂MeasureTheory.volume) ≤
              ∫ x in U,
                |u (convexApproxSample x0 z r ε x)|
                ∂MeasureTheory.volume := by
          exact
            MeasureTheory.setIntegral_mono_set
              hsampleU
              (Filter.Eventually.of_forall
                fun x => abs_nonneg _)
              (Filter.Eventually.of_forall hψU)
        have hVU : V ⊆ U :=
          translateSet_smul_subset_of_convexApproxSample_mapsTo
            (x0 := x0) (z := z) (r := r)
            (ε := ε) hmap
        have hchange :
            (∫ x in U,
                |u (convexApproxSample x0 z r ε x)|
                ∂MeasureTheory.volume) =
              (a ^ d)⁻¹ *
                ∫ y in V, |u y|
                  ∂MeasureTheory.volume := by
          simpa only [convexApproxSample, a, V,
            smul_eq_mul] using
            (setIntegral_comp_smul_add_of_pos
              (d := d) (E := ℝ) ha
              (ε • (x0 - r • z)) U
              (fun y => |u y|))
        have hVBound :
            (∫ y in V, |u y|
                ∂MeasureTheory.volume) ≤ Cu := by
          exact
            MeasureTheory.setIntegral_mono_set
              hu.norm
              (Filter.Eventually.of_forall
                fun y => abs_nonneg _)
              (Filter.Eventually.of_forall hVU)
        calc
          (∫ x,
              |u (convexApproxSample x0 z r ε x)|
              ∂μψ) =
              ∫ x in tsupport ψ,
                |u (convexApproxSample x0 z r ε x)|
                ∂MeasureTheory.volume := by
            rfl
          _ ≤ ∫ x in U,
              |u (convexApproxSample x0 z r ε x)|
              ∂MeasureTheory.volume :=
            hmono
          _ = (a ^ d)⁻¹ *
              ∫ y in V, |u y|
                ∂MeasureTheory.volume :=
            hchange
          _ ≤ (a ^ d)⁻¹ * Cu := by
            exact mul_le_mul_of_nonneg_left
              hVBound (by positivity)
      show
        ‖∫ x,
            ‖ρ z *
              Set.indicator U u
                (convexApproxSample x0 z r ε x) *
              ψ x‖ ∂μψ‖ ≤
          ‖bound z‖
      calc
        ‖∫ x,
            ‖ρ z *
              Set.indicator U u
                (convexApproxSample x0 z r ε x) *
              ψ x‖ ∂μψ‖ =
            ∫ x,
              ‖ρ z *
                Set.indicator U u
                  (convexApproxSample x0 z r ε x) *
                ψ x‖ ∂μψ := by
          have hnonneg :
              0 ≤
                ∫ x,
                  ‖ρ z *
                    Set.indicator U u
                      (convexApproxSample x0 z r ε x) *
                    ψ x‖ ∂μψ :=
            MeasureTheory.integral_nonneg_of_ae
              (Filter.Eventually.of_forall
                fun x => norm_nonneg _)
          rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
        _ ≤ ∫ x,
            ρ z *
              (|u (convexApproxSample x0 z r ε x)| *
                Cψ) ∂μψ :=
          MeasureTheory.integral_mono_ae
            hinner.norm hdom hpointwise
        _ = ρ z *
            (Cψ *
              ∫ x,
                |u (convexApproxSample x0 z r ε x)|
                ∂μψ) := by
          rw [MeasureTheory.integral_const_mul,
            MeasureTheory.integral_mul_const]
          ring
        _ ≤ ρ z * (Cψ * ((a ^ d)⁻¹ * Cu)) := by
          refine mul_le_mul_of_nonneg_left ?_
            (hρ.nonneg z)
          exact mul_le_mul_of_nonneg_left
            hsampleBound hCψNonneg
        _ = bound z := by
          rfl
        _ = ‖bound z‖ := by
          have hboundNonneg : 0 ≤ bound z := by
            dsimp only [bound]
            exact
              mul_nonneg (hρ.nonneg z)
                (mul_nonneg hCψNonneg
                  (mul_nonneg (by positivity) hCuNonneg))
          rw [Real.norm_eq_abs,
            abs_of_nonneg hboundNonneg]
    · have hρz : ρ z = 0 :=
        image_eq_zero_of_notMem_tsupport
          (f := ρ) hzρ
      simp only [bound, hρz, zero_mul, norm_zero,
        MeasureTheory.integral_zero]
      exact le_rfl

theorem
    integrable_kernel_mul_indicator_comp_convexApproxSample_prod_mul
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {u ρ ψ : Vec d → ℝ}
    (hu : MeasureTheory.LocallyIntegrableOn
      u U MeasureTheory.volume)
    (hρ : IsConvexApproxKernel ρ)
    (hψ : Continuous ψ)
    (hψCompact : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ U)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) :
    MeasureTheory.Integrable
      (fun p : Vec d × Vec d =>
        ρ p.2 *
          Set.indicator U u
            (convexApproxSample x0 p.2 r ε p.1) *
          ψ p.1)
      ((MeasureTheory.volume.restrict (tsupport ψ)).prod
        (MeasureTheory.volume.restrict (tsupport ρ))) := by
  let K : Set (Vec d × Vec d) :=
    tsupport ψ ×ˢ tsupport ρ
  let W : Set (Vec d) :=
    (fun p : Vec d × Vec d =>
      convexApproxSample x0 p.2 r ε p.1) '' K
  let uW : Vec d → ℝ := Set.indicator W u
  have hK : IsCompact K :=
    hψCompact.isCompact.prod hρ.compactSupport.isCompact
  have hKMeas : MeasurableSet K :=
    hK.measurableSet
  have hsampleContinuous :
      Continuous
        (fun p : Vec d × Vec d =>
          convexApproxSample x0 p.2 r ε p.1) := by
    unfold convexApproxSample
    fun_prop
  have hW : IsCompact W :=
    hK.image hsampleContinuous
  have hWU : W ⊆ U := by
    rintro y ⟨p, hp, rfl⟩
    have hzNorm : ‖p.2‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall,
        dist_zero_right] using
          hρ.support_subset_closedBall hp.2
    exact
      convexApproxSample_mem_of_isOpenBoundedConvexDomain
        hU (hψU hp.1) hball hr hzNorm hε0 hε1.le
  have huWOnW :
      MeasureTheory.IntegrableOn
        u W MeasureTheory.volume :=
    hu.integrableOn_compact_subset hWU hW
  have huW :
      MeasureTheory.Integrable
        uW MeasureTheory.volume :=
    huWOnW.integrable_indicator hW.measurableSet
  have huWOnU :
      MeasureTheory.IntegrableOn
        uW U MeasureTheory.volume :=
    huW.integrableOn
  have htrunc :
      MeasureTheory.Integrable
        (fun p : Vec d × Vec d =>
          ρ p.2 *
            Set.indicator U uW
              (convexApproxSample x0 p.2 r ε p.1) *
            ψ p.1)
        ((MeasureTheory.volume.restrict (tsupport ψ)).prod
          (MeasureTheory.volume.restrict
            (tsupport ρ))) :=
    integrable_kernel_mul_indicator_comp_convexApproxSample_prod_mul_of_integrableOn
      hU huWOnU hρ hψ hψCompact hψU
      hball hr hε0 hε1
  have hcongr :
      (fun p : Vec d × Vec d =>
        ρ p.2 *
          Set.indicator U uW
            (convexApproxSample x0 p.2 r ε p.1) *
          ψ p.1) =ᵐ[
          (MeasureTheory.volume.restrict (tsupport ψ)).prod
            (MeasureTheory.volume.restrict (tsupport ρ))]
        (fun p : Vec d × Vec d =>
          ρ p.2 *
            Set.indicator U u
              (convexApproxSample x0 p.2 r ε p.1) *
            ψ p.1) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact
      (MeasureTheory.ae_restrict_iff' hKMeas).2
        (Filter.Eventually.of_forall fun p hp => by
          let y : Vec d :=
            convexApproxSample x0 p.2 r ε p.1
          have hyW : y ∈ W :=
            Set.mem_image_of_mem
              (fun q : Vec d × Vec d =>
                convexApproxSample x0 q.2 r ε q.1) hp
          have hyU : y ∈ U := hWU hyW
          have hleft :
              Set.indicator U uW y = u y := by
            rw [Set.indicator_of_mem hyU]
            simpa only [uW] using
              Set.indicator_of_mem
                (s := W) (f := u) hyW
          have hright :
              Set.indicator U u y = u y :=
            Set.indicator_of_mem
              (s := U) (f := u) hyU
          change
            ρ p.2 * Set.indicator U uW y * ψ p.1 =
              ρ p.2 * Set.indicator U u y * ψ p.1
          rw [hleft, hright])
  exact htrunc.congr hcongr

end PDE
