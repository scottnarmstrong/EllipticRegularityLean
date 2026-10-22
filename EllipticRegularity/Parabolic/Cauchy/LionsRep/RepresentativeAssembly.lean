module

public import EllipticRegularity.Parabolic.Cauchy.Lions.ClosureData
public import EllipticRegularity.Parabolic.Cauchy.LionsRep.RieszBallAverage
public import EllipticRegularity.Parabolic.Cauchy.Lions.ExistenceAssembly
public import EllipticRegularity.Parabolic.Energy.Limits
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! # Assemble the every-time Lions representative -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped ENNReal

namespace PDE.Parabolic.LionsRep

/-- The spatial `L²` class of a raw Lions slice, with a zero fallback off the a.e.-good set. -/
noncomputable def cauchyEnergySliceLp
    {d : ℕ} {s T : ℝ} (u : PDE.Parabolic.Lions.CauchyX d s T)
    (t : ℝ) : Lp ℝ 2 (volume : Measure (Vec d)) := by
  classical
  exact if h : MemLp (fun x : Vec d => PDE.Parabolic.Lions.cauchyEnergyValue u (x, t))
      2 (volume : Measure (Vec d)) then
    h.toLp (fun x => PDE.Parabolic.Lions.cauchyEnergyValue u (x, t))
  else 0

private theorem cauchyEnergySliceLp_pairing
    {d : ℕ} {s T : ℝ} (u : PDE.Parabolic.Lions.CauchyX d s T)
    {t : ℝ} (ht : MemLp
      (fun x : Vec d => PDE.Parabolic.Lions.cauchyEnergyValue u (x, t))
      2 (volume : Measure (Vec d)))
    (ψ : Vec d → ℝ) (hψ : MemLp ψ 2 (volume : Measure (Vec d))) :
    PDE.Parabolic.Lions.cauchyValuePairing u ψ t =
      inner ℝ (cauchyEnergySliceLp u t) (hψ.toLp ψ) := by
  classical
  rw [cauchyEnergySliceLp, dite_eq_left ht, MeasureTheory.L2.inner_def,
    PDE.Parabolic.Lions.cauchyValuePairing]
  apply integral_congr_ae
  filter_upwards [ht.coeFn_toLp, hψ.coeFn_toLp] with x hx hψx
  rw [hx, hψx]
  simp only [Real.inner_apply]

/-- Pairings against every whole-space `L²` test identify the Riesz slices with the raw
Lions energy slices for almost every time. The uniform slice-bound hypothesis is the explicit
step-one input in the existence construction. -/
theorem cauchyRieszSlice_eq_energySlice_ae
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T) {u₀ : PDE.Parabolic.Lions.CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (hglobalSliceBound : PDE.Parabolic.Lions.CauchyGlobalSliceBound
      (a := a) f u) :
    ∀ᵐ t ∂(volume.restrict (Icc s T)),
      cauchyEnergySliceLp u t =
        if ht : t ∈ Icc s T then
          cauchyL2TimeSlice hsT ha f hf u hclose hrep ⟨t, ht⟩ else 0 := by
  classical
  let qSlice : ℝ → Lp ℝ 2 (volume : Measure (Vec d)) := fun t =>
    if ht : t ∈ Icc s T then
      cauchyL2TimeSlice hsT ha f hf u hclose hrep ⟨t, ht⟩ else 0
  have hraw : ∀ᵐ t ∂(volume.restrict (Icc s T)),
      MemLp (fun x : Vec d => PDE.Parabolic.Lions.cauchyEnergyValue u (x, t))
        2 (volume : Measure (Vec d)) := by
    filter_upwards [hglobalSliceBound] with t ht
    exact ht.1
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have hscalar (c : Lp ℝ 2 (volume : Measure (Vec d))) :
      (fun t => inner ℝ c (cauchyEnergySliceLp u t - qSlice t)) =ᵐ[
        volume.restrict (Icc s T)] 0 := by
    let ψ : Vec d → ℝ := c
    let hψ : MemLp ψ 2 (volume : Measure (Vec d)) := by
      simpa [ψ] using Lp.memLp c
    have hψclass : hψ.toLp ψ = c := by
      apply Lp.ext
      filter_upwards [hψ.coeFn_toLp] with x _
      simp [ψ]
    obtain ⟨v, _hvcont, hpair, _hinit, hrawPair⟩ :=
      exists_cauchyL2TimeSlice_pairing_continuous_initial
        hsT ha f hf u hclose hrep ψ hψ
    filter_upwards [hrawPair, hraw, ae_restrict_mem measurableSet_Icc]
      with t hrawEq hrawMem ht
    have hrawEq' : PDE.Parabolic.Lions.cauchyValuePairing u ψ t = v ⟨t, ht⟩ := by
      simpa [ht] using hrawEq
    have hrawInner : inner ℝ c (cauchyEnergySliceLp u t) = v ⟨t, ht⟩ := by
      calc
        inner ℝ c (cauchyEnergySliceLp u t) =
            inner ℝ (cauchyEnergySliceLp u t) c := real_inner_comm _ _
        _ = inner ℝ (cauchyEnergySliceLp u t) (hψ.toLp ψ) := by rw [← hψclass]
        _ = PDE.Parabolic.Lions.cauchyValuePairing u ψ t :=
          (cauchyEnergySliceLp_pairing u hrawMem ψ hψ).symm
        _ = v ⟨t, ht⟩ := hrawEq'
    have hsliceInner : inner ℝ c (qSlice t) = v ⟨t, ht⟩ := by
      have hq := hpair ⟨t, ht⟩
      have hqDef : qSlice t =
          cauchyL2TimeSlice hsT ha f hf u hclose hrep ⟨t, ht⟩ := by
        change (if h : t ∈ Icc s T then
          cauchyL2TimeSlice hsT ha f hf u hclose hrep ⟨t, h⟩ else 0) = _
        rw [dite_eq_left ht]
      calc
        inner ℝ c (qSlice t) =
            inner ℝ c (cauchyL2TimeSlice hsT ha f hf u hclose hrep ⟨t, ht⟩) := by
          rw [hqDef]
        _ = inner ℝ (cauchyL2TimeSlice hsT ha f hf u hclose hrep ⟨t, ht⟩) c :=
          real_inner_comm _ _
        _ = inner ℝ (cauchyL2TimeSlice hsT ha f hf u hclose hrep ⟨t, ht⟩)
            (hψ.toLp ψ) := by rw [← hψclass]
        _ = v ⟨t, ht⟩ := hq
    calc
      inner ℝ c (cauchyEnergySliceLp u t - qSlice t) =
          inner ℝ c (cauchyEnergySliceLp u t) - inner ℝ c (qSlice t) :=
        inner_sub_right _ _ _
      _ = 0 := by rw [hrawInner, hsliceInner]; exact sub_self _
  have hclass := ae_eq_zero_of_forall_inner (μ := volume.restrict (Icc s T))
    (f := fun t => cauchyEnergySliceLp u t - qSlice t) hscalar
  filter_upwards [hclass, ae_restrict_mem measurableSet_Icc] with t hEq ht
  have hEq' : cauchyEnergySliceLp u t = qSlice t := sub_eq_zero.mp hEq
  rw [show qSlice t = cauchyL2TimeSlice hsT ha f hf u hclose hrep ⟨t, ht⟩ by
    change (if h : t ∈ Icc s T then
      cauchyL2TimeSlice hsT ha f hf u hclose hrep ⟨t, h⟩ else 0) = _
    rw [dite_eq_left ht]] at hEq'
  simpa only [dite_eq_left ht] using hEq'

theorem cauchyRieszSliceRepresentative_ae_eq_energyValue
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T) {u₀ : PDE.Parabolic.Lions.CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (hglobalSliceBound : PDE.Parabolic.Lions.CauchyGlobalSliceBound
      (a := a) f u) :
    cauchyRieszSliceRepresentative hsT ha f hf u hclose hrep =ᵐ[
      PDE.Parabolic.Lions.slabMeasure d s T] PDE.Parabolic.Lions.cauchyEnergyValue u := by
  classical
  let R : Vec d × ℝ → ℝ :=
    cauchyRieszSliceRepresentative hsT ha f hf u hclose hrep
  let G : Vec d × ℝ → ℝ := PDE.Parabolic.Lions.cauchyEnergyValue u
  have hclasses := cauchyRieszSlice_eq_energySlice_ae hsT ha f hf u hclose hrep
    hglobalSliceBound
  have hraw : ∀ᵐ t ∂(volume.restrict (Icc s T)),
      MemLp (fun x : Vec d => G (x, t)) 2 (volume : Measure (Vec d)) := by
    filter_upwards [hglobalSliceBound] with t ht
    exact ht.1
  have hNested : ∀ᵐ t ∂(volume.restrict (Icc s T)),
      ∀ᵐ x ∂(volume : Measure (Vec d)), R (x, t) = G (x, t) := by
    filter_upwards [hclasses, hraw, ae_restrict_mem measurableSet_Icc]
      with t hclass hrawMem ht
    have hclass' : cauchyEnergySliceLp u t =
        cauchyL2TimeSlice hsT ha f hf u hclose hrep ⟨t, ht⟩ := by
      simpa only [dite_eq_left ht] using hclass
    have hclassFun : (cauchyEnergySliceLp u t : Vec d → ℝ) =ᵐ[volume]
        (cauchyL2TimeSlice hsT ha f hf u hclose hrep ⟨t, ht⟩ : Vec d → ℝ) := by
      have hfun := congrArg (fun q : Lp ℝ 2 (volume : Measure (Vec d)) =>
        (q : Vec d → ℝ)) hclass'
      exact Filter.Eventually.of_forall fun x => congrFun hfun x
    have hclassRaw : (cauchyEnergySliceLp u t : Vec d → ℝ) =ᵐ[volume]
        (fun x => G (x, t)) := by
      rw [cauchyEnergySliceLp, dite_eq_left hrawMem]
      exact hrawMem.coeFn_toLp
    have hRslice := cauchyRieszSliceRepresentative_ae_eq_slice
      hsT ha f hf u hclose hrep ⟨t, ht⟩
    exact hRslice.trans (hclassFun.symm.trans hclassRaw)
  have hRmeas : Measurable R := by
    dsimp [R]
    exact cauchyRieszSliceRepresentative_measurable hsT ha f hf u hclose hrep
  have hGmeas : Measurable G := by
    dsimp [G]
    exact (PDE.Parabolic.Lions.cauchyEnergyValue_stronglyMeasurable u).measurable
  have hmeasEq : MeasurableSet {z : Vec d × ℝ | R z = G z} :=
    measurableSet_eq_fun hRmeas hGmeas
  have hprod : ∀ᵐ z ∂((volume : Measure (Vec d)).prod
      (volume.restrict (Icc s T))), R z = G z :=
    (Measure.ae_prod_iff_ae_ae hmeasEq).2
      ((Measure.ae_ae_comm hmeasEq).2 hNested)
  have hmeasure : (volume : Measure (Vec d)).prod
      (volume.restrict (Icc s T)) = PDE.Parabolic.Lions.slabMeasure d s T := by
    change (volume : Measure (Vec d)).prod (volume.restrict (Icc s T)) =
      (volume : Measure (Vec d × ℝ)).restrict ((univ : Set (Vec d)) ×ˢ Icc s T)
    calc
      _ = (volume.restrict (univ : Set (Vec d))).prod
          (volume.restrict (Icc s T) : Measure ℝ) := by simp
      _ = (volume : Measure (Vec d × ℝ)).restrict
          ((univ : Set (Vec d)) ×ˢ Icc s T) :=
        (PDE.Parabolic.Energy.volume_restrict_prod univ (Icc s T)).symm
  rw [← hmeasure]
  change R =ᵐ[(volume : Measure (Vec d)).prod
    (volume.restrict (Icc s T))] G
  exact hprod

end PDE.Parabolic.LionsRep
