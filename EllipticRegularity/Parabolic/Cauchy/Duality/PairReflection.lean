module

public import EllipticRegularity.Parabolic.Cauchy.Duality.PairData

@[expose] public section

namespace PDE.Parabolic.Duality

open MeasureTheory Set

/-- Reflection `τ ↦ c - τ` transports an open-left interval to its reflected open-left
interval; the two possible endpoint conventions differ only on a null set. -/
theorem time_reflection_preserving_Ioc_shift (c l r : ℝ) :
    MeasurePreserving (fun τ : ℝ => c - τ)
      (volume.restrict (Ioc l r))
      (volume.restrict (Ioc (c - r) (c - l))) := by
  let ρ : ℝ → ℝ := fun τ => c - τ
  let S : Set ℝ := Ioc (c - r) (c - l)
  have hneg : MeasurePreserving (fun τ : ℝ => -τ) (volume : Measure ℝ) volume :=
    Measure.measurePreserving_neg volume
  have hadd : MeasurePreserving (fun τ : ℝ => c + τ) volume volume :=
    MeasureTheory.measurePreserving_add_left volume c
  have hfull : MeasurePreserving ρ volume volume := by
    convert hadd.comp hneg using 1
    ext τ
    simp [ρ, sub_eq_add_neg]
  have hpre : ρ ⁻¹' S = Ico l r := by
    ext τ
    simp only [S, mem_preimage, ρ, mem_Ioc, mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith [h2], by linarith [h1]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith [h2], by linarith [h1]⟩
  have hrestrictEq : volume.restrict (Ico l r) = volume.restrict (Ioc l r) :=
    Measure.restrict_congr_set Ico_ae_eq_Ioc
  have hrestrict := hfull.restrict_preimage
    (s := S) measurableSet_Ioc
  rw [hpre, hrestrictEq] at hrestrict
  simpa [ρ, S] using hrestrict

/-- Reflection about the midpoint of `[s,t]` preserves volume restricted to `Ioc s t`. -/
theorem time_reflection_preserving_Ioc (s t : ℝ) :
    MeasurePreserving (fun τ : ℝ => s + t - τ)
      (volume.restrict (Ioc s t)) (volume.restrict (Ioc s t)) := by
  let ρ : ℝ → ℝ := fun τ => s + t - τ
  let S : Set ℝ := Ioc s t
  have hneg : MeasurePreserving (fun τ : ℝ => -τ) (volume : Measure ℝ) volume :=
    Measure.measurePreserving_neg volume
  have hadd : MeasurePreserving (fun τ : ℝ => (s + t) + τ) volume volume :=
    MeasureTheory.measurePreserving_add_left volume (s + t)
  have hfull : MeasurePreserving ρ volume volume := by
    convert hadd.comp hneg using 1
    ext τ
    simp [ρ, sub_eq_add_neg, add_assoc]
  have hpre : ρ ⁻¹' S = Ico s t := by
    ext τ
    simp only [S, mem_preimage, ρ, mem_Ioc, mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith [h2], by linarith [h1]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith [h2], by linarith [h1]⟩
  have hrestrictEq : volume.restrict (Ico s t) = volume.restrict (Ioc s t) :=
    Measure.restrict_congr_set Ico_ae_eq_Ioc
  have hrestrict := hfull.restrict_preimage
    (s := S) measurableSet_Ioc
  rw [hpre, hrestrictEq] at hrestrict
  simpa [ρ, S] using hrestrict

/-- Time reflection preserves space-time volume restricted to a compact spatial collar and an
open-left time slab. The reflected preimage is `Ico`; the endpoint discrepancy is null. -/
theorem time_reflection_preserving_collar_Ioc_shift {d : ℕ} (K : Set (Vec d))
    (hK : MeasurableSet K) (c l r : ℝ) :
    MeasurePreserving
      (fun z : Vec d × ℝ => (z.1, c - z.2))
      (volume.restrict (K ×ˢ Ioc l r))
      (volume.restrict (K ×ˢ Ioc (c - r) (c - l))) := by
  let ρ : ℝ → ℝ := fun τ => c - τ
  let R : Vec d × ℝ → Vec d × ℝ := fun z => (z.1, ρ z.2)
  let S : Set (Vec d × ℝ) := K ×ˢ Ioc (c - r) (c - l)
  have hneg : MeasurePreserving (fun τ : ℝ => -τ) (volume : Measure ℝ) volume :=
    Measure.measurePreserving_neg volume
  have hadd : MeasurePreserving (fun τ : ℝ => c + τ) volume volume :=
    MeasureTheory.measurePreserving_add_left volume c
  have htime : MeasurePreserving ρ volume volume := by
    convert hadd.comp hneg using 1
    ext τ
    simp [ρ, sub_eq_add_neg]
  have hprod : MeasurePreserving R
      ((volume : Measure (Vec d)).prod volume)
      ((volume : Measure (Vec d)).prod volume) := by
    convert (MeasurePreserving.id (volume : Measure (Vec d))).prod htime using 1
    rfl
  have hfull : MeasurePreserving R volume volume := by
    simpa only [MeasureTheory.Measure.volume_eq_prod] using hprod
  have hpre : R ⁻¹' S = K ×ˢ Ico l r := by
    ext z
    rcases z with ⟨x, τ⟩
    simp only [R, S, ρ, mem_preimage, mem_prod, mem_Ioc, mem_Ico]
    constructor
    · rintro ⟨hx, hτ⟩
      exact ⟨hx, ⟨by linarith [hτ.2], by linarith [hτ.1]⟩⟩
    · rintro ⟨hx, hτ⟩
      exact ⟨hx, ⟨by linarith [hτ.2], by linarith [hτ.1]⟩⟩
  have hset : K ×ˢ Ico l r =ᵐ[volume] K ×ˢ Ioc l r := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    exact MeasureTheory.Measure.set_prod_ae_eq .rfl Ico_ae_eq_Ioc
  have hrestrictEq : volume.restrict (K ×ˢ Ico l r) =
      volume.restrict (K ×ˢ Ioc l r) := Measure.restrict_congr_set hset
  have hrestrict := hfull.restrict_preimage
    (s := S) (MeasurableSet.prod hK measurableSet_Ioc)
  rw [hpre, hrestrictEq] at hrestrict
  simpa [R, S, ρ] using hrestrict

/-- Time reflection preserves space-time volume restricted to a compact spatial collar and an
open-left time slab. The reflected preimage is `Ico`; the endpoint discrepancy is null. -/
theorem time_reflection_preserving_collar_Ioc {d : ℕ} (K : Set (Vec d))
    (hK : MeasurableSet K) (s t : ℝ) :
    MeasurePreserving
      (fun z : Vec d × ℝ => (z.1, s + t - z.2))
      (volume.restrict (K ×ˢ Ioc s t))
      (volume.restrict (K ×ˢ Ioc s t)) := by
  let ρ : ℝ → ℝ := fun τ => s + t - τ
  let R : Vec d × ℝ → Vec d × ℝ := fun z => (z.1, ρ z.2)
  let S : Set (Vec d × ℝ) := K ×ˢ Ioc s t
  have hneg : MeasurePreserving (fun τ : ℝ => -τ) (volume : Measure ℝ) volume :=
    Measure.measurePreserving_neg volume
  have hadd : MeasurePreserving (fun τ : ℝ => (s + t) + τ) volume volume :=
    MeasureTheory.measurePreserving_add_left volume (s + t)
  have htime : MeasurePreserving ρ volume volume := by
    convert hadd.comp hneg using 1
    ext τ
    simp [ρ, sub_eq_add_neg, add_assoc]
  have hprod : MeasurePreserving R
      ((volume : Measure (Vec d)).prod volume)
      ((volume : Measure (Vec d)).prod volume) := by
    convert (MeasurePreserving.id (volume : Measure (Vec d))).prod htime using 1
    rfl
  have hfull : MeasurePreserving R volume volume := by
    simpa only [MeasureTheory.Measure.volume_eq_prod] using hprod
  have hpre : R ⁻¹' S = K ×ˢ Ico s t := by
    ext z
    rcases z with ⟨x, τ⟩
    simp only [R, S, ρ, mem_preimage, mem_prod, mem_Ioc, mem_Ico]
    constructor
    · rintro ⟨hx, hτ⟩
      exact ⟨hx, ⟨by linarith [hτ.2], by linarith [hτ.1]⟩⟩
    · rintro ⟨hx, hτ⟩
      exact ⟨hx, ⟨by linarith [hτ.2], by linarith [hτ.1]⟩⟩
  have hset : K ×ˢ Ico s t =ᵐ[volume] K ×ˢ Ioc s t := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    exact MeasureTheory.Measure.set_prod_ae_eq .rfl Ico_ae_eq_Ioc
  have hrestrictEq : volume.restrict (K ×ˢ Ico s t) =
      volume.restrict (K ×ˢ Ioc s t) := Measure.restrict_congr_set hset
  have hrestrict := hfull.restrict_preimage
    (s := S) (MeasurableSet.prod hK measurableSet_Ioc)
  rw [hpre, hrestrictEq] at hrestrict
  simpa [R, S, ρ] using hrestrict

end PDE.Parabolic.Duality
