module

public import EllipticRegularity.Parabolic.Cauchy.Lions.ClosureData
public import EllipticRegularity.Parabolic.Cauchy.Lions.MollifiedData
public import EllipticRegularity.Parabolic.Cauchy.Lions.MollifiedInitialSlice
public import EllipticRegularity.Parabolic.Cauchy.Energy.Cutoff

/-! # Compact cutoff energy data for the fixed-scale Lions representative -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set Metric

namespace PDE.Parabolic.Lions

/-- The time-continuous representatives of the same spatial mollification agree at every time. -/
theorem cauchyMollified_continuous_rep_unique
    {d : ℕ} {s T ε : ℝ} {F : Vec d × ℝ → ℝ} (hsT : s < T)
    {w₁ w₂ : Vec d × ℝ → ℝ}
    (hcont₁ : ∀ x, ContinuousOn (fun t => w₁ (x, t)) (Icc s T))
    (hcont₂ : ∀ x, ContinuousOn (fun t => w₂ (x, t)) (Icc s T))
    (hae₁ : ∀ x, (fun t => PDE.Parabolic.Energy.mollT ε univ F (x, t)) =ᵐ[
      volume.restrict (Icc s T)] (fun t => w₁ (x, t)))
    (hae₂ : ∀ x, (fun t => PDE.Parabolic.Energy.mollT ε univ F (x, t)) =ᵐ[
      volume.restrict (Icc s T)] (fun t => w₂ (x, t))) :
    ∀ x t, t ∈ Icc s T → w₁ (x, t) = w₂ (x, t) := by
  intro x t ht
  have hae : (fun τ => w₁ (x, τ)) =ᵐ[volume.restrict (Icc s T)]
      (fun τ => w₂ (x, τ)) := (hae₁ x).symm.trans (hae₂ x)
  have heq : EqOn (fun τ => w₁ (x, τ)) (fun τ => w₂ (x, τ)) (Icc s T) :=
    Measure.eqOn_Icc_of_ae_eq (volume : Measure ℝ) hsT.ne hae
      (hcont₁ x) (hcont₂ x)
  exact heq ht

/-- A fixed-scale mollified Lions representative supplies the hypotheses of the abstract compact
cutoff energy identity, on the whole closed time slab. -/
theorem exists_cauchy_mollified_energyData
    {d : ℕ} {lam Lam s T ε : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (hε : 0 < ε) (f : Vec d → ℝ)
    (hf : MemLp f 2 (volume : Measure (Vec d)))
    (u : CauchyX d s T) {u₀ : CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    {t R : ℝ} (hst : s < t) (htT : t ≤ T) (hR : 0 < R) :
    ∃ E : PDE.Parabolic.Energy.Data d,
      E.s = s ∧ E.t = t ∧ E.δ0 = 1 ∧
      E.K = tsupport (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff R hR).toFun ∧
      E.φ = (PDE.Parabolic.Cauchy.Energy.cauchyParabolicCutoff
        (d := d) s T R hR).toFun ∧
      E.u =ᵐ[slabMeasure d s T]
        PDE.Parabolic.Energy.mollT ε univ (cauchyEnergyValue u) ∧
      (∀ i : Fin d, (fun z => E.Du z i) =ᵐ[slabMeasure d s T]
        PDE.Parabolic.Energy.mollT ε univ (fun z => cauchyEnergyGradient u z i)) ∧
      (∀ i : Fin d, (fun z => E.G z i) =ᵐ[slabMeasure d s T]
        PDE.Parabolic.Energy.mollT ε univ
          (fun z => matVecMul (a z) (cauchyEnergyGradient u z) i)) ∧
      (∀ x, ContinuousOn (fun τ => E.u (x, τ)) (Icc s T)) ∧
      (∀ x, (fun τ => PDE.Parabolic.Energy.mollT ε univ
        (cauchyEnergyValue u) (x, τ)) =ᵐ[volume.restrict (Icc s T)]
          (fun τ => E.u (x, τ))) ∧
      (∀ x, E.u (x, s) = PDE.wholeSpaceMollify ε f x) := by
  obtain ⟨W, w, D, G, hwm, hDm, hGm, hwcont, hwsec, hloc, hWmem, hDmem, hGmem,
    hwae, hDae, hGae, hWgrad, ⟨B, hB, hwB⟩, hW, hD⟩ :=
      exists_cauchy_mollified_parabolicFunction hsT ha hε f hf u hclose hrep
  let ζ : Vec d → ℝ := (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff R hR).toFun
  let K : Set (Vec d) := tsupport ζ
  have hK : IsCompact K := by
    dsimp [K, ζ]
    exact (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff R hR).hasCompactSupport.isCompact
  let K1 : Set (Vec d) := cthickening (1 : ℝ) K
  have hK1 : IsCompact K1 := hK.cthickening
  let χ := PDE.Parabolic.Cauchy.Energy.cauchyParabolicCutoff (d := d) s T R hR
  have hinit : ∀ x, w (x, s) = PDE.wholeSpaceMollify ε f x := by
    intro x
    exact cauchyMollified_initialSlice_of_section hsT ha hε f hf u hrep
      w hwcont hwsec x
  have hDmem' : ∀ i : Fin d, MemLp (fun z => D z i) 2 (slabMeasure d s T) := by
    intro i
    simpa only [hD] using W.gradMemL2 i
  have hwmem' : MemLp w 2 (slabMeasure d s T) := by
    simpa only [hW] using W.memL2
  have hslabSub : K1 ×ˢ Ioc s t ⊆ (univ : Set (Vec d)) ×ˢ Icc s T := by
    apply prod_mono (subset_univ _)
    intro τ hτ
    exact ⟨hτ.1.le, hτ.2.trans htT⟩
  have hmeasureLe : volume.restrict (K1 ×ˢ Ioc s t) ≤
      volume.restrict ((univ : Set (Vec d)) ×ˢ Icc s T) :=
    Measure.restrict_mono hslabSub le_rfl
  have hWgFull : ∀ᵐ τ ∂(volume.restrict (Ioc s T)), ∀ a' : ℝ,
        0 < a' → a' ≤ 1 → ∀ x ∈ K, ∀ i,
        ∫ y in K1,
            fderiv ℝ (PDE.Parabolic.Energy.kern a') (x - y) (basisVec i) * w (y, τ) =
          ∫ y in K1,
            PDE.Parabolic.Energy.kern a' (x - y) * D (y, τ) i := by
    exact cauchyMollifiedRepresentative_hwg hK one_pos hW hD hWgrad
  have hsl : ∀ a' : ℝ, 0 < a' → a' ≤ 1 → ∀ x ∈ K,
      ∀ τ1 τ2 : ℝ, s ≤ τ1 → τ1 ≤ τ2 → τ2 ≤ t →
        (∫ y in K1, PDE.Parabolic.Energy.kern a' (x - y) * w (y, τ2)) -
            ∫ y in K1, PDE.Parabolic.Energy.kern a' (x - y) * w (y, τ1) =
          ∫ z in K1 ×ˢ Ioc τ1 τ2,
            ∑ i, G z i * fderiv ℝ (PDE.Parabolic.Energy.kern a')
              (x - z.1) (basisVec i) := by
    intro a' ha' haδ x hx τ1 τ2 h1 h12 h2
    exact cauchyMollifiedRepresentative_hslice hsT ha ha' hε f hf u hrep
      hK one_pos w G hwm hwcont hwae B hB hwB hGmem hGae h1 h12
      (h2.trans htT) haδ x hx
  have hWg : ∀ᵐ τ ∂(volume.restrict (Ioc s t)), ∀ a' : ℝ,
      0 < a' → a' ≤ 1 → ∀ x ∈ K, ∀ i,
        ∫ y in K1,
            fderiv ℝ (PDE.Parabolic.Energy.kern a') (x - y) (basisVec i) * w (y, τ) =
          ∫ y in K1,
            PDE.Parabolic.Energy.kern a' (x - y) * D (y, τ) i := by
    exact ae_restrict_of_ae_restrict_of_subset
      (Ioc_subset_Ioc le_rfl htT) hWgFull
  have hζK : ∀ x, x ∉ K → ζ x = 0 := by
    intro x hx
    exact image_eq_zero_of_notMem_tsupport hx
  have hDcoord : ∀ i : Fin d, Measurable (fun z => D z i) := by
    have h := hDm
    rw [measurable_pi_iff] at h
    exact h
  have hGcoord : ∀ i : Fin d, Measurable (fun z => G z i) := by
    have h := hGm
    rw [measurable_pi_iff] at h
    exact h
  let E : PDE.Parabolic.Energy.Data d := {
    K := K
    hK := hK
    δ0 := 1
    hδ0 := one_pos
    hδ1 := le_rfl
    s := s
    t := t
    hst := hst
    u := w
    Du := D
    G := G
    φ := χ.toFun
    hφ := χ.contDiff
    hφK := by
      intro x τ hτ hx hnotK
      change (1 : ℝ) * ζ x = 0
      rw [hζK x hnotK]
      ring
    hDum := hDcoord
    hGm := hGcoord
    hu2 := hwmem'.mono_measure hmeasureLe
    hDu2 := fun i => (hDmem' i).mono_measure hmeasureLe
    hG2 := fun i => (hGmem i).mono_measure hmeasureLe
    hus := by
      intro τ hτ
      exact hloc τ ⟨hτ.1, hτ.2.trans htT⟩ K1 hK1
    hwg := hWg
    hslice := hsl }
  refine ⟨E, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change w =ᵐ[slabMeasure d s T]
      PDE.Parabolic.Energy.mollT ε univ (cauchyEnergyValue u)
    exact hwae
  · intro i
    filter_upwards [hDae i] with z hz
    exact hz
  · intro i
    filter_upwards [hGae i] with z hz
    exact hz
  · simpa only [E] using hwcont
  · simpa only [E] using hwsec
  · simpa only [E] using hinit

end PDE.Parabolic.Lions
