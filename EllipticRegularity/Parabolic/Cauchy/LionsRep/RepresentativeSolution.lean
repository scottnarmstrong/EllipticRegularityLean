module

public import EllipticRegularity.Parabolic.Cauchy.Lions.ClosureData
public import EllipticRegularity.Parabolic.Cauchy.LionsRep.RepresentativeProperties
public import PDEFoundation.Sobolev.WeakDerivative.Congruence

/-! # Assemble the Lions fields into a weak Cauchy solution -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set Filter

namespace PDE.Parabolic.LionsRep

private theorem cauchyEnergyGradient_ae_sliceMemLp
    {d : ℕ} {s T : ℝ} (u : PDE.Parabolic.Lions.CauchyX d s T) (i : Fin d) :
    ∀ᵐ t ∂(volume.restrict (Icc s T)),
      MemLp (fun x : Vec d => PDE.Parabolic.Lions.cauchyEnergyGradient u (x, t) i)
        2 (volume : Measure (Vec d)) := by
  have h := PDE.Parabolic.Energy.ae_slice_memLp (d := d)
    (K1 := (univ : Set (Vec d))) (J := Icc s T)
    (g := fun z => PDE.Parabolic.Lions.cauchyEnergyGradient u z i)
    MeasurableSet.univ (PDE.Parabolic.Lions.cauchyEnergyGradient_coord_memLp u i)
  filter_upwards [h] with t ht
  simpa using ht

theorem exists_cauchy_energy_representative
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T) {u₀ : PDE.Parabolic.Lions.CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (hglobalSliceBound : PDE.Parabolic.Lions.CauchyGlobalSliceBound
      (a := a) f u) :
    ∃ W : ParH1Function (univ : Set (Vec d)) (Icc s T),
      W.toFun =ᵐ[PDE.Parabolic.Lions.slabMeasure d s T]
        PDE.Parabolic.Lions.cauchyEnergyValue u ∧
      ∀ i : Fin d, (fun z => W.grad z i) =ᵐ[PDE.Parabolic.Lions.slabMeasure d s T]
        (fun z => PDE.Parabolic.Lions.cauchyEnergyGradient u z i) := by
  let R : Vec d × ℝ → ℝ :=
    cauchyRieszSliceRepresentative hsT ha f hf u hclose hrep
  have hWae := cauchyRieszSliceRepresentative_ae_eq_energyValue
    hsT ha f hf u hclose hrep hglobalSliceBound
  have hweak := PDE.Parabolic.Lions.cauchyClosure_ae_energySliceWeakGradient hclose
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
  have hWprod : R =ᵐ[(volume : Measure (Vec d)).prod
      (volume.restrict (Icc s T))] PDE.Parabolic.Lions.cauchyEnergyValue u := by
    rw [hmeasure]
    simpa [R] using hWae
  have hWslice : ∀ᵐ t ∂(volume.restrict (Icc s T)),
      (fun x : Vec d => R (x, t)) =ᵐ[volume]
        (fun x => PDE.Parabolic.Lions.cauchyEnergyValue u (x, t)) :=
    PDE.Parabolic.Energy.ae_ae_swap hWprod
  have hweakR : ∀ᵐ t ∂(volume.restrict (Icc s T)),
      HasWeakGradientOn (univ : Set (Vec d))
        (fun x => R (x, t))
        (fun x => PDE.Parabolic.Lions.cauchyEnergyGradient u (x, t)) := by
    have hrawSlice : ∀ᵐ t ∂(volume.restrict (Icc s T)),
        MemLp (fun x : Vec d => PDE.Parabolic.Lions.cauchyEnergyValue u (x, t))
          2 (volume : Measure (Vec d)) := by
      filter_upwards [hglobalSliceBound] with t ht
      exact ht.1
    have hrepSlice : ∀ t ∈ Icc s T,
        MemLp (fun x : Vec d => R (x, t)) 2 (volume : Measure (Vec d)) := by
      intro t ht
      exact cauchyRieszSliceRepresentative_slice_memLp
        hsT ha f hf u hclose hrep ⟨t, ht⟩
    have hgradAll : ∀ᵐ t ∂(volume.restrict (Icc s T)), ∀ i : Fin d,
        MemLp (fun x : Vec d => PDE.Parabolic.Lions.cauchyEnergyGradient u (x, t) i)
          2 (volume : Measure (Vec d)) := by
      exact ae_all_iff.mpr fun i => cauchyEnergyGradient_ae_sliceMemLp u i
    filter_upwards [hweak, hWslice, hrawSlice,
      hgradAll, ae_restrict_mem measurableSet_Icc]
      with t hw hval hraw hgrad ht
    intro i
    have hRloc : LocallyIntegrableOn (fun x : Vec d => R (x, t))
        (univ : Set (Vec d)) volume :=
      ((hrepSlice t ht).locallyIntegrable (by norm_num)).locallyIntegrableOn univ
    have hrawLoc : LocallyIntegrableOn
        (fun x : Vec d => PDE.Parabolic.Lions.cauchyEnergyValue u (x, t))
        (univ : Set (Vec d)) volume :=
      (hraw.locallyIntegrable (by norm_num)).locallyIntegrableOn univ
    have hgradLoc : LocallyIntegrableOn
        (fun x : Vec d => PDE.Parabolic.Lions.cauchyEnergyGradient u (x, t) i)
        (univ : Set (Vec d)) volume :=
      ((hgrad i).locallyIntegrable (by norm_num)).locallyIntegrableOn univ
    have hval' : (fun x : Vec d => R (x, t)) =ᵐ[volumeOn (univ : Set (Vec d))]
        (fun x => PDE.Parabolic.Lions.cauchyEnergyValue u (x, t)) := by
      simpa [PDE.volumeOn] using hval
    exact PDE.HasWeakPartialDerivOn.congr_value_ae
      (hw i) MeasurableSet.univ hrawLoc hRloc hgradLoc hval'.symm
  let W : ParH1Function (univ : Set (Vec d)) (Icc s T) := {
    toFun := R
    grad := PDE.Parabolic.Lions.cauchyEnergyGradient u
    memL2 := by
      have h := (memLp_congr_ae hWae).mpr
        (PDE.Parabolic.Lions.cauchyEnergyValue_memLp u)
      simpa [PDE.Parabolic.Lions.slabMeasure] using h
    gradMemL2 := by
      intro i
      exact PDE.Parabolic.Lions.cauchyEnergyGradient_coord_memLp u i
    sliceWeakGradient := hweakR
    sliceL2loc := by
      intro t ht K hK hKU
      have h := cauchyRieszSliceRepresentative_slice_memLp
        hsT ha f hf u hclose hrep ⟨t, ht⟩
      change MemLp (fun x : Vec d => R (x, t)) 2 (volume.restrict K)
      exact h.mono_measure Measure.restrict_le_self
    weakCont := by
      intro ψ hψ
      simpa [R] using cauchyRieszSliceRepresentative_pairing_continuousOn
        hsT ha f hf u hclose hrep ψ hψ
  }
  refine ⟨W, ?_, ?_⟩
  · simpa [W, R] using hWae
  · intro i
    exact Filter.Eventually.of_forall fun _ => rfl

theorem exists_cauchy_energy_solution_of_globalSliceBound
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T) {u₀ : PDE.Parabolic.Lions.CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (hglobalSliceBound : PDE.Parabolic.Lions.CauchyGlobalSliceBound
      (a := a) f u) :
    ∃ W : ParH1Function (univ : Set (Vec d)) (Icc s T),
      PDE.IsCauchySolution a s T f W := by
  obtain ⟨W, hWae, hGae⟩ := exists_cauchy_energy_representative
    hsT ha f hf u hclose hrep hglobalSliceBound
  exact ⟨W, PDE.Parabolic.Lions.cauchyEnergyRepresentative_isCauchySolution
    hsT ha f hf u hclose hrep W hWae hGae⟩

end PDE.Parabolic.LionsRep
