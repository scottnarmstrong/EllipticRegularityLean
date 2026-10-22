module

public import EllipticRegularity.Parabolic.Cauchy.Lions.ClosureData
public import EllipticRegularity.Parabolic.Cauchy.Lions.MollifiedWeakGradient
public import EllipticRegularity.Parabolic.Cauchy.Lions.MollifiedSliceLp
public import EllipticRegularity.Parabolic.Cauchy.Lions.MollifiedLp

/-! # Measurable representatives for mollified Lions energy fields -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace PDE.Parabolic.Lions

private theorem weakGradient_univ_congr_ae {d : ℕ} {v w : Vec d → ℝ}
    {G H : Vec d → Vec d} (hv : v =ᵐ[volume] w)
    (hG : ∀ i : Fin d, (fun x => G x i) =ᵐ[volume] fun x => H x i)
    (hweak : HasWeakGradientOn (univ : Set (Vec d)) v G) :
    HasWeakGradientOn univ w H := by
  intro i φ hφ hφc hφU
  have hweak' := hweak i φ hφ hφc hφU
  have hweak'' :
      ∫ x, v x * (fderiv ℝ φ x) (basisVec i) = -∫ x, G x i * φ x := by
    simpa only [setIntegral_univ] using hweak'
  have hright : ∫ x, G x i * φ x = ∫ x, H x i * φ x := by
    apply integral_congr_ae
    filter_upwards [hG i] with x hx
    rw [hx]
  have hresult :
      ∫ x, w x * (fderiv ℝ φ x) (basisVec i) = -∫ x, H x i * φ x := calc
    ∫ x, w x * (fderiv ℝ φ x) (basisVec i) =
        ∫ x, v x * (fderiv ℝ φ x) (basisVec i) := by
          apply integral_congr_ae
          filter_upwards [hv] with x hx
          rw [hx]
    _ = -∫ x, G x i * φ x := hweak''
    _ = -∫ x, H x i * φ x := by rw [hright]
  simpa only [setIntegral_univ] using hresult

private theorem cauchyEnergyGradient_coord_stronglyMeasurable {d : ℕ} {s T : ℝ}
    (u : CauchyX d s T) (i : Fin d) :
    StronglyMeasurable (fun z => cauchyEnergyGradient u z i) := by
  let L : WithLp 2 (ℝ × HilbertVec d) →L[ℝ] ℝ :=
    (PiLp.proj 2 (fun _ : Fin d => ℝ) i).comp
      (WithLp.sndL 2 ℝ ℝ (HilbertVec d))
  have hbase : StronglyMeasurable (fun z => L (u z)) :=
    L.continuous.comp_stronglyMeasurable (Lp.stronglyMeasurable u)
  have hw : StronglyMeasurable
      (fun z : Vec d × ℝ => cauchyWeight (s := s) z) :=
    Real.continuous_exp.comp_stronglyMeasurable
      (continuous_snd.sub continuous_const).stronglyMeasurable
  change StronglyMeasurable (fun z => cauchyWeight (s := s) z * L (u z))
  exact hw.mul hbase

/-- A chosen jointly measurable representative of the spatial mollification, together with
measurable representatives of its mollified gradient and coefficient flux. The value representative
has continuous time sections and `L²_loc` slices at every time; all three fields retain global
space-time `L²` bounds. The weak gradient identity is transferred to the chosen value field for
almost every time. -/
theorem exists_cauchy_mollified_energy_representatives
    {d : ℕ} {lam Lam s T ε : ℝ} {A : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam A univ (Icc s T))
    (hε : 0 < ε) (f : Vec d → ℝ) (hf : MemLp f 2 (volume : Measure (Vec d)))
    (u : CauchyX d s T) {u₀ : CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u) :
    ∃ w : Vec d × ℝ → ℝ, ∃ D G : Vec d × ℝ → Vec d,
      Measurable w ∧ Measurable D ∧ Measurable G ∧
      (∀ x, ContinuousOn (fun t => w (x, t)) (Icc s T)) ∧
      (∀ x, (fun t => PDE.Parabolic.Energy.mollT ε univ
        (cauchyEnergyValue u) (x, t)) =ᵐ[volume.restrict (Icc s T)]
          (fun t => w (x, t))) ∧
      (∀ t ∈ Icc s T, ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun x => w (x, t)) 2 (volume.restrict K)) ∧
      MemLp w 2 (slabMeasure d s T) ∧
      (∀ i : Fin d, MemLp (fun z => D z i) 2 (slabMeasure d s T)) ∧
      (∀ i : Fin d, MemLp (fun z => G z i) 2 (slabMeasure d s T)) ∧
      (∀ᵐ z ∂(slabMeasure d s T),
        w z = PDE.Parabolic.Energy.mollT ε univ (cauchyEnergyValue u) z) ∧
      (∀ i, ∀ᵐ z ∂(slabMeasure d s T),
        D z i = PDE.Parabolic.Energy.mollT ε univ
          (fun z => cauchyEnergyGradient u z i) z) ∧
      (∀ i, ∀ᵐ z ∂(slabMeasure d s T),
        G z i = PDE.Parabolic.Energy.mollT ε univ
          (fun z => matVecMul (A z) (cauchyEnergyGradient u z) i) z) ∧
      (∀ᵐ t ∂(volume.restrict (Icc s T)),
        HasWeakGradientOn (univ : Set (Vec d))
          (fun x => w (x, t)) (fun x i => D (x, t) i)) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ x : Vec d, ∀ t ∈ Icc s T, |w (x, t)| ≤ B := by
  obtain ⟨w, hwm, hwcont, hwsec, hwae, hloc, hB⟩ :=
    exists_cauchy_mollified_alltime_sliceL2loc hsT ha hε f hf u hrep
  let D : Vec d × ℝ → Vec d := fun z i => PDE.Parabolic.Energy.mollT ε univ
    (fun q => cauchyEnergyGradient u q i) z
  let flux : Fin d → Vec d × ℝ → ℝ := fun i z =>
    matVecMul (A z) (cauchyEnergyGradient u z) i
  let G : Vec d × ℝ → Vec d := fun z i =>
    PDE.Parabolic.Energy.mollT ε univ
      ((cauchyEnergyFlux_coord_memLp ha u i).aestronglyMeasurable.mk (flux i)) z
  have hDmeas : Measurable D := by
    rw [measurable_pi_iff]
    intro i
    exact (PDE.Parabolic.Energy.stronglyMeasurable_mollT MeasurableSet.univ
      (cauchyEnergyGradient_coord_stronglyMeasurable u i).measurable ε).measurable
  have hGmeas : Measurable G := by
    rw [measurable_pi_iff]
    intro i
    exact (PDE.Parabolic.Energy.stronglyMeasurable_mollT MeasurableSet.univ
      ((cauchyEnergyFlux_coord_memLp ha u i).aestronglyMeasurable.stronglyMeasurable_mk).measurable
      ε).measurable
  have hGinput (i : Fin d) : MemLp
      ((cauchyEnergyFlux_coord_memLp ha u i).aestronglyMeasurable.mk (flux i)) 2
        (slabMeasure d s T) := by
    exact (cauchyEnergyFlux_coord_memLp ha u i).ae_eq
      (cauchyEnergyFlux_coord_memLp ha u i).aestronglyMeasurable.ae_eq_mk
  have hDmem : ∀ i : Fin d, MemLp (fun z => D z i) 2 (slabMeasure d s T) := by
    intro i
    dsimp [D]
    exact (cauchyMollT_memLp hε (cauchyEnergyGradient_coord_memLp u i)).1
  have hGmem : ∀ i : Fin d, MemLp (fun z => G z i) 2 (slabMeasure d s T) := by
    intro i
    dsimp [G, flux]
    exact (cauchyMollT_memLp hε (hGinput i)).1
  have hWmem : MemLp w 2 (slabMeasure d s T) := by
    have hmoll : MemLp (PDE.Parabolic.Energy.mollT ε univ
        (cauchyEnergyValue u)) 2 (slabMeasure d s T) :=
      (cauchyMollT_memLp hε (cauchyEnergyValue_memLp u)).1
    have hWae : w =ᵐ[slabMeasure d s T]
        PDE.Parabolic.Energy.mollT ε univ (cauchyEnergyValue u) := hwae
    exact hmoll.ae_eq hWae.symm
  have hDae : ∀ i : Fin d, ∀ᵐ z ∂(slabMeasure d s T),
      D z i = PDE.Parabolic.Energy.mollT ε univ
        (fun z => cauchyEnergyGradient u z i) z := by
    intro i
    exact Filter.Eventually.of_forall fun z => rfl
  have hGae : ∀ i : Fin d, ∀ᵐ z ∂(slabMeasure d s T),
      G z i = PDE.Parabolic.Energy.mollT ε univ (flux i) z := by
    intro i
    have hslice := PDE.Parabolic.Energy.mollT_ae_slice MeasurableSet.univ
      (J := Icc s T)
      (cauchyEnergyFlux_coord_memLp ha u i).aestronglyMeasurable.ae_eq_mk ε
    have hprod := PDE.Parabolic.Energy.ae_prod_of_ae_slice
      (μ := (volume : Measure (Vec d)))
      (ν := volume.restrict (Icc s T))
      (P := fun x t => PDE.Parabolic.Energy.mollT ε univ (flux i) (x, t) =
        PDE.Parabolic.Energy.mollT ε univ
          ((cauchyEnergyFlux_coord_memLp ha u i).aestronglyMeasurable.mk (flux i)) (x, t))
      hslice
    have hmeasure : (volume : Measure (Vec d)).prod
        (volume.restrict (Icc s T)) = slabMeasure d s T := by
      change (volume : Measure (Vec d)).prod (volume.restrict (Icc s T)) =
        (volume : Measure (Vec d × ℝ)).restrict (univ ×ˢ Icc s T)
      calc
        _ = (volume.restrict (univ : Set (Vec d))).prod
            (volume.restrict (Icc s T)) := by simp
        _ = (volume : Measure (Vec d × ℝ)).restrict (univ ×ˢ Icc s T) :=
          (PDE.Parabolic.Energy.volume_restrict_prod univ (Icc s T)).symm
    have hprod' : ∀ᵐ z ∂(slabMeasure d s T),
        PDE.Parabolic.Energy.mollT ε univ (flux i) z =
          PDE.Parabolic.Energy.mollT ε univ
            ((cauchyEnergyFlux_coord_memLp ha u i).aestronglyMeasurable.mk (flux i)) z := by
      rw [ae_iff] at hprod ⊢
      rw [hmeasure] at hprod
      simpa using hprod
    filter_upwards [hprod'] with z hz
    exact hz.symm
  have hWgrad : ∀ᵐ t ∂(volume.restrict (Icc s T)),
      HasWeakGradientOn (univ : Set (Vec d))
        (fun x => w (x, t)) (fun x i => D (x, t) i) := by
    have hraw := cauchyMollified_ae_sliceWeakGradient hε hclose
    have hWprod : ∀ᵐ z ∂((volume : Measure (Vec d)).prod
        (volume.restrict (Icc s T))),
        w z = PDE.Parabolic.Energy.mollT ε univ (cauchyEnergyValue u) z := by
      have hmeasure : (volume : Measure (Vec d)).prod
          (volume.restrict (Icc s T)) = slabMeasure d s T := by
        change (volume : Measure (Vec d)).prod (volume.restrict (Icc s T)) =
          (volume : Measure (Vec d × ℝ)).restrict (univ ×ˢ Icc s T)
        calc
          _ = (volume.restrict (univ : Set (Vec d))).prod
              (volume.restrict (Icc s T)) := by simp
          _ = (volume : Measure (Vec d × ℝ)).restrict (univ ×ˢ Icc s T) :=
            (PDE.Parabolic.Energy.volume_restrict_prod univ (Icc s T)).symm
      have hwae' := hwae
      rw [← hmeasure] at hwae'
      exact hwae'
    have hWtimes := PDE.Parabolic.Energy.ae_ae_swap hWprod
    filter_upwards [hraw, hWtimes] with t hrt hwt
    have hwtEq : (fun x => PDE.Parabolic.Energy.mollT ε univ
        (cauchyEnergyValue u) (x, t)) =ᵐ[volume] (fun x => w (x, t)) := by
      filter_upwards [hwt] with x hx
      exact hx.symm
    apply weakGradient_univ_congr_ae hwtEq
    · intro i
      exact Filter.Eventually.of_forall fun x => rfl
    · exact hrt
  refine ⟨w, D, G, hwm, hDmeas, hGmeas, hwcont, hwsec, hloc, hWmem, hDmem, hGmem,
    hwae, hDae, hGae, hWgrad, hB⟩

end PDE.Parabolic.Lions
