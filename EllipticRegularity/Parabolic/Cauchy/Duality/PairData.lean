module

public import EllipticRegularity.Parabolic.Energy.Bridge

@[expose] public section

namespace PDE.Parabolic.Duality

open MeasureTheory Set
open Metric
open PDE.Parabolic.Energy

/-- Bundle a weak solution into the abstract whole-space energy data using a prescribed compact
spatial collar. Fixing the collar lets us add data from two different weak evolutions. -/
theorem cauchy_solution_energy_data_fixed_collar {d : ℕ} {lam Lam : ℝ}
    {I : Set ℝ} {a : ParCoeffField d} (hI : I.OrdConnected)
    (ha : IsParabolicCoeff lam Lam a (univ : Set (Vec d)) I)
    (u : ParH1Function (univ : Set (Vec d)) I)
    (hu : IsParabolicWeakSolution a univ I u)
    {K : Set (Vec d)} (hK : IsCompact K)
    {δ0 s t : ℝ} (hδ0 : 0 < δ0) (hδ1 : δ0 ≤ 1)
    (hs : s ∈ I) (ht : t ∈ I) (hst : s < t)
    (φ : Vec d × ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hφK : ∀ x τ, τ ∈ Icc s t → x ∈ cthickening (2 * δ0) K →
      x ∉ K → φ (x, τ) = 0) :
    ∃ D : Energy.Data d, D.K = K ∧ D.δ0 = δ0 ∧ D.s = s ∧ D.t = t ∧
      D.u = u.toFun ∧ D.φ = φ ∧
      ∀ᵐ z ∂(volume.restrict ((univ : Set (Vec d)) ×ˢ I)),
        D.Du z = u.grad z ∧ D.G z = flux a u z := by
  have hK1c : IsCompact (cthickening δ0 K) := hK.cthickening
  have hK1m : MeasurableSet (cthickening δ0 K) := hK1c.measurableSet
  have hIcc : Icc s t ⊆ I := hI.out hs ht
  let Q : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ I
  let K1 : Set (Vec d) := cthickening δ0 K
  have hslab : K1 ×ˢ Ioc s t ⊆ (univ : Set (Vec d)) ×ˢ I :=
    prod_mono (subset_univ _) (Ioc_subset_Icc_self.trans hIcc)
  have hle : volume.restrict (K1 ×ˢ Ioc s t) ≤
      volume.restrict ((univ : Set (Vec d)) ×ˢ I) :=
    Measure.restrict_mono hslab le_rfl
  have hDuM : ∀ i : Fin d, AEStronglyMeasurable (fun z => u.grad z i)
      (volume.restrict ((univ : Set (Vec d)) ×ˢ I)) :=
    fun i => (u.gradMemL2 i).aestronglyMeasurable
  have hGMem : ∀ i : Fin d, MemLp (fun z => flux a u z i)
      2 (volume.restrict ((univ : Set (Vec d)) ×ˢ I)) :=
    fun i => flux_memLp ha u i
  have hGM : ∀ i : Fin d, AEStronglyMeasurable (fun z => flux a u z i)
      (volume.restrict ((univ : Set (Vec d)) ×ˢ I)) :=
    fun i => (hGMem i).aestronglyMeasurable
  let Du : Vec d × ℝ → Vec d := fun z i => (hDuM i).mk (fun z => u.grad z i) z
  let G : Vec d × ℝ → Vec d := fun z i => (hGM i).mk (fun z => flux a u z i) z
  have hDuAE : ∀ᵐ z ∂(volume.restrict ((univ : Set (Vec d)) ×ˢ I)),
      ∀ i, Du z i = u.grad z i := by
    rw [ae_all_iff]
    intro i
    exact (hDuM i).ae_eq_mk.mono fun z hz => hz.symm
  have hGAE : ∀ᵐ z ∂(volume.restrict ((univ : Set (Vec d)) ×ˢ I)),
      ∀ i, G z i = flux a u z i := by
    rw [ae_all_iff]
    intro i
    exact (hGM i).ae_eq_mk.mono fun z hz => hz.symm
  have hDuAESlab : ∀ᵐ z ∂(volume.restrict (K1 ×ˢ Ioc s t)),
      ∀ i, Du z i = u.grad z i :=
    (ae_restrict_of_ae_restrict_of_subset hslab hDuAE)
  have hGAESlab : ∀ᵐ z ∂(volume.restrict (K1 ×ˢ Ioc s t)),
      ∀ i, G z i = flux a u z i :=
    (ae_restrict_of_ae_restrict_of_subset hslab hGAE)
  have hIoc : Ioc s t ⊆ I := Ioc_subset_Icc_self.trans hIcc
  have hDuProd : ∀ᵐ z ∂((volume.restrict (univ : Set (Vec d))).prod
      (volume.restrict I)), ∀ i, Du z i = u.grad z i := by
    rw [← PDE.Parabolic.Energy.volume_restrict_prod]
    exact hDuAE
  have hDuSlice : ∀ᵐ τ ∂(volume.restrict (Ioc s t)), ∀ i,
      (fun y => Du (y, τ) i) =ᵐ[volume.restrict (univ : Set (Vec d))]
        fun y => u.grad (y, τ) i := by
    have h := ae_restrict_of_ae_restrict_of_subset hIoc (ae_ae_swap hDuProd)
    filter_upwards [h] with τ hτ i
    exact hτ.mono fun y hy => hy i
  have hK1U' : K1 ⊆ (univ : Set (Vec d)) := subset_univ _
  have hus : ∀ τ ∈ Icc s t,
      MemLp (fun y => u.toFun (y, τ)) 2 (volume.restrict K1) := by
    intro τ hτ
    exact u.sliceL2loc τ (hIcc hτ) K1 hK1c hK1U'
  have hwg : ∀ᵐ τ ∂(volume.restrict (Ioc s t)), ∀ a' : ℝ, 0 < a' → a' ≤ δ0 →
      ∀ x ∈ K, ∀ i,
        ∫ y in K1, fderiv ℝ (kern a') (x - y) (basisVec i) * u.toFun (y, τ) =
          ∫ y in K1, kern a' (x - y) * Du (y, τ) i := by
    filter_upwards
      [ae_restrict_of_ae_restrict_of_subset hIoc u.sliceWeakGradient, hDuSlice]
      with τ hweak hdu a' ha' haδ x hx i
    exact weakGrad_identity (U := (univ : Set (Vec d))) isOpen_univ u hK1m hK1U'
      ha' (x := x)
      ((closedBall_subset_cthickening hx a').trans (cthickening_mono haδ K))
      (τ := τ) hweak hdu i
  have hslice : ∀ a' : ℝ, 0 < a' → a' ≤ δ0 → ∀ x ∈ K,
      ∀ τ1 τ2 : ℝ, s ≤ τ1 → τ1 ≤ τ2 → τ2 ≤ t →
        (∫ y in K1, kern a' (x - y) * u.toFun (y, τ2)) -
            (∫ y in K1, kern a' (x - y) * u.toFun (y, τ1)) =
          ∫ z in K1 ×ˢ Ioc τ1 τ2,
            ∑ i, G z i * fderiv ℝ (kern a') (x - z.1) (basisVec i) := by
    intro a' ha' haδ x hx τ1 τ2 h1 h12 h2
    have ht1 : τ1 ∈ I := hIcc ⟨h1, h12.trans h2⟩
    have ht2 : τ2 ∈ I := hIcc ⟨h1.trans h12, h2⟩
    exact slice_identity_aux (U := (univ : Set (Vec d))) isOpen_univ hI ha u hu
      hK1m hK1U' ha' (x := x)
      ((closedBall_subset_cthickening hx a').trans (cthickening_mono haδ K))
      ht1 ht2 h12 hGAE
  have hDuVec : ∀ᵐ z ∂(volume.restrict ((univ : Set (Vec d)) ×ˢ I)),
      Du z = u.grad z := by
    filter_upwards [hDuAE] with z hz
    ext i
    exact hz i
  have hGVec : ∀ᵐ z ∂(volume.restrict ((univ : Set (Vec d)) ×ˢ I)),
      G z = flux a u z := by
    filter_upwards [hGAE] with z hz
    ext i
    exact hz i
  refine ⟨⟨K, hK, δ0, hδ0, hδ1, s, t, hst, u.toFun, Du, G, φ, hφ, hφK,
    (fun i => ((hDuM i).stronglyMeasurable_mk).measurable),
    (fun i => ((hGM i).stronglyMeasurable_mk).measurable),
    u.memL2.mono_measure hle,
    (fun i => ((u.gradMemL2 i).mono_measure hle).ae_eq
      (hDuAESlab.mono fun z hz => (hz i).symm)),
    (fun i => ((hGMem i).mono_measure hle).ae_eq
      (hGAESlab.mono fun z hz => (hz i).symm)),
    hus, hwg, hslice⟩, rfl, rfl, rfl, rfl, rfl, rfl,
    ?_⟩
  filter_upwards [hDuVec, hGVec] with z hdu hflux
  exact ⟨hdu, hflux⟩

end PDE.Parabolic.Duality
