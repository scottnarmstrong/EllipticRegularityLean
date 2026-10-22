module

public import EllipticRegularity.Parabolic.Energy.Limit
public import EllipticRegularity.Parabolic.Energy.TestFunction
public import EllipticRegularity.Parabolic.WeakSlice.Result

/-!
# From `H¹_par` weak solutions to the abstract data
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.Energy

open MeasureTheory Set Filter Topology Metric PDE PDE.Parabolic.WeakSlice

section Bridge

variable {d : ℕ} {lam Lam : ℝ} {U : Set (Vec d)} {I : Set ℝ} {a : ParCoeffField d}

/-- The flux `a ∇u`. -/
noncomputable def flux (a : ParCoeffField d) {U : Set (Vec d)} {I : Set ℝ}
    (u : ParH1Function U I) (z : Vec d × ℝ) : Vec d :=
  matVecMul (a z) (u.grad z)

theorem flux_apply (u : ParH1Function U I) (z : Vec d × ℝ) (i : Fin d) :
    flux a u z i = ∑ j, a z i j * u.grad z j := by
  simp [flux, matVecMul]

theorem flux_memLp (ha : IsParabolicCoeff lam Lam a U I) (u : ParH1Function U I) (i : Fin d) :
    MemLp (fun z => flux a u z i) 2 (volume.restrict (U ×ˢ I)) := by
  simp only [flux_apply]
  refine memLp_finsetSum _ fun j _ => ?_
  refine (u.gradMemL2 j).of_le_mul (c := Lam) ?_ ?_
  · exact (ha.measurable i j).aestronglyMeasurable.mul (u.gradMemL2 j).aestronglyMeasurable
  · filter_upwards [ha.elliptic] with z hz
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (matrix_abs_entry_le hz i j) (abs_nonneg _)

/-- A compact set carrying the cutoff, and a collar inside `U`. -/
theorem exists_collar (hU : IsOpen U) (φ : ParCutoff U I) :
    ∃ (K : Set (Vec d)) (δ0 : ℝ), IsCompact K ∧ K ⊆ U ∧ 0 < δ0 ∧ δ0 ≤ 1 ∧
      cthickening (2 * δ0) K ⊆ U ∧ ∀ x ∈ U, x ∉ K → ∀ τ ∈ I, φ.toFun (x, τ) = 0 := by
  obtain ⟨Z, hZc, hZsub, hZ0⟩ := φ.compact_support
  have hKc : IsCompact (Prod.fst '' Z) := hZc.image continuous_fst
  have hKU : Prod.fst '' Z ⊆ U := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hZsub hz).1
  obtain ⟨δ, hδ, hsub⟩ := hKc.exists_cthickening_subset_open hU hKU
  refine ⟨Prod.fst '' Z, min 1 (δ / 2), hKc, hKU, lt_min one_pos (half_pos hδ), min_le_left _ _,
    (cthickening_mono ?_ _).trans hsub, ?_⟩
  · have := min_le_right (1 : ℝ) (δ / 2)
    linarith
  · intro x hx hxK τ hτ
    refine hZ0 (x, τ) ⟨hx, hτ⟩ ?_
    intro hz
    exact hxK ⟨(x, τ), hz, rfl⟩

theorem lt_norm_of_notMem_closedBall {a' : ℝ} {x y : Vec d} (hy : y ∉ closedBall x a') :
    a' < ‖x - y‖ := by
  rw [mem_closedBall, dist_eq_norm, not_le] at hy
  rwa [← norm_neg, neg_sub]

theorem zeta_tsupport_subset_U {a' : ℝ} (ha' : 0 < a') {x : Vec d} {K1 : Set (Vec d)}
    (hball : closedBall x a' ⊆ K1) (hK1U : K1 ⊆ U) : tsupport (zeta a' x) ⊆ U :=
  (zeta_tsupport_subset ha' x).trans (hball.trans hK1U)

theorem setIntegral_pairing {a' : ℝ} (ha' : 0 < a') {x : Vec d} {K1 : Set (Vec d)}
    (hball : closedBall x a' ⊆ K1) (hU : IsOpen U) (hK1m : MeasurableSet K1) (hK1U : K1 ⊆ U)
    (f : Vec d → ℝ) :
    ∫ y in U, f y * zeta a' x y = ∫ y in K1, kern a' (x - y) * f y := by
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hK1U]
  · refine setIntegral_congr_fun hK1m fun y _ => ?_
    simp only [zeta]
    ring
  · intro y hy
    have : y ∉ closedBall x a' := fun h => hy.2 (hball h)
    simp [zeta_eq_zero ha' this]

theorem vecDot_flux_zeta (u : ParH1Function U I) (a' : ℝ) (x : Vec d) (z : Vec d × ℝ) :
    vecDot (matVecMul (a z) (u.grad z)) (spaceGradC1 (zeta a' x) z.1) =
      -∑ i, flux a u z i * fderiv ℝ (kern a') (x - z.1) (basisVec i) := by
  simp only [vecDot, spaceGradC1, fderiv_zeta, flux, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The mollified weak time-slice identity, in the form required by `Data`. -/
theorem slice_identity_aux (hU : IsOpen U) (hI : I.OrdConnected)
    (ha : IsParabolicCoeff lam Lam a U I) (u : ParH1Function U I)
    (hu : IsParabolicWeakSolution a U I u) {K1 : Set (Vec d)} (hK1m : MeasurableSet K1)
    (hK1U : K1 ⊆ U) {a' : ℝ} (ha' : 0 < a') {x : Vec d} (hball : closedBall x a' ⊆ K1)
    {τ1 τ2 : ℝ} (h1 : τ1 ∈ I) (h2 : τ2 ∈ I) (h12 : τ1 ≤ τ2) {G : Vec d × ℝ → Vec d}
    (hG : ∀ᵐ z ∂(volume.restrict (U ×ˢ I)), ∀ i, G z i = flux a u z i) :
    (∫ y in K1, kern a' (x - y) * u.toFun (y, τ2)) -
        (∫ y in K1, kern a' (x - y) * u.toFun (y, τ1)) =
      ∫ z in K1 ×ˢ Ioc τ1 τ2, ∑ i, G z i * fderiv ℝ (kern a') (x - z.1) (basisVec i) := by
  rcases h12.eq_or_lt with rfl | hlt
  · simp
  · obtain ⟨_, hws⟩ := PDE.Parabolic.weak_slice d lam Lam U hU I hI a ha u hu (zeta a' x)
      (zeta_contDiff_one a' x) (zeta_hasCompactSupport ha' x)
      (zeta_tsupport_subset_U ha' hball hK1U) τ1 τ2 h1 h2 hlt
    rw [setIntegral_pairing ha' hball hU hK1m hK1U (fun y => u.toFun (y, τ2)),
      setIntegral_pairing ha' hball hU hK1m hK1U (fun y => u.toFun (y, τ1))] at hws
    rw [hws]
    simp only [vecDot_flux_zeta]
    rw [integral_neg, neg_neg]
    have hsub : K1 ×ˢ Ioc τ1 τ2 ⊆ U ×ˢ Ioc τ1 τ2 := prod_mono hK1U subset_rfl
    rw [← setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hU.measurableSet.prod measurableSet_Ioc)
      hsub]
    · have hsubI : U ×ˢ Ioc τ1 τ2 ⊆ U ×ˢ I :=
        prod_mono subset_rfl (fun τ hτ => hI.out h1 h2 ⟨hτ.1.le, hτ.2⟩)
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hsubI hG] with z hz
      exact Finset.sum_congr rfl fun i _ => by rw [hz i]
    · rintro ⟨y, τ⟩ ⟨hyU, hn⟩
      have hyK : y ∉ K1 := fun hy => hn ⟨hy, hyU.2⟩
      have hy : y ∉ closedBall x a' := fun h => hyK (hball h)
      have hnorm : a' < ‖x - y‖ := by
        rw [mem_closedBall, dist_eq_norm, not_le] at hy
        rwa [← norm_neg, neg_sub]
      simp [fderiv_kern_eq_zero_of_lt_norm ha' hnorm]

/-- The mollified weak-gradient identity for one slice. -/
theorem weakGrad_identity (hU : IsOpen U) (u : ParH1Function U I) {K1 : Set (Vec d)}
    (hK1m : MeasurableSet K1) (hK1U : K1 ⊆ U) {a' : ℝ} (ha' : 0 < a') {x : Vec d}
    (hball : closedBall x a' ⊆ K1) {τ : ℝ}
    (hτ : HasWeakGradientOn U (parSlice u.toFun τ) (parSlice u.grad τ))
    {Du : Vec d × ℝ → Vec d} (hDu : ∀ i, (fun y => Du (y, τ) i) =ᵐ[volume.restrict U]
      fun y => u.grad (y, τ) i) (i : Fin d) :
    ∫ y in K1, fderiv ℝ (kern a') (x - y) (basisVec i) * u.toFun (y, τ) =
      ∫ y in K1, kern a' (x - y) * Du (y, τ) i := by
  have h := hτ i (zeta a' x) (zeta_contDiff a' x) (zeta_hasCompactSupport ha' x)
    (zeta_tsupport_subset_U ha' hball hK1U)
  have vanish : ∀ (f : Vec d → ℝ), ∫ y in U, f y * zeta a' x y = ∫ y in K1, kern a' (x - y) * f y :=
    fun f => setIntegral_pairing ha' hball hU hK1m hK1U f
  have h1 : ∫ y in U, parSlice u.toFun τ y * fderiv ℝ (zeta a' x) y (basisVec i) =
      -∫ y in K1, fderiv ℝ (kern a') (x - y) (basisVec i) * u.toFun (y, τ) := by
    have : ∀ y, parSlice u.toFun τ y * fderiv ℝ (zeta a' x) y (basisVec i) =
        -(fderiv ℝ (kern a') (x - y) (basisVec i) * u.toFun (y, τ)) := fun y => by
      simp only [fderiv_zeta, parSlice]; ring
    simp only [this, integral_neg]
    congr 1
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hK1U]
    intro y hy
    have hyb : y ∉ closedBall x a' := fun h => hy.2 (hball h)
    simp [fderiv_kern_eq_zero_of_lt_norm ha' (lt_norm_of_notMem_closedBall hyb)]
  have h2 : ∫ y in U, parSlice u.grad τ y i * zeta a' x y =
      ∫ y in K1, kern a' (x - y) * u.grad (y, τ) i :=
    vanish (fun y => u.grad (y, τ) i)
  have h3 : ∫ y in K1, kern a' (x - y) * Du (y, τ) i =
      ∫ y in K1, kern a' (x - y) * u.grad (y, τ) i := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hK1U (hDu i)] with y hy
    rw [hy]
  rw [h1, h2] at h
  rw [h3]
  linarith

/-- Bundling of a parabolic weak solution into the abstract data. -/
theorem exists_data (hU : IsOpen U) (hI : I.OrdConnected)
    (ha : IsParabolicCoeff lam Lam a U I) (u : ParH1Function U I)
    (hu : IsParabolicWeakSolution a U I u) (φ : ParCutoff U I) {s t : ℝ} (hs : s ∈ I)
    (ht : t ∈ I) (hst : s < t) :
    ∃ D : Data d, D.u = u.toFun ∧ D.φ = φ.toFun ∧ D.s = s ∧ D.t = t ∧ D.K ⊆ U ∧
      (∀ x ∈ U, x ∉ D.K → ∀ τ ∈ I, φ.toFun (x, τ) = 0) ∧
      ∀ᵐ z ∂(volume.restrict (U ×ˢ I)),
        (∀ i, D.G z i = flux a u z i) ∧ ∀ i, D.Du z i = u.grad z i := by
  obtain ⟨K, δ0, hKc, hKU, hδ0, hδ1, hcU, hφ0⟩ := exists_collar hU φ
  have hIcc : Icc s t ⊆ I := hI.out hs ht
  have hDuM : ∀ i, AEStronglyMeasurable (fun z => u.grad z i) (volume.restrict (U ×ˢ I)) :=
    fun i => (u.gradMemL2 i).aestronglyMeasurable
  have hFM : ∀ i, AEStronglyMeasurable (fun z => flux a u z i) (volume.restrict (U ×ˢ I)) :=
    fun i => (flux_memLp ha u i).aestronglyMeasurable
  set Du : Vec d × ℝ → Vec d := fun z i => (hDuM i).mk _ z with hDu
  set G : Vec d × ℝ → Vec d := fun z i => (hFM i).mk _ z with hG
  have hae : ∀ᵐ z ∂(volume.restrict (U ×ˢ I)), (∀ i, G z i = flux a u z i) ∧
      ∀ i, Du z i = u.grad z i := by
    have h1 : ∀ᵐ z ∂(volume.restrict (U ×ˢ I)), ∀ i, G z i = flux a u z i := by
      rw [ae_all_iff]; intro i; exact (hFM i).ae_eq_mk.mono fun z hz => hz.symm
    have h2 : ∀ᵐ z ∂(volume.restrict (U ×ˢ I)), ∀ i, Du z i = u.grad z i := by
      rw [ae_all_iff]; intro i; exact (hDuM i).ae_eq_mk.mono fun z hz => hz.symm
    filter_upwards [h1, h2] with z a1 a2 using ⟨a1, a2⟩
  have hK1U : cthickening δ0 K ⊆ U :=
    (cthickening_mono (by linarith) K).trans hcU
  have hslab : cthickening δ0 K ×ˢ Ioc s t ⊆ U ×ˢ I :=
    prod_mono hK1U ((Ioc_subset_Icc_self).trans hIcc)
  have hle : (volume.restrict (cthickening δ0 K ×ˢ Ioc s t)) ≤ volume.restrict (U ×ˢ I) :=
    Measure.restrict_mono hslab le_rfl
  have haeS : ∀ᵐ z ∂(volume.restrict (cthickening δ0 K ×ˢ Ioc s t)),
      (∀ i, G z i = flux a u z i) ∧ ∀ i, Du z i = u.grad z i :=
    ae_restrict_of_ae_restrict_of_subset hslab hae
  have hφK : ∀ x τ, τ ∈ Icc s t → x ∈ cthickening (2 * δ0) K → x ∉ K → φ.toFun (x, τ) = 0 := by
    intro x τ hτ hx hxK
    exact hφ0 x (hcU hx) hxK τ (hIcc hτ)
  have hus : ∀ τ ∈ Icc s t, MemLp (fun y => u.toFun (y, τ)) 2 (volume.restrict (cthickening δ0 K)) := by
    intro τ hτ
    exact u.sliceL2loc τ (hIcc hτ) _ hKc.cthickening hK1U
  have hwg : ∀ᵐ τ ∂(volume.restrict (Ioc s t)), ∀ a' : ℝ, 0 < a' → a' ≤ δ0 → ∀ x ∈ K, ∀ i,
      ∫ y in cthickening δ0 K, fderiv ℝ (kern a') (x - y) (basisVec i) * u.toFun (y, τ) =
        ∫ y in cthickening δ0 K, kern a' (x - y) * Du (y, τ) i := by
    have hIoc : Ioc s t ⊆ I := Ioc_subset_Icc_self.trans hIcc
    have hw1 : ∀ᵐ τ ∂(volume.restrict (Ioc s t)),
        HasWeakGradientOn U (parSlice u.toFun τ) (parSlice u.grad τ) :=
      ae_restrict_of_ae_restrict_of_subset hIoc u.sliceWeakGradient
    have hw2 : ∀ᵐ τ ∂(volume.restrict (Ioc s t)), ∀ i,
        (fun y => Du (y, τ) i) =ᵐ[volume.restrict U] fun y => u.grad (y, τ) i := by
      have h : ∀ᵐ z ∂((volume.restrict U).prod (volume.restrict I)), ∀ i, Du z i = u.grad z i := by
        rw [← volume_restrict_prod]; exact hae.mono fun z hz => hz.2
      have h' := ae_restrict_of_ae_restrict_of_subset hIoc (ae_ae_swap h)
      filter_upwards [h'] with τ hτ i
      exact hτ.mono fun y hy => hy i
    filter_upwards [hw1, hw2] with τ h1 h2 a' ha' haδ x hx i
    exact weakGrad_identity hU u isClosed_cthickening.measurableSet hK1U ha'
      ((closedBall_subset_cthickening hx a').trans (cthickening_mono haδ K)) h1 h2 i
  have hslice : ∀ a' : ℝ, 0 < a' → a' ≤ δ0 → ∀ x ∈ K, ∀ τ1 τ2 : ℝ, s ≤ τ1 → τ1 ≤ τ2 → τ2 ≤ t →
      (∫ y in cthickening δ0 K, kern a' (x - y) * u.toFun (y, τ2)) -
          (∫ y in cthickening δ0 K, kern a' (x - y) * u.toFun (y, τ1)) =
        ∫ z in cthickening δ0 K ×ˢ Ioc τ1 τ2,
          ∑ i, G z i * fderiv ℝ (kern a') (x - z.1) (basisVec i) := by
    intro a' ha' haδ x hx τ1 τ2 h1 h12 h2
    exact slice_identity_aux hU hI ha u hu (isClosed_cthickening.measurableSet) hK1U ha'
      ((closedBall_subset_cthickening hx a').trans (cthickening_mono haδ K))
      (hIcc ⟨h1, h12.trans h2⟩) (hIcc ⟨h1.trans h12, h2⟩) h12
      (hae.mono fun z hz => hz.1)
  refine ⟨⟨K, hKc, δ0, hδ0, hδ1, s, t, hst, u.toFun, Du, G, φ.toFun, φ.contDiff, hφK,
    fun i => ((hDuM i).stronglyMeasurable_mk).measurable,
    fun i => ((hFM i).stronglyMeasurable_mk).measurable,
    u.memL2.mono_measure hle,
    fun i => ((u.gradMemL2 i).mono_measure hle).ae_eq (haeS.mono fun z hz => (hz.2 i).symm),
    fun i => ((flux_memLp ha u i).mono_measure hle).ae_eq (haeS.mono fun z hz => (hz.1 i).symm),
    hus, hwg, hslice⟩, rfl, rfl, rfl, rfl, hKU, hφ0, hae⟩

end Bridge
