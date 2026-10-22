module

public import EllipticRegularity.Parabolic.SliceEstimate.VSliceIdentity
public import EllipticRegularity.Parabolic.Energy.Conclusion
public import EllipticRegularity.Parabolic.Caccioppoli.Assembly

/-!
# The energy identity for `v = ∂ₜu`

`v` satisfies the weak-slice identity (`v_slice_identity`), which is the only consequence of the
weak-solution property used in the energy estimate.  We rebuild the abstract `Data` for `v` and deduce
`EnergyConclusion` for `v`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.Slice

open MeasureTheory Set Filter Topology Metric PDE PDE.Parabolic PDE.Parabolic.Energy
  PDE.Parabolic.WeakSlice

variable {d : ℕ}

section DataV

variable {lam Lam : ℝ} {a₀ : Vec d → Mat d}

/-- The mollified weak time-slice identity for `v`. -/
theorem slice_identity_aux_v
    (ha : IsParabolicCoeff lam Lam (fun z : Vec d × ℝ => a₀ z.1)
      (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (u v : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (hu : IsParabolicWeakSolution (fun z : Vec d × ℝ => a₀ z.1)
      (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u)
    (hv : ∀ ψ : ParTestFunction (euclideanBall (0 : Vec d) 1) (interior (Ioc (-1 : ℝ) 0)),
      ∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0, v.toFun z * ψ.toFun z =
        -∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0,
          u.toFun z * parTimeDeriv ψ.toFun z)
    {K1 : Set (Vec d)} (hK1c : IsCompact K1) {δ' : ℝ} (hδ'0 : 0 < δ') (hδ'1 : δ' ≤ 1)
    (hK1δ : cthickening δ' K1 ⊆ euclideanBall (0 : Vec d) 1)
    (hK1U : K1 ⊆ euclideanBall (0 : Vec d) 1) {a' : ℝ} (ha' : 0 < a') {x : Vec d}
    (hball : closedBall x a' ⊆ K1) {τ1 τ2 : ℝ} (h1 : τ1 ∈ Ioc (-1 : ℝ) 0)
    (h2 : τ2 ∈ Ioc (-1 : ℝ) 0) (h12 : τ1 ≤ τ2) {G : Vec d × ℝ → Vec d}
    (hG : ∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
      ∀ i, G z i = flux (fun z : Vec d × ℝ => a₀ z.1) v z i) :
    (∫ y in K1, kern a' (x - y) * v.toFun (y, τ2)) -
        (∫ y in K1, kern a' (x - y) * v.toFun (y, τ1)) =
      ∫ z in K1 ×ˢ Ioc τ1 τ2, ∑ i, G z i * fderiv ℝ (kern a') (x - z.1) (basisVec i) := by
  have hU : IsOpen (euclideanBall (0 : Vec d) 1) := isOpen_euclideanBall _ _
  have hI : (Ioc (-1 : ℝ) 0).OrdConnected := ordConnected_Ioc
  have hK1m : MeasurableSet K1 := hK1c.measurableSet
  rcases h12.eq_or_lt with rfl | hlt
  · simp
  · obtain ⟨_, hws⟩ := v_slice_identity ha u v hu hv (zeta_contDiff_one a' x)
      (zeta_hasCompactSupport ha' x) hK1c hδ'0 hδ'1 hK1U hK1δ
      ((zeta_tsupport_subset ha' x).trans hball) h1 h2 hlt
    rw [setIntegral_pairing ha' hball hU hK1m hK1U (fun y => v.toFun (y, τ2)),
      setIntegral_pairing ha' hball hU hK1m hK1U (fun y => v.toFun (y, τ1))] at hws
    rw [hws]
    simp only [vecDot_flux_zeta (a := fun z : Vec d × ℝ => a₀ z.1)]
    rw [integral_neg, neg_neg]
    have hsub : K1 ×ˢ Ioc τ1 τ2 ⊆ euclideanBall (0 : Vec d) 1 ×ˢ Ioc τ1 τ2 :=
      prod_mono hK1U subset_rfl
    rw [← setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hU.measurableSet.prod measurableSet_Ioc)
      hsub]
    · have hsubI : euclideanBall (0 : Vec d) 1 ×ˢ Ioc τ1 τ2 ⊆
          euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0 :=
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


/-- Bundling of `v` into the abstract data. -/
theorem exists_data_v
    (ha : IsParabolicCoeff lam Lam (fun z : Vec d × ℝ => a₀ z.1)
      (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (u v : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (hu : IsParabolicWeakSolution (fun z : Vec d × ℝ => a₀ z.1)
      (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u)
    (hv : ∀ ψ : ParTestFunction (euclideanBall (0 : Vec d) 1) (interior (Ioc (-1 : ℝ) 0)),
      ∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0, v.toFun z * ψ.toFun z =
        -∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0,
          u.toFun z * parTimeDeriv ψ.toFun z)
    (φ : ParCutoff (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0)) {s t : ℝ}
    (hs : s ∈ Ioc (-1 : ℝ) 0) (ht : t ∈ Ioc (-1 : ℝ) 0) (hst : s < t) :
    ∃ D : Data d, D.u = v.toFun ∧ D.φ = φ.toFun ∧ D.s = s ∧ D.t = t ∧
      D.K ⊆ euclideanBall (0 : Vec d) 1 ∧
      (∀ x ∈ euclideanBall (0 : Vec d) 1, x ∉ D.K → ∀ τ ∈ Ioc (-1 : ℝ) 0, φ.toFun (x, τ) = 0) ∧
      ∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
        (∀ i, D.G z i = flux (fun z : Vec d × ℝ => a₀ z.1) v z i) ∧ ∀ i, D.Du z i = v.grad z i := by
  have hU : IsOpen (euclideanBall (0 : Vec d) 1) := isOpen_euclideanBall _ _
  have hI : (Ioc (-1 : ℝ) 0).OrdConnected := ordConnected_Ioc
  obtain ⟨K, δ0, hKc, hKU, hδ0, hδ1, hcU, hφ0⟩ := exists_collar hU φ
  have hIcc : Icc s t ⊆ Ioc (-1 : ℝ) 0 := hI.out hs ht
  have hDuM : ∀ i, AEStronglyMeasurable (fun z => v.grad z i)
      (volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)) :=
    fun i => (v.gradMemL2 i).aestronglyMeasurable
  have hFM : ∀ i, AEStronglyMeasurable (fun z => flux (fun z : Vec d × ℝ => a₀ z.1) v z i)
      (volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)) :=
    fun i => (flux_memLp ha v i).aestronglyMeasurable
  set Du : Vec d × ℝ → Vec d := fun z i => (hDuM i).mk _ z with hDu
  set G : Vec d × ℝ → Vec d := fun z i => (hFM i).mk _ z with hG
  have hae : ∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
      (∀ i, G z i = flux (fun z : Vec d × ℝ => a₀ z.1) v z i) ∧ ∀ i, Du z i = v.grad z i := by
    have h1 : ∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
        ∀ i, G z i = flux (fun z : Vec d × ℝ => a₀ z.1) v z i := by
      rw [ae_all_iff]; intro i; exact (hFM i).ae_eq_mk.mono fun z hz => hz.symm
    have h2 : ∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
        ∀ i, Du z i = v.grad z i := by
      rw [ae_all_iff]; intro i; exact (hDuM i).ae_eq_mk.mono fun z hz => hz.symm
    filter_upwards [h1, h2] with z a1 a2 using ⟨a1, a2⟩
  have hK1U : cthickening δ0 K ⊆ euclideanBall (0 : Vec d) 1 :=
    (cthickening_mono (by linarith) K).trans hcU
  have hK1δ : cthickening δ0 (cthickening δ0 K) ⊆ euclideanBall (0 : Vec d) 1 := by
    refine (cthickening_cthickening_subset hδ0.le hδ0.le K).trans ?_
    rw [← two_mul]; exact hcU
  have hslab : cthickening δ0 K ×ˢ Ioc s t ⊆
      euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0 :=
    prod_mono hK1U ((Ioc_subset_Icc_self).trans hIcc)
  have hle : (volume.restrict (cthickening δ0 K ×ˢ Ioc s t) : Measure (Vec d × ℝ)) ≤
      volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0) :=
    Measure.restrict_mono hslab le_rfl
  have haeS : ∀ᵐ z ∂(volume.restrict (cthickening δ0 K ×ˢ Ioc s t)),
      (∀ i, G z i = flux (fun z : Vec d × ℝ => a₀ z.1) v z i) ∧ ∀ i, Du z i = v.grad z i :=
    ae_restrict_of_ae_restrict_of_subset hslab hae
  have hφK : ∀ x τ, τ ∈ Icc s t → x ∈ cthickening (2 * δ0) K → x ∉ K → φ.toFun (x, τ) = 0 := by
    intro x τ hτ hx hxK
    exact hφ0 x (hcU hx) hxK τ (hIcc hτ)
  have hus : ∀ τ ∈ Icc s t, MemLp (fun y => v.toFun (y, τ)) 2
      (volume.restrict (cthickening δ0 K)) := by
    intro τ hτ
    exact v.sliceL2loc τ (hIcc hτ) _ hKc.cthickening hK1U
  have hwg : ∀ᵐ τ ∂(volume.restrict (Ioc s t)), ∀ a' : ℝ, 0 < a' → a' ≤ δ0 → ∀ x ∈ K, ∀ i,
      ∫ y in cthickening δ0 K, fderiv ℝ (kern a') (x - y) (basisVec i) * v.toFun (y, τ) =
        ∫ y in cthickening δ0 K, kern a' (x - y) * Du (y, τ) i := by
    have hIoc : Ioc s t ⊆ Ioc (-1 : ℝ) 0 := Ioc_subset_Icc_self.trans hIcc
    have hw1 : ∀ᵐ τ ∂(volume.restrict (Ioc s t)),
        HasWeakGradientOn (euclideanBall (0 : Vec d) 1) (parSlice v.toFun τ) (parSlice v.grad τ) :=
      ae_restrict_of_ae_restrict_of_subset hIoc v.sliceWeakGradient
    have hw2 : ∀ᵐ τ ∂(volume.restrict (Ioc s t)), ∀ i,
        (fun y => Du (y, τ) i) =ᵐ[volume.restrict (euclideanBall (0 : Vec d) 1)]
          fun y => v.grad (y, τ) i := by
      have h : ∀ᵐ z ∂((volume.restrict (euclideanBall (0 : Vec d) 1)).prod
          (volume.restrict (Ioc (-1 : ℝ) 0))), ∀ i, Du z i = v.grad z i := by
        rw [← volume_restrict_prod]; exact hae.mono fun z hz => hz.2
      have h' := ae_restrict_of_ae_restrict_of_subset hIoc (ae_ae_swap h)
      filter_upwards [h'] with τ hτ i
      exact hτ.mono fun y hy => hy i
    filter_upwards [hw1, hw2] with τ h1 h2 a' ha' haδ x hx i
    exact weakGrad_identity hU v isClosed_cthickening.measurableSet hK1U ha'
      ((closedBall_subset_cthickening hx a').trans (cthickening_mono haδ K)) h1 h2 i
  have hslice : ∀ a' : ℝ, 0 < a' → a' ≤ δ0 → ∀ x ∈ K, ∀ τ1 τ2 : ℝ, s ≤ τ1 → τ1 ≤ τ2 → τ2 ≤ t →
      (∫ y in cthickening δ0 K, kern a' (x - y) * v.toFun (y, τ2)) -
          (∫ y in cthickening δ0 K, kern a' (x - y) * v.toFun (y, τ1)) =
        ∫ z in cthickening δ0 K ×ˢ Ioc τ1 τ2,
          ∑ i, G z i * fderiv ℝ (kern a') (x - z.1) (basisVec i) := by
    intro a' ha' haδ x hx τ1 τ2 h1 h12 h2
    exact slice_identity_aux_v ha u v hu hv hKc.cthickening hδ0 hδ1 hK1δ hK1U ha'
      ((closedBall_subset_cthickening hx a').trans (cthickening_mono haδ K))
      (hIcc ⟨h1, h12.trans h2⟩) (hIcc ⟨h1.trans h12, h2⟩) h12
      (hae.mono fun z hz => hz.1)
  refine ⟨⟨K, hKc, δ0, hδ0, hδ1, s, t, hst, v.toFun, Du, G, φ.toFun, φ.contDiff, hφK,
    fun i => ((hDuM i).stronglyMeasurable_mk).measurable,
    fun i => ((hFM i).stronglyMeasurable_mk).measurable,
    v.memL2.mono_measure hle,
    fun i => ((v.gradMemL2 i).mono_measure hle).ae_eq (haeS.mono fun z hz => (hz.2 i).symm),
    fun i => ((flux_memLp ha v i).mono_measure hle).ae_eq
      (haeS.mono fun z hz => (hz.1 i).symm),
    hus, hwg, hslice⟩, rfl, rfl, rfl, rfl, hKU, hφ0, hae⟩


/-- Part (3) of the energy identity for `v`, for one `s < t`. -/
theorem slab_conclusion_v
    (ha : IsParabolicCoeff lam Lam (fun z : Vec d × ℝ => a₀ z.1)
      (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (u v : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (hu : IsParabolicWeakSolution (fun z : Vec d × ℝ => a₀ z.1)
      (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u)
    (hv : ∀ ψ : ParTestFunction (euclideanBall (0 : Vec d) 1) (interior (Ioc (-1 : ℝ) 0)),
      ∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0, v.toFun z * ψ.toFun z =
        -∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0,
          u.toFun z * parTimeDeriv ψ.toFun z)
    (φ : ParCutoff (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0)) {s t : ℝ}
    (hs : s ∈ Ioc (-1 : ℝ) 0) (ht : t ∈ Ioc (-1 : ℝ) 0) (hst : s < t) :
    IntegrableOn (fun z => v.toFun z ^ 2 * φ.toFun z * parTimeDeriv φ.toFun z)
        (euclideanBall (0 : Vec d) 1 ×ˢ Ioc s t) ∧
      IntegrableOn (fun z => vecDot (matVecMul (a₀ z.1) (v.grad z))
          (φ.toFun z ^ 2 • v.grad z + (2 * φ.toFun z * v.toFun z) • parSpaceGrad φ.toFun z))
          (euclideanBall (0 : Vec d) 1 ×ˢ Ioc s t) ∧
      ((1 / 2 : ℝ) * ∫ x in euclideanBall (0 : Vec d) 1, φ.toFun (x, t) ^ 2 * v.toFun (x, t) ^ 2) -
          (1 / 2 : ℝ) * ∫ x in euclideanBall (0 : Vec d) 1, φ.toFun (x, s) ^ 2 * v.toFun (x, s) ^ 2 =
        (∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc s t,
            v.toFun z ^ 2 * φ.toFun z * parTimeDeriv φ.toFun z) -
          ∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc s t, vecDot (matVecMul (a₀ z.1) (v.grad z))
            (φ.toFun z ^ 2 • v.grad z + (2 * φ.toFun z * v.toFun z) • parSpaceGrad φ.toFun z) := by
  have hU : IsOpen (euclideanBall (0 : Vec d) 1) := isOpen_euclideanBall _ _
  have hI : (Ioc (-1 : ℝ) 0).OrdConnected := ordConnected_Ioc
  obtain ⟨D, hDu, hDφ, hDs, hDt, hKU, hφ0, hae⟩ := exists_data_v ha u v hu hv φ hs ht hst
  have hIcc : Icc s t ⊆ Ioc (-1 : ℝ) 0 := hI.out hs ht
  have hIoc : Ioc s t ⊆ Ioc (-1 : ℝ) 0 := Ioc_subset_Icc_self.trans hIcc
  have key := D.energy_identity
  have hA := D.integrable_A
  have hB := D.integrable_B
  unfold Data.μP at key hA hB
  rw [hDu, hDφ, hDs, hDt] at key hA hB
  have hmeas : MeasurableSet (euclideanBall (0 : Vec d) 1 ×ˢ Ioc s t) :=
    hU.measurableSet.prod measurableSet_Ioc
  have hsub : D.K ×ˢ Ioc s t ⊆ euclideanBall (0 : Vec d) 1 ×ˢ Ioc s t := prod_mono hKU subset_rfl
  have hvan : ∀ z ∈ euclideanBall (0 : Vec d) 1 ×ˢ Ioc s t \ D.K ×ˢ Ioc s t, φ.toFun z = 0 := by
    rintro ⟨x, τ⟩ ⟨⟨hx, hτ⟩, hn⟩
    exact hφ0 x hx (fun h => hn ⟨h, hτ⟩) τ (hIoc hτ)
  have haeS : ∀ᵐ z ∂(volume.restrict (D.K ×ˢ Ioc s t)),
      ∑ i, D.G z i * (φ.toFun z ^ 2 * D.Du z i + 2 * φ.toFun z * v.toFun z *
        parSpaceGrad φ.toFun z i) =
      vecDot (matVecMul (a₀ z.1) (v.grad z))
        (φ.toFun z ^ 2 • v.grad z + (2 * φ.toFun z * v.toFun z) • parSpaceGrad φ.toFun z) := by
    have hsl : D.K ×ˢ Ioc s t ⊆ euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0 :=
      prod_mono hKU hIoc
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsl hae] with z hz
    rw [vecDot_eq_sum (fun z : Vec d × ℝ => a₀ z.1)]
    exact Finset.sum_congr rfl fun i _ => by rw [hz.1 i, hz.2 i]
  have hA1 : IntegrableOn (fun z => v.toFun z ^ 2 * φ.toFun z * parTimeDeriv φ.toFun z)
      (D.K ×ˢ Ioc s t) := hA
  have hA' : IntegrableOn (fun z => v.toFun z ^ 2 * φ.toFun z * parTimeDeriv φ.toFun z)
      (euclideanBall (0 : Vec d) 1 ×ˢ Ioc s t) :=
    hA1.of_forall_sdiff_eq_zero hmeas fun z hz => by rw [hvan z hz]; ring
  have hB1 : IntegrableOn (fun z => vecDot (matVecMul (a₀ z.1) (v.grad z))
      (φ.toFun z ^ 2 • v.grad z + (2 * φ.toFun z * v.toFun z) • parSpaceGrad φ.toFun z))
      (D.K ×ˢ Ioc s t) := hB.congr haeS
  have hB' : IntegrableOn (fun z => vecDot (matVecMul (a₀ z.1) (v.grad z))
      (φ.toFun z ^ 2 • v.grad z + (2 * φ.toFun z * v.toFun z) • parSpaceGrad φ.toFun z))
      (euclideanBall (0 : Vec d) 1 ×ˢ Ioc s t) :=
    hB1.of_forall_sdiff_eq_zero hmeas fun z hz => by simp [vecDot, hvan z hz]
  refine ⟨hA', hB', ?_⟩
  have e1 : ∀ τ ∈ Ioc (-1 : ℝ) 0, ∫ x in euclideanBall (0 : Vec d) 1,
      φ.toFun (x, τ) ^ 2 * v.toFun (x, τ) ^ 2 =
      ∫ x in D.K, φ.toFun (x, τ) ^ 2 * v.toFun (x, τ) ^ 2 := by
    intro τ hτ
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hKU fun x hx => ?_
    rw [hφ0 x hx.1 hx.2 τ hτ]; ring
  have e2 : ∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc s t,
        v.toFun z ^ 2 * φ.toFun z * parTimeDeriv φ.toFun z =
      ∫ z in D.K ×ˢ Ioc s t, v.toFun z ^ 2 * φ.toFun z * parTimeDeriv φ.toFun z := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeas hsub fun z hz => ?_
    rw [hvan z hz]; ring
  have e3 : ∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc s t, vecDot (matVecMul (a₀ z.1) (v.grad z))
        (φ.toFun z ^ 2 • v.grad z + (2 * φ.toFun z * v.toFun z) • parSpaceGrad φ.toFun z) =
      ∫ z in D.K ×ˢ Ioc s t, ∑ i, D.G z i * (φ.toFun z ^ 2 * D.Du z i + 2 * φ.toFun z *
        v.toFun z * parSpaceGrad φ.toFun z i) := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeas hsub]
    · exact (integral_congr_ae haeS).symm
    · intro z hz
      simp [vecDot, hvan z hz]
  rw [e1 t ht, e1 s hs, e2, e3]
  exact key


/-- The energy identity (all parts) for `v`, in the form used by the Caccioppoli assembly. -/
theorem energyConclusion_v
    (ha : IsParabolicCoeff lam Lam (fun z : Vec d × ℝ => a₀ z.1)
      (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (u v : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (hu : IsParabolicWeakSolution (fun z : Vec d × ℝ => a₀ z.1)
      (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u)
    (hv : ∀ ψ : ParTestFunction (euclideanBall (0 : Vec d) 1) (interior (Ioc (-1 : ℝ) 0)),
      ∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0, v.toFun z * ψ.toFun z =
        -∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0,
          u.toFun z * parTimeDeriv ψ.toFun z)
    (φ : ParCutoff (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0)) :
    PDE.ParabCaccioppoli.EnergyConclusion (fun z : Vec d × ℝ => a₀ z.1)
      (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) v φ := by
  have hU : IsOpen (euclideanBall (0 : Vec d) 1) := isOpen_euclideanBall _ _
  have hI : (Ioc (-1 : ℝ) 0).OrdConnected := ordConnected_Ioc
  refine ⟨fun t ht => slice_integrable hU v φ ht, ?_,
    fun s t hs ht hst => slab_conclusion_v ha u v hu hv φ hs ht hst⟩
  set A : Vec d × ℝ → ℝ := fun z => v.toFun z ^ 2 * φ.toFun z * parTimeDeriv φ.toFun z with hA
  set B : Vec d × ℝ → ℝ := fun z => vecDot (matVecMul (a₀ z.1) (v.grad z))
    (φ.toFun z ^ 2 • v.grad z + (2 * φ.toFun z * v.toFun z) • parSpaceGrad φ.toFun z) with hB
  refine continuousOn_of_primitive hI
    (g := fun σ => ∫ x in euclideanBall (0 : Vec d) 1, (A - B) (x, σ)) ?_
  intro s t hs ht hst
  obtain ⟨hAi, hBi, hid⟩ := slab_conclusion_v ha u v hu hv φ hs ht hst
  have hΨ : Integrable (A - B)
      (volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc s t)) := hAi.sub hBi
  have hΨ' : Integrable (A - B) ((volume.restrict (euclideanBall (0 : Vec d) 1)).prod
      (volume.restrict (Ioc s t))) := by
    rw [← volume_restrict_prod]; exact hΨ
  refine ⟨hΨ'.integral_prod_right, ?_⟩
  rw [hid, ← integral_sub hAi hBi]
  have := integral_prod_symm (A - B) hΨ'
  rw [← volume_restrict_prod] at this
  exact this

end DataV

end PDE.Parabolic.Slice
