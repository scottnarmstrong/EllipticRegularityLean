module

public import EllipticRegularity.Parabolic.SliceEstimate.VSlice
public import EllipticRegularity.Parabolic.SliceEstimate.TimeEnergyCore
public import EllipticRegularity.Parabolic.Energy.Bridge
public import EllipticRegularity.Parabolic.Caccioppoli.Cutoff

/-!
# From `H¹_par` data to the abstract time-energy data

Test functions `x ↦ ∂ᵢ k_a(y - x)`, the every-time mollified gradients `Ab`, `Zb`, and the
verification of the hypotheses of `EData`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.Slice

open MeasureTheory Set Filter Topology Metric PDE PDE.Parabolic PDE.Parabolic.Energy
  PDE.Parabolic.WeakSlice

variable {d : ℕ}

/-- The test function `x ↦ (∂ᵢ k_a)(y - x)`. -/
noncomputable def dzeta (a : ℝ) (y : Vec d) (i : Fin d) : Vec d → ℝ :=
  fun x => fderiv ℝ (kern a) (y - x) (basisVec i)

theorem dzeta_eq (a : ℝ) (y : Vec d) (i : Fin d) (x : Vec d) :
    dzeta a y i x = -fderiv ℝ (zeta a y) x (basisVec i) := by
  rw [fderiv_zeta]; simp [dzeta]

theorem dzeta_eq_zero {a : ℝ} (ha : 0 < a) {y x : Vec d} (i : Fin d) (hx : x ∉ closedBall y a) :
    dzeta a y i x = 0 := by
  have : a < ‖y - x‖ := by
    rw [mem_closedBall, dist_eq_norm, not_le] at hx
    rwa [← norm_neg, neg_sub]
  simp [dzeta, fderiv_kern_eq_zero_of_lt_norm ha this]

theorem dzeta_contDiff_one (a : ℝ) (y : Vec d) (i : Fin d) : ContDiff ℝ 1 (dzeta a y i) := by
  have h : dzeta a y i = fun x => -fderiv ℝ (zeta a y) x (basisVec i) :=
    funext (dzeta_eq a y i)
  rw [h]
  have h1 : ContDiff ℝ 1 (fderiv ℝ (zeta a y)) :=
    (zeta_contDiff a y).fderiv_right (m := 1) (by simp)
  exact (h1.clm_apply contDiff_const).neg

theorem dzeta_hasCompactSupport {a : ℝ} (ha : 0 < a) (y : Vec d) (i : Fin d) :
    HasCompactSupport (dzeta a y i) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall y a) fun x hx => by
    by_contra h; exact hx (dzeta_eq_zero ha i h)

theorem dzeta_tsupport_subset {a : ℝ} (ha : 0 < a) (y : Vec d) (i : Fin d) :
    tsupport (dzeta a y i) ⊆ closedBall y a := by
  refine closure_minimal (fun x hx => ?_) isClosed_closedBall
  by_contra h
  exact hx (dzeta_eq_zero ha i h)


theorem volume_Ioc_ne_zero : (volume.restrict (Ioc (-1 : ℝ) 0)) ≠ 0 := by
  intro h
  have := congrArg (fun μ : Measure ℝ => μ univ) h
  simp at this

theorem ae_elliptic_space {lam Lam : ℝ} {a₀ : Vec d → Mat d}
    (ha : IsParabolicCoeff lam Lam (fun z : Vec d × ℝ => a₀ z.1)
      (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0)) :
    ∀ᵐ x ∂(volume.restrict (euclideanBall (0 : Vec d) 1)), IsEllipticMatrix lam Lam (a₀ x) := by
  have h := ha.elliptic
  rw [volume_restrict_prod] at h
  have h2 := Measure.ae_ae_of_ae_prod h
  have : NeBot (ae (volume.restrict (Ioc (-1 : ℝ) 0))) := ae_neBot.2 volume_Ioc_ne_zero
  filter_upwards [h2] with x hx
  exact hx.exists.choose_spec

theorem aemeasurable_space {lam Lam : ℝ} {a₀ : Vec d → Mat d}
    (ha : IsParabolicCoeff lam Lam (fun z : Vec d × ℝ => a₀ z.1)
      (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0)) (i j : Fin d) :
    AEMeasurable (fun x => a₀ x i j) (volume.restrict (euclideanBall (0 : Vec d) 1)) := by
  have h := ha.measurable i j
  rw [volume_restrict_prod] at h
  have hsw : AEMeasurable (fun w : ℝ × Vec d => a₀ w.2 i j)
      ((volume.restrict (Ioc (-1 : ℝ) 0)).prod (volume.restrict (euclideanBall (0 : Vec d) 1))) :=
    h.comp_quasiMeasurePreserving
      (Measure.measurePreserving_swap (μ := volume.restrict (Ioc (-1 : ℝ) 0))
        (ν := volume.restrict (euclideanBall (0 : Vec d) 1))).quasiMeasurePreserving
  have h1 := hsw.aestronglyMeasurable.prodMk_left
  have : NeBot (ae (volume.restrict (Ioc (-1 : ℝ) 0))) := ae_neBot.2 volume_Ioc_ne_zero
  obtain ⟨τ, hτ⟩ := h1.exists
  exact hτ.aemeasurable


/-- The every-time mollified gradient pairing `∫_B w(x,τ) (∂ᵢ k_a)(y - x) dx`. -/
noncomputable def AbF (w : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (i : Fin d) (a : ℝ) (y : Vec d) (τ : ℝ) : ℝ :=
  ∫ x in euclideanBall (0 : Vec d) 1, w.toFun (x, τ) * dzeta a y i x

theorem setIntegral_dzeta {K1 B' : Set (Vec d)} (hK1m : MeasurableSet K1) (hB : MeasurableSet B')
    (hsub : K1 ⊆ B') {a : ℝ} (ha : 0 < a) {y : Vec d} (hball : closedBall y a ⊆ K1) (i : Fin d)
    (f : Vec d → ℝ) :
    ∫ x in B', f x * dzeta a y i x = ∫ x in K1, fderiv ℝ (kern a) (y - x) (basisVec i) * f x := by
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hB hsub]
  · refine setIntegral_congr_fun hK1m fun x _ => ?_
    simp only [dzeta]; ring
  · intro x hx
    have : x ∉ closedBall y a := fun h => hx.2 (hball h)
    simp [dzeta_eq_zero ha i this]

theorem mollT_eq_setIntegral {K1 : Set (Vec d)} (hK1m : MeasurableSet K1) (a : ℝ)
    (g : Vec d × ℝ → ℝ) (y : Vec d) (τ : ℝ) :
    mollT a K1 g (y, τ) = ∫ x in K1, kern a (y - x) * g (x, τ) := by
  rw [mollT_eq, ← integral_indicator hK1m]
  congr 1; funext x
  by_cases hx : x ∈ K1 <;> simp [hx]


/-- Abstract data for a compact `K` inside the ball with collar, an initial time `p` and any `C¹`
weight `φ` vanishing at time `p` on `K`. -/
theorem exists_edata_gen {lam Lam : ℝ} {a₀ : Vec d → Mat d}
    (ha : IsParabolicCoeff lam Lam (fun z : Vec d × ℝ => a₀ z.1)
      (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (u v : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (hv : ∀ ψ : ParTestFunction (euclideanBall (0 : Vec d) 1) (interior (Ioc (-1 : ℝ) 0)),
      ∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0, v.toFun z * ψ.toFun z =
        -∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0,
          u.toFun z * parTimeDeriv ψ.toFun z)
    {K : Set (Vec d)} {δ0 : ℝ} (hKc : IsCompact K) (hδ0 : 0 < δ0) (hδ1 : δ0 ≤ 1)
    (hKU : K ⊆ euclideanBall (0 : Vec d) 1) (hK1U : cthickening δ0 K ⊆ euclideanBall (0 : Vec d) 1)
    {p : ℝ} (hp1 : -1 < p) (hp0 : p < 0) (φ : Vec d × ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hφp : ∀ x ∈ K, φ (x, p) = 0) :
    ∃ D : EData d, D.K = K ∧ D.δ0 = δ0 ∧ D.p = p ∧ D.q = 0 ∧ D.A = a₀ ∧ D.φ = φ ∧ D.lam = lam ∧
      D.Lam = Lam ∧ (∀ i, D.W i = fun z => u.grad z i) ∧ (∀ i, D.Z i = fun z => v.grad z i) := by
  have hU : IsOpen (euclideanBall (0 : Vec d) 1) := isOpen_euclideanBall _ _
  have hI : (Ioc (-1 : ℝ) 0).OrdConnected := ordConnected_Ioc
  have hK1m : MeasurableSet (cthickening δ0 K) := isClosed_cthickening.measurableSet
  have hpJ : Ioc p 0 ⊆ Ioc (-1 : ℝ) 0 := Ioc_subset_Ioc_left hp1.le
  have hslab : cthickening δ0 K ×ˢ Ioc p 0 ⊆
      euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0 := prod_mono hK1U hpJ
  have hle : (volume.restrict (cthickening δ0 K ×ˢ Ioc p 0) : Measure (Vec d × ℝ)) ≤
      volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0) :=
    Measure.restrict_mono hslab le_rfl
  -- mollified weak gradients
  have hgradAb : ∀ (w : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0)),
      ∀ᵐ τ ∂(volume.restrict (Ioc p 0)), ∀ a : ℝ, 0 < a → a ≤ δ0 → ∀ y ∈ K, ∀ i,
        AbF w i a y τ = mollT a (cthickening δ0 K) (fun z => w.grad z i) (y, τ) := by
    intro w
    have h1 : ∀ᵐ τ ∂(volume.restrict (Ioc p 0)),
        HasWeakGradientOn (euclideanBall (0 : Vec d) 1) (parSlice w.toFun τ) (parSlice w.grad τ) :=
      ae_restrict_of_ae_restrict_of_subset hpJ w.sliceWeakGradient
    filter_upwards [h1] with τ hτ a ha haδ y hy i
    have hball : closedBall y a ⊆ cthickening δ0 K :=
      (closedBall_subset_cthickening hy a).trans (cthickening_mono haδ K)
    have hid := weakGrad_identity hU w hK1m hK1U ha hball hτ (Du := w.grad)
      (fun j => Filter.EventuallyEq.rfl) i
    rw [AbF, setIntegral_dzeta hK1m hU.measurableSet hK1U ha hball i, mollT_eq_setIntegral hK1m]
    simpa using hid
  -- absolute continuity
  have hAC : ∀ a : ℝ, 0 < a → a ≤ δ0 → ∀ y ∈ K, ∀ i, ∀ τ1 τ2 : ℝ, p ≤ τ1 → τ1 ≤ τ2 → τ2 ≤ 0 →
      AbF u i a y τ2 - AbF u i a y τ1 = ∫ σ in τ1..τ2, AbF v i a y σ := by
    intro a ha haδ y hy i τ1 τ2 h1 h12 h2
    rcases h12.eq_or_lt with rfl | hlt
    · simp
    · have hball : closedBall y a ⊆ cthickening δ0 K :=
        (closedBall_subset_cthickening hy a).trans (cthickening_mono haδ K)
      have hts : tsupport (dzeta a y i) ⊆ euclideanBall (0 : Vec d) 1 :=
        (dzeta_tsupport_subset ha y i).trans (hball.trans hK1U)
      have := time_derivative_slice hU hI u v hv (dzeta_contDiff_one a y i)
        (dzeta_hasCompactSupport ha y i) hts (s := τ1) (t := τ2)
        ⟨by linarith, by linarith⟩ ⟨by linarith, h2⟩ hlt
      rw [intervalIntegral.integral_of_le hlt.le]
      exact this
  have hZint : ∀ a : ℝ, 0 < a → a ≤ δ0 → ∀ y ∈ K, ∀ i,
      IntervalIntegrable (AbF v i a y) volume p 0 := by
    intro a ha haδ y hy i
    have hball : closedBall y a ⊆ cthickening δ0 K :=
      (closedBall_subset_cthickening hy a).trans (cthickening_mono haδ K)
    have hts : tsupport (dzeta a y i) ⊆ euclideanBall (0 : Vec d) 1 :=
      (dzeta_tsupport_subset ha y i).trans (hball.trans hK1U)
    have hIcc : Icc p 0 ⊆ Ioc (-1 : ℝ) 0 := fun τ hτ => ⟨by linarith [hτ.1], hτ.2⟩
    have hint := integrableOn_mul_fst hU v.memL2 (dzeta_contDiff_one a y i).continuous
      (dzeta_hasCompactSupport ha y i) hts hIcc measurableSet_Icc
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hp0.le).2
      (integral_prod_slices hint).1
  refine ⟨⟨K, hKc, δ0, hδ0, hδ1, p, 0, hp0, lam, Lam, a₀,
    fun i j => (aemeasurable_space ha i j).mono_measure (Measure.restrict_mono hKU le_rfl),
    (ae_elliptic_space ha).filter_mono (ae_mono (Measure.restrict_mono hKU le_rfl)),
    φ, hφ, hφp,
    fun i z => u.grad z i, fun i z => v.grad z i,
    fun i => (u.gradMemL2 i).mono_measure hle,
    fun i => (v.gradMemL2 i).mono_measure hle,
    fun i a y τ => AbF u i a y τ, fun i a y τ => AbF v i a y τ,
    hgradAb u, hgradAb v, hAC, hZint⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    fun i => rfl, fun i => rfl⟩

/-- The abstract data attached to a cutoff and to `u`, `v = ∂ₜu`. -/
theorem exists_edata {lam Lam : ℝ} {a₀ : Vec d → Mat d}
    (ha : IsParabolicCoeff lam Lam (fun z : Vec d × ℝ => a₀ z.1)
      (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (u v : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (hv : ∀ ψ : ParTestFunction (euclideanBall (0 : Vec d) 1) (interior (Ioc (-1 : ℝ) 0)),
      ∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0, v.toFun z * ψ.toFun z =
        -∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0,
          u.toFun z * parTimeDeriv ψ.toFun z)
    (φ : ParCutoff (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0)) :
    ∃ D : EData d, D.A = a₀ ∧ D.φ = φ.toFun ∧ D.lam = lam ∧ D.Lam = Lam ∧ D.q = 0 ∧
      D.K ⊆ euclideanBall (0 : Vec d) 1 ∧ -1 < D.p ∧ D.p < 0 ∧
      (∀ i, D.W i = fun z => u.grad z i) ∧ (∀ i, D.Z i = fun z => v.grad z i) ∧
      (∀ x ∈ euclideanBall (0 : Vec d) 1, x ∉ D.K → ∀ τ ∈ Ioc (-1 : ℝ) 0, φ.toFun (x, τ) = 0) ∧
      (∀ x ∈ euclideanBall (0 : Vec d) 1, ∀ τ ∈ Ioc (-1 : ℝ) 0, τ ≤ D.p → φ.toFun (x, τ) = 0) := by
  have hU : IsOpen (euclideanBall (0 : Vec d) 1) := isOpen_euclideanBall _ _
  obtain ⟨K, δ0, hKc, hKU, hδ0, hδ1, hcU, hφ0⟩ := exists_collar hU φ
  obtain ⟨m, hm1, hm0, hmφ⟩ := PDE.ParabCaccioppoli.exists_vanishing_time φ
  set p : ℝ := (-1 + m) / 2 with hp
  have hpm : p < m := by rw [hp]; linarith
  have hp1 : -1 < p := by rw [hp]; linarith
  have hp0 : p < 0 := by linarith
  have hK1U : cthickening δ0 K ⊆ euclideanBall (0 : Vec d) 1 :=
    (cthickening_mono (by linarith) K).trans hcU
  obtain ⟨D, hK, hδ, hp', hq, hA, hφD, hl, hL, hW, hZ⟩ := exists_edata_gen ha u v hv hKc hδ0 hδ1 hKU
    hK1U hp1 hp0 φ.toFun φ.contDiff (fun x hx => hmφ (x, p) ⟨hKU hx, hp1, hp0.le⟩ hpm)
  refine ⟨D, hA, hφD, hl, hL, hq, hK ▸ hKU, hp' ▸ hp1, hp' ▸ hp0, hW, hZ, ?_, ?_⟩
  · intro x hx hxK τ hτ
    exact hφ0 x hx (hK ▸ hxK) τ hτ
  · intro x hx τ hτ hτp
    exact hmφ (x, τ) ⟨hx, hτ⟩ (lt_of_le_of_lt (hp' ▸ hτp) hpm)

end PDE.Parabolic.Slice
