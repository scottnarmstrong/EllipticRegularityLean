module

public import EllipticRegularity.Parabolic.SliceEstimate.TimeEnergyData
public import EllipticRegularity.Parabolic.SliceEstimate.Matrix
public import EllipticRegularity.Parabolic.ParabolicDef

/-!
# The mollified time-energy inequality: pointwise identity, bounds, integrability
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.Slice

open MeasureTheory Set Filter Topology Metric PDE PDE.Parabolic.Energy

variable {d : ℕ}

namespace EData

variable (D : EData d)

/-- The vector `(W_i z)_i`. -/
def Wv (z : Vec d × ℝ) : Vec d := fun i => D.W i z
def Zv (z : Vec d × ℝ) : Vec d := fun i => D.Z i z
def Abv (a : ℝ) (z : Vec d × ℝ) : Vec d := fun i => D.Ab i a z.1 z.2
def Zbv (a : ℝ) (z : Vec d × ℝ) : Vec d := fun i => D.Zb i a z.1 z.2

theorem continuous_phi : Continuous D.φ := D.hφ.continuous

theorem continuous_timeDeriv : Continuous (parTimeDeriv D.φ) :=
  (D.hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem contDiff_timeSlice (x : Vec d) : ContDiff ℝ 1 fun τ => D.φ (x, τ) :=
  D.hφ.comp (contDiff_const.prodMk contDiff_id)

theorem deriv_timeSlice (x : Vec d) (τ : ℝ) :
    deriv (fun τ => D.φ (x, τ)) τ = parTimeDeriv D.φ (x, τ) := by
  have h1 : HasFDerivAt D.φ (fderiv ℝ D.φ (x, τ)) (x, τ) :=
    ((D.hφ.differentiable (by simp)) (x, τ)).hasFDerivAt
  have h2 : HasDerivAt (fun τ : ℝ => ((x, τ) : Vec d × ℝ)) ((0 : Vec d), (1 : ℝ)) τ :=
    (hasDerivAt_const τ x).prodMk (hasDerivAt_id τ)
  exact (h1.comp_hasDerivAt τ h2).deriv

theorem deriv_timeSlice_sq (x : Vec d) (τ : ℝ) :
    deriv (fun τ => D.φ (x, τ) ^ 2) τ = 2 * D.φ (x, τ) * parTimeDeriv D.φ (x, τ) := by
  have h1 : HasDerivAt (fun τ => D.φ (x, τ)) (parTimeDeriv D.φ (x, τ)) τ := by
    have := ((D.contDiff_timeSlice x).differentiable (by simp) τ).hasDerivAt
    rwa [D.deriv_timeSlice] at this
  have h2 : HasDerivAt (fun τ => D.φ (x, τ) * D.φ (x, τ))
      (parTimeDeriv D.φ (x, τ) * D.φ (x, τ) + D.φ (x, τ) * parTimeDeriv D.φ (x, τ)) τ := h1.mul h1
  have e : (fun τ => D.φ (x, τ) ^ 2) = fun τ => D.φ (x, τ) * D.φ (x, τ) := by
    funext τ; ring
  rw [e, h2.deriv]
  ring

/-- The product slab `K × (p,t]` for `t ≤ q` sits in the compact set `K × [p,q]`. -/
theorem slab_subset {t : ℝ} (ht : t ≤ D.q) : D.K ×ˢ Ioc D.p t ⊆ D.K ×ˢ Icc D.p D.q :=
  prod_mono subset_rfl fun _τ hτ => ⟨hτ.1.le, hτ.2.trans ht⟩

theorem μ_eq (t : ℝ) : D.μ t = (volume.restrict D.K).prod (volume.restrict (Ioc D.p t)) :=
  volume_restrict_prod _ _

/-- A continuous weight is bounded on the slab. -/
theorem ae_bound_weight {f : Vec d × ℝ → ℝ} (hf : Continuous f) {t : ℝ} (ht : t ≤ D.q) :
    ∃ M : ℝ, ∀ᵐ z ∂(D.μ t), |f z| ≤ M := by
  obtain ⟨M, hM⟩ := (D.hK.prod isCompact_Icc).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨M, (ae_restrict_iff' (D.K_measurable.prod measurableSet_Ioc)).2
    (Eventually.of_forall fun z hz => ?_)⟩
  simpa using hM z (D.slab_subset ht hz)

theorem ae_fst_mem {t : ℝ} : ∀ᵐ z ∂(D.μ t), z.1 ∈ D.K :=
  (ae_restrict_iff' (D.K_measurable.prod measurableSet_Ioc)).2
    (Eventually.of_forall fun _z hz => hz.1)

theorem ae_elliptic {t : ℝ} : ∀ᵐ z ∂(D.μ t), IsEllipticMatrix D.lam D.Lam (D.A z.1) := by
  rw [μ_eq]
  exact (Measure.quasiMeasurePreserving_fst (μ := volume.restrict D.K)
    (ν := volume.restrict (Ioc D.p t))).ae D.hAe

theorem aemeasurable_A {t : ℝ} (i j : Fin d) :
    AEMeasurable (fun z : Vec d × ℝ => symmPart (D.A z.1) i j) (D.μ t) := by
  rw [μ_eq]
  have h1 : AEMeasurable (fun x => symmPart (D.A x) i j) (volume.restrict D.K) := by
    simp only [symmPart]
    exact ((D.hAm i j).add (D.hAm j i)).div_const 2
  exact h1.comp_quasiMeasurePreserving
    (Measure.quasiMeasurePreserving_fst (μ := volume.restrict D.K)
      (ν := volume.restrict (Ioc D.p t)))

theorem ae_entry_bound {t : ℝ} : ∀ᵐ z ∂(D.μ t), ∀ i j, |symmPart (D.A z.1) i j| ≤ D.Lam := by
  filter_upwards [D.ae_elliptic (t := t)] with z hz i j
  simp only [symmPart]
  have h1 := abs_apply_le_of_isEllipticMatrix hz i j
  have h2 := abs_apply_le_of_isEllipticMatrix hz j i
  rw [abs_div, abs_two]
  have := abs_add_le (D.A z.1 i j) (D.A z.1 j i)
  linarith

theorem ae_qf_nonneg {t : ℝ} (F : Vec d × ℝ → Vec d) :
    ∀ᵐ z ∂(D.μ t), 0 ≤ qf (D.A z.1) (F z) (F z) := by
  filter_upwards [D.ae_elliptic (t := t)] with z hz
  exact qf_self_nonneg hz _

/-- Integrability of a bounded weight times a quadratic form of `L²` fields. -/
theorem integrable_qf {t : ℝ} {ω : Vec d × ℝ → ℝ} (hω : AEStronglyMeasurable ω (D.μ t)) {M : ℝ}
    (hM : ∀ᵐ z ∂(D.μ t), |ω z| ≤ M) {F G : Fin d → Vec d × ℝ → ℝ}
    (hF : ∀ i, MemLp (F i) 2 (D.μ t)) (hG : ∀ i, MemLp (G i) 2 (D.μ t)) :
    Integrable (fun z => ω z * qf (D.A z.1) (fun i => F i z) (fun i => G i z)) (D.μ t) := by
  have hq : ∀ z, ω z * qf (D.A z.1) (fun i => F i z) (fun i => G i z) =
      ∑ i, ∑ j, (ω z * symmPart (D.A z.1) i j) * F i z * G j z := by
    intro z
    rw [qf_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [hq]
  refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
  refine integrable_weight_mul (hω.mul (D.aemeasurable_A i j).aestronglyMeasurable)
    (M := M * D.Lam) ?_ (hF i) (hG j)
  filter_upwards [hM, D.ae_entry_bound (t := t)] with z h1 h2
  rw [abs_mul]
  exact mul_le_mul h1 (h2 i j) (abs_nonneg _) ((abs_nonneg _).trans h1)

/-- The per-point identity: increment of `φ⁴ Q(Ab)` along the absolutely continuous `Ab`. -/
theorem pointwise_identity {a : ℝ} (ha : 0 < a) (haδ : a ≤ D.δ0) {y : Vec d} (hy : y ∈ D.K)
    {t : ℝ} (ht : t ∈ Icc D.p D.q) :
    D.φ (y, t) ^ 4 * qf (D.A y) (D.Abv a (y, t)) (D.Abv a (y, t)) =
      ∫ τ in D.p..t, (4 * D.φ (y, τ) ^ 3 * parTimeDeriv D.φ (y, τ) *
          qf (D.A y) (D.Abv a (y, τ)) (D.Abv a (y, τ)) +
        2 * D.φ (y, τ) ^ 4 * qf (D.A y) (D.Abv a (y, τ)) (D.Zbv a (y, τ))) := by
  have hS : ∀ i j, symmPart (D.A y) i j = symmPart (D.A y) j i := fun i j => by
    simp only [symmPart]; ring
  have hint : ∀ i, IntervalIntegrable (D.Zb i a y) volume D.p t := fun i =>
    (D.hZint a ha haδ y hy i).mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le (ht.1.trans ht.2)]; exact Icc_subset_Icc_right ht.2)
  have hα : ∀ i, ∀ τ ∈ Icc D.p t, D.Ab i a y τ = D.Ab i a y D.p + ∫ σ in D.p..τ, D.Zb i a y σ := by
    intro i τ hτ
    have := D.hAC a ha haδ y hy i D.p τ le_rfl hτ.1 (hτ.2.trans ht.2)
    linarith
  have hch := chain_quad (s := D.p) (t := t) ht.1 hS (ψ := fun τ => D.φ (y, τ) ^ 2)
    ((D.contDiff_timeSlice y).pow 2) (α := fun i τ => D.Ab i a y τ) (D := fun i τ => D.Zb i a y τ)
    hint hα
  simp only [D.deriv_timeSlice_sq, D.hφp y hy, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_mul, sub_zero] at hch
  have e1 : ∀ τ, qf (D.A y) (D.Abv a (y, τ)) (D.Abv a (y, τ)) =
      ∑ i, ∑ j, symmPart (D.A y) i j * (D.Ab i a y τ * D.Ab j a y τ) := fun τ =>
    qf_eq_sum (D.A y) (D.Abv a (y, τ)) (D.Abv a (y, τ))
  have e2 : ∀ τ, qf (D.A y) (D.Abv a (y, τ)) (D.Zbv a (y, τ)) =
      ∑ i, ∑ j, symmPart (D.A y) i j * (D.Ab i a y τ * D.Zb j a y τ) := fun τ =>
    qf_eq_sum (D.A y) (D.Abv a (y, τ)) (D.Zbv a (y, τ))
  simp only [e1, e2]
  have h4 : (D.φ (y, t) ^ 2) ^ 2 = D.φ (y, t) ^ 4 := by ring
  rw [h4] at hch
  rw [hch]
  refine intervalIntegral.integral_congr fun τ _ => ?_
  ring


/-- Almost everywhere in the slab, `Ab` and `Zb` are the slice-wise mollifications of `W`, `Z`. -/
theorem ae_Ab_eq {t : ℝ} (ht : t ≤ D.q) : ∀ᵐ z ∂(D.μ t), ∀ a : ℝ, 0 < a → a ≤ D.δ0 → ∀ i,
    D.Ab i a z.1 z.2 = mollT a D.K1 (D.W i) z ∧ D.Zb i a z.1 z.2 = mollT a D.K1 (D.Z i) z := by
  rw [μ_eq]
  have h1 : ∀ᵐ τ ∂(volume.restrict (Ioc D.p t)), ∀ x : Vec d, x ∈ D.K → ∀ a : ℝ, 0 < a →
      a ≤ D.δ0 → ∀ i, D.Ab i a x τ = mollT a D.K1 (D.W i) (x, τ) ∧
        D.Zb i a x τ = mollT a D.K1 (D.Z i) (x, τ) := by
    have hsub : Ioc D.p t ⊆ Ioc D.p D.q := Ioc_subset_Ioc_right ht
    have hA := ae_restrict_of_ae_restrict_of_subset hsub D.hAb
    have hZ := ae_restrict_of_ae_restrict_of_subset hsub D.hZb
    filter_upwards [hA, hZ] with τ h1 h2 x hx a ha haδ i
    exact ⟨h1 a ha haδ x hx i, h2 a ha haδ x hx i⟩
  have h2 := ae_prod_of_ae_slice (μ := volume.restrict D.K) (P := fun x τ => x ∈ D.K → ∀ a : ℝ,
    0 < a → a ≤ D.δ0 → ∀ i, D.Ab i a x τ = mollT a D.K1 (D.W i) (x, τ) ∧
        D.Zb i a x τ = mollT a D.K1 (D.Z i) (x, τ)) (by
    filter_upwards [h1] with τ hτ x hx using hτ x hx)
  have h3 : ∀ᵐ x ∂(volume.restrict D.K), x ∈ D.K := ae_restrict_mem D.K_measurable
  have h4 : ∀ᵐ z ∂((volume.restrict D.K).prod (volume.restrict (Ioc D.p t))), z.1 ∈ D.K :=
    (Measure.quasiMeasurePreserving_fst (μ := volume.restrict D.K)
      (ν := volume.restrict (Ioc D.p t))).ae h3
  filter_upwards [h2, h4] with z hz hz1
  exact hz hz1

theorem memLp_Ab {t : ℝ} (ht : t ≤ D.q) {a : ℝ} (ha : 0 < a) (haδ : a ≤ D.δ0) (i : Fin d) :
    MemLp (fun z : Vec d × ℝ => D.Ab i a z.1 z.2) 2 (D.μ t) ∧
      MemLp (fun z : Vec d × ℝ => D.Zb i a z.1 z.2) 2 (D.μ t) := by
  have hW' : MemLp (D.W i) 2 (volume.restrict (D.K1 ×ˢ Ioc D.p t)) :=
    (D.hW2 i).mono_measure
      (Measure.restrict_mono (prod_mono subset_rfl (Ioc_subset_Ioc_right ht)) le_rfl)
  have hZ' : MemLp (D.Z i) 2 (volume.restrict (D.K1 ×ˢ Ioc D.p t)) :=
    (D.hZ2 i).mono_measure
      (Measure.restrict_mono (prod_mono subset_rfl (Ioc_subset_Ioc_right ht)) le_rfl)
  have hae := D.ae_Ab_eq ht
  constructor
  · refine (memLp_mollT D.K1_compact hW' ha).ae_eq ?_
    filter_upwards [hae] with z hz using (hz a ha haδ i).1.symm
  · refine (memLp_mollT D.K1_compact hZ' ha).ae_eq ?_
    filter_upwards [hae] with z hz using (hz a ha haδ i).2.symm

theorem memLp_W {t : ℝ} (ht : t ≤ D.q) (i : Fin d) :
    MemLp (D.W i) 2 (D.μ t) ∧ MemLp (D.Z i) 2 (D.μ t) := by
  have := fun g (hg : MemLp g 2 (volume.restrict (D.K1 ×ˢ Ioc D.p D.q))) =>
    (D.conv_mollT ht hg).1
  exact ⟨this _ (D.hW2 i), this _ (D.hZ2 i)⟩


/-- `E_a(t) = ∫_K φ⁴ Q(Ab_a(·,t))`. -/
noncomputable def Eab (a t : ℝ) : ℝ :=
  ∫ x in D.K, D.φ (x, t) ^ 4 * qf (D.A x) (D.Abv a (x, t)) (D.Abv a (x, t))

/-- The time derivative of the integrand, at scale `a`. -/
noncomputable def gA (a : ℝ) (z : Vec d × ℝ) : ℝ :=
  4 * D.φ z ^ 3 * parTimeDeriv D.φ z * qf (D.A z.1) (D.Abv a z) (D.Abv a z) +
    2 * D.φ z ^ 4 * qf (D.A z.1) (D.Abv a z) (D.Zbv a z)

/-- The upper bound for `gA`, with parameter `ε`. -/
noncomputable def rA (ε : ℝ) (a : ℝ) (z : Vec d × ℝ) : ℝ :=
  (4 * |D.φ z| ^ 3 * |parTimeDeriv D.φ z| + ε⁻¹ * D.φ z ^ 4) *
      qf (D.A z.1) (D.Abv a z) (D.Abv a z) +
    ε * D.φ z ^ 4 * qf (D.A z.1) (D.Zbv a z) (D.Zbv a z)

theorem continuous_w1 : Continuous fun z : Vec d × ℝ => 4 * D.φ z ^ 3 * parTimeDeriv D.φ z :=
  (continuous_const.mul (D.continuous_phi.pow 3)).mul D.continuous_timeDeriv

theorem continuous_w2 (c : ℝ) : Continuous fun z : Vec d × ℝ => c * D.φ z ^ 4 :=
  continuous_const.mul (D.continuous_phi.pow 4)

theorem continuous_w3 (ε : ℝ) : Continuous fun z : Vec d × ℝ =>
    4 * |D.φ z| ^ 3 * |parTimeDeriv D.φ z| + ε⁻¹ * D.φ z ^ 4 :=
  ((continuous_const.mul (D.continuous_phi.abs.pow 3)).mul D.continuous_timeDeriv.abs).add
    (D.continuous_w2 _)

theorem integrable_gA {t : ℝ} (ht : t ≤ D.q) {a : ℝ} (ha : 0 < a) (haδ : a ≤ D.δ0) :
    Integrable (D.gA a) (D.μ t) := by
  obtain ⟨M1, hM1⟩ := D.ae_bound_weight D.continuous_w1 ht
  obtain ⟨M2, hM2⟩ := D.ae_bound_weight (D.continuous_w2 2) ht
  have hA := fun i => (D.memLp_Ab ht ha haδ i).1
  have hZ := fun i => (D.memLp_Ab ht ha haδ i).2
  have h1 := D.integrable_qf (t := t) D.continuous_w1.aestronglyMeasurable hM1 hA hA
  have h2 := D.integrable_qf (t := t) (D.continuous_w2 2).aestronglyMeasurable hM2 hA hZ
  exact h1.add h2

theorem integrable_rA {t : ℝ} (ht : t ≤ D.q) {ε : ℝ} {a : ℝ} (ha : 0 < a) (haδ : a ≤ D.δ0) :
    Integrable (D.rA ε a) (D.μ t) := by
  obtain ⟨M1, hM1⟩ := D.ae_bound_weight (D.continuous_w3 ε) ht
  obtain ⟨M2, hM2⟩ := D.ae_bound_weight (D.continuous_w2 ε) ht
  have hA := fun i => (D.memLp_Ab ht ha haδ i).1
  have hZ := fun i => (D.memLp_Ab ht ha haδ i).2
  have h1 := D.integrable_qf (t := t) (D.continuous_w3 ε).aestronglyMeasurable hM1 hA hA
  have h2 := D.integrable_qf (t := t) (D.continuous_w2 ε).aestronglyMeasurable hM2 hZ hZ
  have := h1.add h2
  refine this.congr (Eventually.of_forall fun z => ?_)
  rfl

theorem Eab_eq {t : ℝ} (ht : t ∈ Icc D.p D.q) {a : ℝ} (ha : 0 < a) (haδ : a ≤ D.δ0) :
    D.Eab a t = ∫ z, D.gA a z ∂(D.μ t) := by
  have hint := D.integrable_gA ht.2 ha haδ
  calc D.Eab a t = ∫ x in D.K, ∫ τ in D.p..t, D.gA a (x, τ) := by
        refine setIntegral_congr_fun D.K_measurable fun x hx => ?_
        exact D.pointwise_identity ha haδ hx ht
    _ = ∫ z, D.gA a z ∂(D.μ t) := by
        rw [μ_eq] at hint ⊢
        rw [integral_prod _ hint]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only
        rw [intervalIntegral.integral_of_le ht.1]

theorem gA_le_rA {t : ℝ} {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    ∀ᵐ z ∂(D.μ t), D.gA a z ≤ D.rA ε a z := by
  filter_upwards [D.ae_elliptic (t := t)] with z hz
  have hy := qf_young hz (D.Abv a z) (D.Zbv a z) hε
  have h1 := qf_self_nonneg hz (D.Abv a z)
  have h2 : 0 ≤ D.φ z ^ 4 := by positivity
  have h3 : 4 * D.φ z ^ 3 * parTimeDeriv D.φ z ≤ 4 * |D.φ z| ^ 3 * |parTimeDeriv D.φ z| := by
    have : D.φ z ^ 3 * parTimeDeriv D.φ z ≤ |D.φ z| ^ 3 * |parTimeDeriv D.φ z| := by
      calc D.φ z ^ 3 * parTimeDeriv D.φ z ≤ |D.φ z ^ 3 * parTimeDeriv D.φ z| := le_abs_self _
        _ = |D.φ z| ^ 3 * |parTimeDeriv D.φ z| := by rw [abs_mul, abs_pow]
    linarith
  unfold gA rA
  have h4 := mul_le_mul_of_nonneg_right h3 h1
  have h5 := mul_le_mul_of_nonneg_left hy h2
  nlinarith [h4, h5]

theorem Eab_le {t : ℝ} (ht : t ∈ Icc D.p D.q) {ε : ℝ} (hε : 0 < ε) {a : ℝ} (ha : 0 < a)
    (haδ : a ≤ D.δ0) : D.Eab a t ≤ ∫ z, D.rA ε a z ∂(D.μ t) := by
  rw [D.Eab_eq ht ha haδ]
  exact integral_mono_ae (D.integrable_gA ht.2 ha haδ) (D.integrable_rA ht.2 ha haδ)
    (D.gA_le_rA hε a)


/-! ### Weighted limits of quadratic forms -/

theorem weight_term_aesm {ν : Measure (Vec d × ℝ)} (hν : ν ≤ D.μ D.q) {ω : Vec d × ℝ → ℝ}
    (hω : Continuous ω) (i j : Fin d) :
    AEStronglyMeasurable (fun z => ω z * symmPart (D.A z.1) i j) ν :=
  hω.aestronglyMeasurable.mul
    ((D.aemeasurable_A (t := D.q) i j).mono_measure hν).aestronglyMeasurable

theorem weight_term_bound {ν : Measure (Vec d × ℝ)} (hν : ν ≤ D.μ D.q) {ω : Vec d × ℝ → ℝ}
    (hω : Continuous ω) : ∃ M : ℝ, ∀ i j, ∀ᵐ z ∂ν, |ω z * symmPart (D.A z.1) i j| ≤ M := by
  obtain ⟨M, hM⟩ := D.ae_bound_weight hω le_rfl
  refine ⟨M * D.Lam, fun i j => ?_⟩
  have h1 := (ae_mono hν) hM
  have h2 := (ae_mono hν) (D.ae_entry_bound (t := D.q))
  filter_upwards [h1, h2] with z hz1 hz2
  rw [abs_mul]
  exact mul_le_mul hz1 (hz2 i j) (abs_nonneg _) ((abs_nonneg _).trans hz1)

theorem integral_weight_qf {ν : Measure (Vec d × ℝ)} (hν : ν ≤ D.μ D.q) {ω : Vec d × ℝ → ℝ}
    (hω : Continuous ω) {F G : Fin d → Vec d × ℝ → ℝ} (hF : ∀ i, MemLp (F i) 2 ν)
    (hG : ∀ i, MemLp (G i) 2 ν) :
    ∫ z, ω z * qf (D.A z.1) (fun i => F i z) (fun i => G i z) ∂ν =
      ∑ i, ∑ j, ∫ z, (ω z * symmPart (D.A z.1) i j) * F i z * G j z ∂ν := by
  obtain ⟨M, hM⟩ := D.weight_term_bound hν hω
  have hq : ∀ z, ω z * qf (D.A z.1) (fun i => F i z) (fun i => G i z) =
      ∑ i, ∑ j, (ω z * symmPart (D.A z.1) i j) * F i z * G j z := by
    intro z
    rw [qf_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hint : ∀ i j, Integrable (fun z => (ω z * symmPart (D.A z.1) i j) * F i z * G j z) ν :=
    fun i j => integrable_weight_mul (D.weight_term_aesm hν hω i j) (hM i j) (hF i) (hG j)
  simp_rw [hq]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hint i j]

theorem tendsto_weight_qf {ν : Measure (Vec d × ℝ)} (hν : ν ≤ D.μ D.q) {ω : Vec d × ℝ → ℝ}
    (hω : Continuous ω) {F G : ℕ → Fin d → Vec d × ℝ → ℝ} {F0 G0 : Fin d → Vec d × ℝ → ℝ}
    (hF : ∀ n i, MemLp (F n i) 2 ν) (hG : ∀ n i, MemLp (G n i) 2 ν)
    (hF0 : ∀ i, MemLp (F0 i) 2 ν) (hG0 : ∀ i, MemLp (G0 i) 2 ν)
    (hFl : ∀ i, Tendsto (fun n => eLpNorm (F n i - F0 i) 2 ν) atTop (𝓝 0))
    (hGl : ∀ i, Tendsto (fun n => eLpNorm (G n i - G0 i) 2 ν) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, ω z * qf (D.A z.1) (fun i => F n i z) (fun i => G n i z) ∂ν) atTop
      (𝓝 (∫ z, ω z * qf (D.A z.1) (fun i => F0 i z) (fun i => G0 i z) ∂ν)) := by
  obtain ⟨M, hM⟩ := D.weight_term_bound hν hω
  simp_rw [D.integral_weight_qf hν hω (hF _) (hG _), D.integral_weight_qf hν hω hF0 hG0]
  refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
  exact tendsto_integral_weight_mul_of_L2 (D.weight_term_aesm hν hω i j) (hM i j)
    (fun n => hF n i) (fun n => hG n j) (hF0 i) (hG0 j) (hFl i) (hGl j)


/-- The limiting energy `E(t) = ∫_K φ⁴ Q(W(·,t))`. -/
noncomputable def Eu (t : ℝ) : ℝ :=
  ∫ x in D.K, D.φ (x, t) ^ 4 * qf (D.A x) (D.Wv (x, t)) (D.Wv (x, t))

/-- The limiting upper bound integrand. -/
noncomputable def r0 (ε : ℝ) (z : Vec d × ℝ) : ℝ :=
  (4 * |D.φ z| ^ 3 * |parTimeDeriv D.φ z| + ε⁻¹ * D.φ z ^ 4) * qf (D.A z.1) (D.Wv z) (D.Wv z) +
    ε * D.φ z ^ 4 * qf (D.A z.1) (D.Zv z) (D.Zv z)

theorem tendsto_Ab (i : Fin d) :
    Tendsto (fun n => eLpNorm ((fun z : Vec d × ℝ => D.Ab i (D.aSeq n) z.1 z.2) - D.W i) 2
        (D.μ D.q)) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm ((fun z : Vec d × ℝ => D.Zb i (D.aSeq n) z.1 z.2) - D.Z i) 2
        (D.μ D.q)) atTop (𝓝 0) := by
  have hae := D.ae_Ab_eq (le_refl D.q)
  constructor
  · refine ((D.conv_mollT le_rfl (D.hW2 i)).2.2).congr fun n => ?_
    refine eLpNorm_congr_ae ?_
    filter_upwards [hae] with z hz
    simp only [Pi.sub_apply]
    rw [(hz (D.aSeq n) (D.aSeq_pos n) (D.aSeq_le_δ0 n) i).1]
  · refine ((D.conv_mollT le_rfl (D.hZ2 i)).2.2).congr fun n => ?_
    refine eLpNorm_congr_ae ?_
    filter_upwards [hae] with z hz
    simp only [Pi.sub_apply]
    rw [(hz (D.aSeq n) (D.aSeq_pos n) (D.aSeq_le_δ0 n) i).2]

theorem tendsto_rA (ε : ℝ) :
    Tendsto (fun n => ∫ z, D.rA ε (D.aSeq n) z ∂(D.μ D.q)) atTop
      (𝓝 (∫ z, D.r0 ε z ∂(D.μ D.q))) := by
  have hle : D.μ D.q ≤ D.μ D.q := le_rfl
  have hA := fun n i => (D.memLp_Ab le_rfl (D.aSeq_pos n) (D.aSeq_le_δ0 n) i).1
  have hZ := fun n i => (D.memLp_Ab le_rfl (D.aSeq_pos n) (D.aSeq_le_δ0 n) i).2
  have hW := fun i => (D.memLp_W le_rfl i).1
  have hZ0 := fun i => (D.memLp_W le_rfl i).2
  have t1 := D.tendsto_weight_qf hle (D.continuous_w3 ε)
    (F := fun n i z => D.Ab i (D.aSeq n) z.1 z.2) (G := fun n i z => D.Ab i (D.aSeq n) z.1 z.2)
    hA hA hW hW (fun i => (D.tendsto_Ab i).1) (fun i => (D.tendsto_Ab i).1)
  have t2 := D.tendsto_weight_qf hle (D.continuous_w2 ε)
    (F := fun n i z => D.Zb i (D.aSeq n) z.1 z.2) (G := fun n i z => D.Zb i (D.aSeq n) z.1 z.2)
    hZ hZ hZ0 hZ0 (fun i => (D.tendsto_Ab i).2) (fun i => (D.tendsto_Ab i).2)
  obtain ⟨M1, hM1⟩ := D.ae_bound_weight (D.continuous_w3 ε) (le_refl D.q)
  obtain ⟨M2, hM2⟩ := D.ae_bound_weight (D.continuous_w2 ε) (le_refl D.q)
  have i1 : ∀ n, Integrable (fun z => (4 * |D.φ z| ^ 3 * |parTimeDeriv D.φ z| + ε⁻¹ * D.φ z ^ 4) *
      qf (D.A z.1) (fun i => D.Ab i (D.aSeq n) z.1 z.2) (fun i => D.Ab i (D.aSeq n) z.1 z.2))
      (D.μ D.q) := fun n =>
    D.integrable_qf (D.continuous_w3 ε).aestronglyMeasurable hM1 (hA n) (hA n)
  have i2 : ∀ n, Integrable (fun z => ε * D.φ z ^ 4 *
      qf (D.A z.1) (fun i => D.Zb i (D.aSeq n) z.1 z.2) (fun i => D.Zb i (D.aSeq n) z.1 z.2))
      (D.μ D.q) := fun n =>
    D.integrable_qf (D.continuous_w2 ε).aestronglyMeasurable hM2 (hZ n) (hZ n)
  have i3 : Integrable (fun z => (4 * |D.φ z| ^ 3 * |parTimeDeriv D.φ z| + ε⁻¹ * D.φ z ^ 4) *
      qf (D.A z.1) (fun i => D.W i z) (fun i => D.W i z)) (D.μ D.q) :=
    D.integrable_qf (D.continuous_w3 ε).aestronglyMeasurable hM1 hW hW
  have i4 : Integrable (fun z => ε * D.φ z ^ 4 *
      qf (D.A z.1) (fun i => D.Z i z) (fun i => D.Z i z)) (D.μ D.q) :=
    D.integrable_qf (D.continuous_w2 ε).aestronglyMeasurable hM2 hZ0 hZ0
  have := t1.add t2
  have e1 : ∀ n, ∫ z, D.rA ε (D.aSeq n) z ∂(D.μ D.q) =
      (∫ z, (4 * |D.φ z| ^ 3 * |parTimeDeriv D.φ z| + ε⁻¹ * D.φ z ^ 4) *
        qf (D.A z.1) (fun i => D.Ab i (D.aSeq n) z.1 z.2) (fun i => D.Ab i (D.aSeq n) z.1 z.2)
          ∂(D.μ D.q)) +
      ∫ z, ε * D.φ z ^ 4 *
        qf (D.A z.1) (fun i => D.Zb i (D.aSeq n) z.1 z.2) (fun i => D.Zb i (D.aSeq n) z.1 z.2)
          ∂(D.μ D.q) := fun n => integral_add (i1 n) (i2 n)
  have e0 : ∫ z, D.r0 ε z ∂(D.μ D.q) =
      (∫ z, (4 * |D.φ z| ^ 3 * |parTimeDeriv D.φ z| + ε⁻¹ * D.φ z ^ 4) *
        qf (D.A z.1) (fun i => D.W i z) (fun i => D.W i z) ∂(D.μ D.q)) +
      ∫ z, ε * D.φ z ^ 4 * qf (D.A z.1) (fun i => D.Z i z) (fun i => D.Z i z) ∂(D.μ D.q) :=
    integral_add i3 i4
  rw [e0]
  exact this.congr fun n => (e1 n).symm


theorem restrict_le {T : Set ℝ} (hTsub : T ⊆ Ioc D.p D.q) :
    (volume.restrict (D.K ×ˢ T) : Measure (Vec d × ℝ)) ≤ D.μ D.q :=
  Measure.restrict_mono (prod_mono subset_rfl hTsub) le_rfl

/-- Fubini on `K × T`. -/
theorem fubini_T {T : Set ℝ} (hTsub : T ⊆ Ioc D.p D.q) {F G : Fin d → Vec d × ℝ → ℝ}
    (hF : ∀ i, MemLp (F i) 2 (D.μ D.q)) (hG : ∀ i, MemLp (G i) 2 (D.μ D.q)) :
    ∫ τ in T, ∫ x in D.K, D.φ (x, τ) ^ 4 * qf (D.A x) (fun i => F i (x, τ)) (fun i => G i (x, τ)) =
      ∫ z, D.φ z ^ 4 * qf (D.A z.1) (fun i => F i z) (fun i => G i z)
        ∂(volume.restrict (D.K ×ˢ T)) := by
  obtain ⟨M, hM⟩ := D.ae_bound_weight (D.continuous_phi.pow 4) (le_refl D.q)
  have hint : Integrable (fun z => D.φ z ^ 4 * qf (D.A z.1) (fun i => F i z) (fun i => G i z))
      (volume.restrict (D.K ×ˢ T)) :=
    (D.integrable_qf (D.continuous_phi.pow 4).aestronglyMeasurable hM hF hG).mono_measure
      (D.restrict_le hTsub)
  rw [volume_restrict_prod] at hint ⊢
  rw [integral_prod_symm _ hint]

theorem tendsto_setIntegral_Eab {T : Set ℝ} (hTsub : T ⊆ Ioc D.p D.q) :
    Tendsto (fun n => ∫ τ in T, D.Eab (D.aSeq n) τ) atTop (𝓝 (∫ τ in T, D.Eu τ)) := by
  have hν := D.restrict_le hTsub
  have hA := fun n i => (D.memLp_Ab le_rfl (D.aSeq_pos n) (D.aSeq_le_δ0 n) i).1
  have hW := fun i => (D.memLp_W le_rfl i).1
  have h := D.tendsto_weight_qf hν (D.continuous_phi.pow 4)
    (F := fun n i z => D.Ab i (D.aSeq n) z.1 z.2) (G := fun n i z => D.Ab i (D.aSeq n) z.1 z.2)
    (F0 := D.W) (G0 := D.W)
    (fun n i => (hA n i).mono_measure hν) (fun n i => (hA n i).mono_measure hν)
    (fun i => (hW i).mono_measure hν) (fun i => (hW i).mono_measure hν)
    (fun i => tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (D.tendsto_Ab i).1
      (fun n => bot_le) (fun n => eLpNorm_mono_measure _ hν))
    (fun i => tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (D.tendsto_Ab i).1
      (fun n => bot_le) (fun n => eLpNorm_mono_measure _ hν))
  have e1 : ∀ n, ∫ τ in T, D.Eab (D.aSeq n) τ = ∫ z, D.φ z ^ 4 *
      qf (D.A z.1) (fun i => D.Ab i (D.aSeq n) z.1 z.2) (fun i => D.Ab i (D.aSeq n) z.1 z.2)
        ∂(volume.restrict (D.K ×ˢ T)) := fun n =>
    D.fubini_T hTsub (F := fun i z => D.Ab i (D.aSeq n) z.1 z.2)
      (G := fun i z => D.Ab i (D.aSeq n) z.1 z.2) (hA n) (hA n)
  have e0 : ∫ τ in T, D.Eu τ = ∫ z, D.φ z ^ 4 *
      qf (D.A z.1) (fun i => D.W i z) (fun i => D.W i z) ∂(volume.restrict (D.K ×ˢ T)) :=
    D.fubini_T hTsub hW hW
  rw [e0]
  exact h.congr fun n => (e1 n).symm


theorem integrable_slice_T {T : Set ℝ} (hTsub : T ⊆ Ioc D.p D.q) {F G : Fin d → Vec d × ℝ → ℝ}
    (hF : ∀ i, MemLp (F i) 2 (D.μ D.q)) (hG : ∀ i, MemLp (G i) 2 (D.μ D.q)) :
    Integrable (fun τ => ∫ x in D.K,
      D.φ (x, τ) ^ 4 * qf (D.A x) (fun i => F i (x, τ)) (fun i => G i (x, τ)))
      (volume.restrict T) := by
  obtain ⟨M, hM⟩ := D.ae_bound_weight (D.continuous_phi.pow 4) (le_refl D.q)
  have hint : Integrable (fun z => D.φ z ^ 4 * qf (D.A z.1) (fun i => F i z) (fun i => G i z))
      (volume.restrict (D.K ×ˢ T)) :=
    (D.integrable_qf (D.continuous_phi.pow 4).aestronglyMeasurable hM hF hG).mono_measure
      (D.restrict_le hTsub)
  rw [volume_restrict_prod] at hint
  exact hint.integral_prod_right

theorem eab_le_total {t : ℝ} (ht : t ∈ Icc D.p D.q) {ε : ℝ} (hε : 0 < ε) {a : ℝ} (ha : 0 < a)
    (haδ : a ≤ D.δ0) : D.Eab a t ≤ ∫ z, D.rA ε a z ∂(D.μ D.q) := by
  refine (D.Eab_le ht hε ha haδ).trans ?_
  refine integral_mono_measure ?_ ?_ (D.integrable_rA le_rfl ha haδ)
  · exact Measure.restrict_mono (prod_mono subset_rfl (Ioc_subset_Ioc_right ht.2)) le_rfl
  · filter_upwards [D.ae_elliptic (t := D.q)] with z hz
    have h1 := qf_self_nonneg hz (D.Abv a z)
    have h2 := qf_self_nonneg hz (D.Zbv a z)
    have h3 : 0 ≤ 4 * |D.φ z| ^ 3 * |parTimeDeriv D.φ z| + ε⁻¹ * D.φ z ^ 4 := by positivity
    have h4 : 0 ≤ ε * D.φ z ^ 4 := by positivity
    unfold rA
    positivity

theorem volume_T_ne_top {T : Set ℝ} (hTsub : T ⊆ Ioc D.p D.q) : volume T ≠ ⊤ :=
  ((measure_mono hTsub).trans_lt (by simp)).ne

theorem setIntegral_Eu_le {T : Set ℝ} (hT : MeasurableSet T) (hTsub : T ⊆ Ioc D.p D.q) {ε : ℝ}
    (hε : 0 < ε) :
    ∫ τ in T, D.Eu τ ≤ (∫ z, D.r0 ε z ∂(D.μ D.q)) * (volume T).toReal := by
  have hlim := D.tendsto_setIntegral_Eab hTsub
  have hR := (D.tendsto_rA ε).mul_const (volume T).toReal
  have hA := fun n i => (D.memLp_Ab le_rfl (D.aSeq_pos n) (D.aSeq_le_δ0 n) i).1
  refine le_of_tendsto_of_tendsto' hlim hR fun n => ?_
  have hint := D.integrable_slice_T hTsub (hA n) (hA n)
  have h1 : ∫ τ in T, D.Eab (D.aSeq n) τ ≤
      ∫ τ in T, ∫ z, D.rA ε (D.aSeq n) z ∂(D.μ D.q) := by
    refine setIntegral_mono_on hint (integrableOn_const (D.volume_T_ne_top hTsub)) hT ?_
    intro τ hτ
    exact D.eab_le_total ⟨(hTsub hτ).1.le, (hTsub hτ).2⟩ hε (D.aSeq_pos n) (D.aSeq_le_δ0 n)
  refine h1.trans (le_of_eq ?_)
  rw [setIntegral_const, smul_eq_mul, mul_comm, Measure.real]

/-- **The mollified time-energy estimate**: for a.e. `t`, `E(t) ≤ ∫_{K×(p,q]} r`. -/
theorem time_energy {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ t ∂(volume.restrict (Ioc D.p D.q)), D.Eu t ≤ ∫ z, D.r0 ε z ∂(D.μ D.q) := by
  have hW := fun i => (D.memLp_W le_rfl i).1
  have hEint : Integrable D.Eu (volume.restrict (Ioc D.p D.q)) :=
    D.integrable_slice_T (subset_refl _) hW hW
  refine ae_le_of_forall_setIntegral_le hEint (integrable_const _) fun s hs _ => ?_
  rw [Measure.restrict_restrict hs]
  have hT : MeasurableSet (s ∩ Ioc D.p D.q) := hs.inter measurableSet_Ioc
  have := D.setIntegral_Eu_le hT (inter_subset_right (s := s)) hε
  rw [setIntegral_const, smul_eq_mul, Measure.real, mul_comm]
  exact this

end EData

end PDE.Parabolic.Slice
