module

public import EllipticRegularity.Parabolic.Energy.Mollifier
public import EllipticRegularity.Parabolic.Energy.Limits

/-!
# Slice-wise mollification on a space-time slab

`mollT a K1 g` mollifies, at every time, the restriction of `g(·, τ)` to `K1`.  We prove joint
measurability for Borel `g`, a.e.-slice congruence, and `L²` convergence on `K ×ˢ J` as `a → 0`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.Energy

open MeasureTheory Set Filter Topology

variable {d : ℕ}

/-- Mollification in space of the restriction to `K1`, at every time. -/
noncomputable def mollT (a : ℝ) (K1 : Set (Vec d)) (g : Vec d × ℝ → ℝ) (z : Vec d × ℝ) : ℝ :=
  wholeSpaceMollify a (K1.indicator (fun y => g (y, z.2))) z.1

theorem mollT_eq (a : ℝ) (K1 : Set (Vec d)) (g : Vec d × ℝ → ℝ) (z : Vec d × ℝ) :
    mollT a K1 g z = ∫ y, kern a (z.1 - y) * K1.indicator (fun y => g (y, z.2)) y :=
  moll_eq _ _ _

theorem stronglyMeasurable_mollT {K1 : Set (Vec d)} (hK1 : MeasurableSet K1) {g : Vec d × ℝ → ℝ}
    (hg : Measurable g) (a : ℝ) : StronglyMeasurable (mollT a K1 g) := by
  have hF : Measurable fun p : (Vec d × ℝ) × Vec d =>
      kern a (p.1.1 - p.2) * K1.indicator (fun y => g (y, p.1.2)) p.2 := by
    have h1 : Measurable fun p : (Vec d × ℝ) × Vec d => kern a (p.1.1 - p.2) :=
      (kern_continuous a).measurable.comp (measurable_fst.fst.sub measurable_snd)
    have h2 : Measurable fun p : (Vec d × ℝ) × Vec d => K1.indicator (fun y => g (y, p.1.2)) p.2 := by
      have : (fun p : (Vec d × ℝ) × Vec d => K1.indicator (fun y => g (y, p.1.2)) p.2) =
          {p : (Vec d × ℝ) × Vec d | p.2 ∈ K1}.indicator (fun p => g (p.2, p.1.2)) := by
        funext p
        by_cases h : p.2 ∈ K1 <;> simp [h]
      rw [this]
      exact (hg.comp (measurable_snd.prodMk measurable_fst.snd)).indicator
        (hK1.preimage measurable_snd)
    exact h1.mul h2
  have := hF.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (Vec d)))
  have h3 : mollT a K1 g = fun z => ∫ y, kern a (z.1 - y) * K1.indicator (fun y => g (y, z.2)) y :=
    funext (mollT_eq a K1 g)
  rw [h3]
  exact this

theorem mollT_ae_slice {K1 : Set (Vec d)} (hK1 : MeasurableSet K1) {J : Set ℝ}
    {g ĝ : Vec d × ℝ → ℝ} (hg : g =ᵐ[volume.restrict (K1 ×ˢ J)] ĝ) (a : ℝ) :
    ∀ᵐ τ ∂(volume.restrict J), ∀ x, mollT a K1 g (x, τ) = mollT a K1 ĝ (x, τ) := by
  have h1 : ∀ᵐ z ∂((volume.restrict K1).prod (volume.restrict J)), g z = ĝ z := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]; exact hg
  filter_upwards [ae_ae_swap h1] with τ hτ x
  rw [mollT_eq, mollT_eq]
  refine integral_congr_ae ?_
  have := (ae_restrict_iff' hK1).1 hτ
  filter_upwards [this] with y hy
  by_cases hyK : y ∈ K1
  · simp [hyK, hy hyK]
  · simp [hyK]

theorem lintegral_enorm_sq_eq {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℝ}
    (hf : AEStronglyMeasurable f μ) :
    ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ = eLpNorm f 2 μ ^ (2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  simp only [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_mul]
  norm_num

theorem volume_restrict_prod (K : Set (Vec d)) (J : Set ℝ) :
    (volume : Measure (Vec d × ℝ)).restrict (K ×ˢ J) =
      (volume.restrict K).prod (volume.restrict J) := by
  rw [Measure.volume_eq_prod, Measure.prod_restrict]

/-- Almost every time slice of an `L²` function on a slab is in `L²` (after cutting off to `K1`). -/
theorem ae_slice_memLp {K1 : Set (Vec d)} (hK1 : MeasurableSet K1) {J : Set ℝ}
    {g : Vec d × ℝ → ℝ} (hg : MemLp g 2 (volume.restrict (K1 ×ˢ J))) :
    ∀ᵐ τ ∂(volume.restrict J), MemLp (K1.indicator fun y => g (y, τ)) 2 volume := by
  have hgm := hg.aestronglyMeasurable
  have hĝ := hgm.stronglyMeasurable_mk
  have hgĝ := hgm.ae_eq_mk
  have h1 : ∀ᵐ z ∂((volume.restrict K1).prod (volume.restrict J)), g z = hgm.mk g z := by
    rw [← volume_restrict_prod]; exact hgĝ
  have hsl := ae_ae_swap h1
  have hprod : ∫⁻ z, ‖g z‖ₑ ^ (2 : ℝ) ∂((volume.restrict K1).prod (volume.restrict J)) ≠ ⊤ := by
    rw [← volume_restrict_prod, lintegral_enorm_sq_eq hgm]
    exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hg.eLpNorm_lt_top.ne).ne
  have hgm' : AEStronglyMeasurable g ((volume.restrict K1).prod (volume.restrict J)) := by
    rw [← volume_restrict_prod]; exact hgm
  have hmeas : AEMeasurable (fun τ => ∫⁻ y, ‖g (y, τ)‖ₑ ^ (2 : ℝ) ∂(volume.restrict K1))
      (volume.restrict J) :=
    AEMeasurable.lintegral_prod_left' (hgm'.aemeasurable.enorm.pow_const (2 : ℝ))
  have hfin := ae_lt_top' hmeas (by
    rw [← lintegral_prod_symm _ (hgm'.aemeasurable.enorm.pow_const (2 : ℝ))]; exact hprod)
  filter_upwards [hsl, hfin] with τ hτ hτfin
  have hmeas' : AEStronglyMeasurable (K1.indicator fun y => g (y, τ)) volume := by
    rw [aestronglyMeasurable_indicator_iff hK1]
    have hm : AEStronglyMeasurable (fun y => hgm.mk g (y, τ)) (volume.restrict K1) :=
      (hĝ.measurable.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    exact hm.congr (hτ.mono fun y hy => hy.symm)
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hmeas']
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
  simp only [ENNReal.toReal_ofNat]
  have : ∫⁻ y, ‖K1.indicator (fun y => g (y, τ)) y‖ₑ ^ (2 : ℝ) =
      ∫⁻ y in K1, ‖g (y, τ)‖ₑ ^ (2 : ℝ) := by
    rw [← lintegral_indicator hK1]
    congr 1; funext y
    by_cases hy : y ∈ K1 <;> simp [hy]
  rw [this]
  exact hτfin.ne

theorem aestronglyMeasurable_mollT {K1 : Set (Vec d)} (hK1 : MeasurableSet K1) {J : Set ℝ}
    (S : Set (Vec d)) {g : Vec d × ℝ → ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict (K1 ×ˢ J))) (a : ℝ) :
    AEStronglyMeasurable (mollT a K1 g) (volume.restrict (S ×ˢ J)) := by
  rw [volume_restrict_prod]
  have hĝ := hg.stronglyMeasurable_mk
  have hae : ∀ᵐ z ∂((volume.restrict S).prod (volume.restrict J)),
      mollT a K1 g z = mollT a K1 (hg.mk g) z :=
    ae_prod_of_ae_slice (P := fun x τ => mollT a K1 g (x, τ) = mollT a K1 (hg.mk g) (x, τ))
      (mollT_ae_slice hK1 hg.ae_eq_mk a)
  exact ((stronglyMeasurable_mollT hK1 hĝ.measurable a).aestronglyMeasurable).congr
    (hae.mono fun z hz => hz.symm)

/-- The mollified slice minus the slice, on `K`, is bounded by the global `L²` error. -/
theorem slice_core {K K1 : Set (Vec d)} (hKK1 : K ⊆ K1) (hKm : MeasurableSet K)
    {g : Vec d × ℝ → ℝ} {τ a : ℝ} (ha : 0 < a)
    (hf : MemLp (K1.indicator fun y => g (y, τ)) 2 volume) :
    ∫⁻ x in K, ‖mollT a K1 g (x, τ) - g (x, τ)‖ₑ ^ (2 : ℝ) ≤
      eLpNorm (wholeSpaceMollify a (K1.indicator fun y => g (y, τ)) -
        (K1.indicator fun y => g (y, τ))) 2 volume ^ (2 : ℝ) := by
  set f := K1.indicator fun y => g (y, τ) with hfdef
  have hloc : LocallyIntegrable f volume := hf.locallyIntegrable (by norm_num)
  have hmoll : AEStronglyMeasurable (wholeSpaceMollify a f) volume :=
    (moll_contDiff ha hloc).continuous.aestronglyMeasurable
  rw [← lintegral_enorm_sq_eq (hmoll.sub hf.aestronglyMeasurable)]
  calc ∫⁻ x in K, ‖mollT a K1 g (x, τ) - g (x, τ)‖ₑ ^ (2 : ℝ)
      = ∫⁻ x in K, ‖wholeSpaceMollify a f x - f x‖ₑ ^ (2 : ℝ) := by
        refine setLIntegral_congr_fun hKm fun x hx => ?_
        have : f x = g (x, τ) := by simp [hfdef, Set.indicator_of_mem (hKK1 hx)]
        show ‖wholeSpaceMollify a f x - g (x, τ)‖ₑ ^ (2 : ℝ) = _
        rw [this]
    _ ≤ ∫⁻ x, ‖(wholeSpaceMollify a f - f) x‖ₑ ^ (2 : ℝ) := by
        simpa using setLIntegral_le_lintegral (μ := volume) K
          (fun x => ‖(wholeSpaceMollify a f - f) x‖ₑ ^ (2 : ℝ))

theorem eLpNorm_moll_le {a : ℝ} (ha : 0 < a) {f : Vec d → ℝ} (hf : MemLp f 2 volume) :
    MemLp (wholeSpaceMollify a f) 2 volume ∧
      eLpNorm (wholeSpaceMollify a f) 2 volume ≤ eLpNorm f 2 volume := by
  have hc := (contDiff_memLp_convolution_scaledConvexApproxKernel
    (isConvexApproxKernel_unitConvexApproxKernel (d := d)) ha (p := 2) (by norm_num)
    (by norm_num) hf)
  exact ⟨hc.2.1, hc.2.2⟩

theorem eLpNorm_moll_sub_le {a : ℝ} (ha : 0 < a) {f : Vec d → ℝ} (hf : MemLp f 2 volume) :
    eLpNorm (wholeSpaceMollify a f - f) 2 volume ≤ 2 * eLpNorm f 2 volume := by
  have hc := eLpNorm_moll_le ha hf
  calc eLpNorm (wholeSpaceMollify a f - f) 2 volume
      ≤ eLpNorm (wholeSpaceMollify a f) 2 volume + eLpNorm f 2 volume :=
        eLpNorm_sub_le (by norm_num)
    _ ≤ eLpNorm f 2 volume + eLpNorm f 2 volume := add_le_add hc.2 le_rfl
    _ = 2 * eLpNorm f 2 volume := by rw [two_mul]

theorem lintegral_indicator_enorm_sq {K1 : Set (Vec d)} (hK1 : MeasurableSet K1)
    (h : Vec d → ℝ) :
    ∫⁻ y, ‖K1.indicator h y‖ₑ ^ (2 : ℝ) = ∫⁻ y in K1, ‖h y‖ₑ ^ (2 : ℝ) := by
  rw [← lintegral_indicator hK1]
  congr 1; funext y
  by_cases hy : y ∈ K1 <;> simp [hy]

/-- `L²` convergence of slice-wise mollifications on a slab. -/
theorem tendsto_lintegral_mollT {K K1 : Set (Vec d)} (hK1 : IsCompact K1) (hKK1 : K ⊆ K1)
    (hKm : MeasurableSet K) {J : Set ℝ} {g : Vec d × ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (K1 ×ˢ J))) {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (ha1 : ∀ n, a n ≤ 1) (ha0 : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ z in K ×ˢ J, ‖mollT (a n) K1 g z - g z‖ₑ ^ (2 : ℝ)) atTop (𝓝 0) := by
  have hK1m : MeasurableSet K1 := hK1.measurableSet
  have hgm := hg.aestronglyMeasurable
  have hĝ := hgm.stronglyMeasurable_mk
  have hgĝ := hgm.ae_eq_mk
  set ĝ := hgm.mk g with hĝdef
  set F : ℕ → Vec d × ℝ → ℝ≥0∞ := fun n z => ‖mollT (a n) K1 g z - g z‖ₑ ^ (2 : ℝ) with hF
  have hsub : K ×ˢ J ⊆ K1 ×ˢ J := prod_mono hKK1 subset_rfl
  have hgK : AEStronglyMeasurable g (volume.restrict (K ×ˢ J)) :=
    hgm.mono_measure (Measure.restrict_mono hsub le_rfl)
  rw [volume_restrict_prod] at hgK ⊢
  have hae : ∀ n, ∀ᵐ z ∂((volume.restrict K).prod (volume.restrict J)),
      mollT (a n) K1 g z = mollT (a n) K1 ĝ z := by
    intro n
    apply ae_prod_of_ae_slice (P := fun x τ => mollT (a n) K1 g (x, τ) = mollT (a n) K1 ĝ (x, τ))
    exact mollT_ae_slice hK1m hgĝ (a n)
  have hFm : ∀ n, AEMeasurable (F n) ((volume.restrict K).prod (volume.restrict J)) := by
    intro n
    have h1 : AEStronglyMeasurable (fun z => mollT (a n) K1 ĝ z - g z)
        ((volume.restrict K).prod (volume.restrict J)) :=
      ((stronglyMeasurable_mollT hK1m hĝ.measurable (a n)).aestronglyMeasurable).sub hgK
    have h2 : AEMeasurable (fun z => ‖mollT (a n) K1 ĝ z - g z‖ₑ ^ (2 : ℝ))
        ((volume.restrict K).prod (volume.restrict J)) := h1.aemeasurable.enorm.pow_const _
    refine h2.congr ?_
    filter_upwards [hae n] with z hz
    simp only [hF, hz]
  have hswap : ∀ n, ∫⁻ z, F n z ∂((volume.restrict K).prod (volume.restrict J)) =
      ∫⁻ τ, ∫⁻ x, F n (x, τ) ∂(volume.restrict K) ∂(volume.restrict J) :=
    fun n => lintegral_prod_symm _ (hFm n)
  have hgood := ae_slice_memLp hK1m hg
  have hgm' : AEStronglyMeasurable g ((volume.restrict K1).prod (volume.restrict J)) := by
    rw [← volume_restrict_prod]; exact hgm
  have hgsq : AEMeasurable (fun z => ‖g z‖ₑ ^ (2 : ℝ))
      ((volume.restrict K1).prod (volume.restrict J)) := hgm'.aemeasurable.enorm.pow_const _
  have hbfin : ∫⁻ τ, (4 * ∫⁻ y in K1, ‖g (y, τ)‖ₑ ^ (2 : ℝ)) ∂(volume.restrict J) ≠ ⊤ := by
    rw [lintegral_const_mul' _ _ (by norm_num), ← lintegral_prod_symm _ hgsq,
      ← volume_restrict_prod, lintegral_enorm_sq_eq hgm]
    exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hg.eLpNorm_lt_top.ne).ne
  show Tendsto (fun n => ∫⁻ z, F n z ∂((volume.restrict K).prod (volume.restrict J))) atTop (𝓝 0)
  simp only [hswap]
  have hDCT := tendsto_lintegral_of_dominated_convergence'
    (μ := volume.restrict J) (F := fun n τ => ∫⁻ x, F n (x, τ) ∂(volume.restrict K))
    (f := fun _ => (0 : ℝ≥0∞))
    (fun τ => 4 * ∫⁻ y in K1, ‖g (y, τ)‖ₑ ^ (2 : ℝ))
    (fun n => (hFm n).lintegral_prod_left') ?_ hbfin ?_
  · simpa using hDCT
  · intro n
    filter_upwards [hgood] with τ hτ
    have hc := slice_core hKK1 hKm (g := g) (τ := τ) (ha n) hτ
    have hm := eLpNorm_moll_sub_le (ha n) hτ
    refine le_trans hc ?_
    calc eLpNorm (wholeSpaceMollify (a n) (K1.indicator fun y => g (y, τ)) -
          (K1.indicator fun y => g (y, τ))) 2 volume ^ (2 : ℝ)
        ≤ (2 * eLpNorm (K1.indicator fun y => g (y, τ)) 2 volume) ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow hm (by norm_num)
      _ = 4 * eLpNorm (K1.indicator fun y => g (y, τ)) 2 volume ^ (2 : ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.rpow_two]
          norm_num
      _ = 4 * ∫⁻ y in K1, ‖g (y, τ)‖ₑ ^ (2 : ℝ) := by
          rw [← lintegral_enorm_sq_eq hτ.aestronglyMeasurable, lintegral_indicator_enorm_sq hK1m]
  · filter_upwards [hgood] with τ hτ
    have hlim := tendsto_eLpNorm_wholeSpaceMollify_sub (p := 2) (by norm_num) (by norm_num) hτ ha ha1 ha0
    have hsq : Tendsto (fun n => eLpNorm (wholeSpaceMollify (a n) (K1.indicator fun y => g (y, τ)) -
          (K1.indicator fun y => g (y, τ))) 2 volume ^ (2 : ℝ)) atTop (𝓝 0) := by
      have := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0).comp hlim
      rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsq (fun n => bot_le)
      (fun n => ?_)
    exact slice_core hKK1 hKm (g := g) (τ := τ) (ha n) hτ

/-- Mollified slices are bounded in `L²(K×J)` by the `L²(K1×J)` norm of the data. -/
theorem memLp_mollT {K K1 : Set (Vec d)} (hK1 : IsCompact K1) {J : Set ℝ}
    {g : Vec d × ℝ → ℝ} (hg : MemLp g 2 (volume.restrict (K1 ×ˢ J))) {a : ℝ} (ha : 0 < a) :
    MemLp (mollT a K1 g) 2 (volume.restrict (K ×ˢ J)) := by
  have hK1m : MeasurableSet K1 := hK1.measurableSet
  have hgm := hg.aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (mollT a K1 g) (volume.restrict (K ×ˢ J)) :=
    aestronglyMeasurable_mollT hK1m K hgm a
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hmeas]
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
  simp only [ENNReal.toReal_ofNat]
  rw [volume_restrict_prod]
  have hmeas' : AEStronglyMeasurable (mollT a K1 g)
      ((volume.restrict K).prod (volume.restrict J)) := by
    rw [← volume_restrict_prod]; exact hmeas
  have hgm' : AEStronglyMeasurable g ((volume.restrict K1).prod (volume.restrict J)) := by
    rw [← volume_restrict_prod]; exact hgm
  rw [lintegral_prod_symm _ (hmeas'.aemeasurable.enorm.pow_const _)]
  have hgood := ae_slice_memLp hK1m hg
  have hle : ∀ᵐ τ ∂(volume.restrict J), ∫⁻ x, ‖mollT a K1 g (x, τ)‖ₑ ^ (2 : ℝ) ∂(volume.restrict K) ≤
      ∫⁻ y, ‖g (y, τ)‖ₑ ^ (2 : ℝ) ∂(volume.restrict K1) := by
    filter_upwards [hgood] with τ hτ
    set f := K1.indicator fun y => g (y, τ) with hfdef
    have hc := eLpNorm_moll_le ha hτ
    calc ∫⁻ x, ‖mollT a K1 g (x, τ)‖ₑ ^ (2 : ℝ) ∂(volume.restrict K)
        ≤ ∫⁻ x, ‖wholeSpaceMollify a f x‖ₑ ^ (2 : ℝ) := setLIntegral_le_lintegral _ _
      _ = eLpNorm (wholeSpaceMollify a f) 2 volume ^ (2 : ℝ) :=
          lintegral_enorm_sq_eq hc.1.aestronglyMeasurable
      _ ≤ eLpNorm f 2 volume ^ (2 : ℝ) := ENNReal.rpow_le_rpow hc.2 (by norm_num)
      _ = ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) := (lintegral_enorm_sq_eq hτ.aestronglyMeasurable).symm
      _ = ∫⁻ y in K1, ‖g (y, τ)‖ₑ ^ (2 : ℝ) := lintegral_indicator_enorm_sq hK1m _
  refine ne_of_lt (lt_of_le_of_lt (lintegral_mono_ae hle) ?_)
  rw [← lintegral_prod_symm _ (hgm'.aemeasurable.enorm.pow_const _), ← volume_restrict_prod,
    lintegral_enorm_sq_eq hgm]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hg.eLpNorm_lt_top.ne

theorem tendsto_eLpNorm_sub_of_lintegral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {F : ℕ → X → ℝ} {F0 : X → ℝ} (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hF0 : AEStronglyMeasurable F0 μ)
    (h : Tendsto (fun n => ∫⁻ x, ‖F n x - F0 x‖ₑ ^ (2 : ℝ) ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n - F0) 2 μ) atTop (𝓝 0) := by
  have h1 : ∀ n, eLpNorm (F n - F0) 2 μ = (∫⁻ x, ‖F n x - F0 x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    intro n
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) ((hF n).sub hF0)]
    simp
  simp only [h1]
  have := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp h
  rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at this

end PDE.Parabolic.Energy
