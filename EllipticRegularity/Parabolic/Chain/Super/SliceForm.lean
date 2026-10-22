/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.Chain.Super.H1Supersolution
public import EllipticRegularity.Parabolic.Chain.Super.LebesgueRamp
public import EllipticRegularity.Parabolic.Chain.Super.SlabIntegrable

/-! # The slice form of the supersolution renormalization inequality -/

@[expose] public section

namespace PDE.Parabolic.Chain.Super

open MeasureTheory Set Filter Topology PDE PDE.Parabolic.WeakSlice PDE.Parabolic.Chain

variable {d : ℕ} {lam Lam : ℝ} {U : Set (Vec d)} {I : Set ℝ} {a : ParCoeffField d}

theorem parTimeDeriv_snd {θ : ℝ → ℝ} (hθ : ContDiff ℝ 1 θ) (z : Vec d × ℝ) :
    parTimeDeriv (fun w : Vec d × ℝ => θ w.2) z = deriv θ z.2 := by
  have := parTimeDeriv_prod (d := d) hθ (contDiff_const (c := (1 : ℝ))) z
  simpa using this

theorem parSpaceGrad_snd {θ : ℝ → ℝ} (hθ : ContDiff ℝ 1 θ) (z : Vec d × ℝ) :
    parSpaceGrad (fun w : Vec d × ℝ => θ w.2) z = 0 := by
  have := parSpaceGrad_prod (d := d) hθ (contDiff_const (c := (1 : ℝ))) z
  have h0 : spaceGradC1 (fun _ : Vec d => (1 : ℝ)) z.1 = 0 := by
    ext i; simp [spaceGradC1]
  simpa [h0] using this

/-- Multiplying the weight by a time cutoff `θ` changes the renormalized integrand by the
term `-F(u) φ θ'`. -/
theorem renormalizedIntegrand_timeCutoff {U : Set (Vec d)} {I : Set ℝ} (u : ParH1Function U I)
    {F : ℝ → ℝ} {φ : Vec d × ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {θ : ℝ → ℝ} (hθ : ContDiff ℝ 1 θ)
    (z : Vec d × ℝ) :
    renormalizedIntegrand a u F (fun w => θ w.2 * φ w) z =
      θ z.2 * renormalizedIntegrand a u F φ z - F (u.toFun z) * φ z * deriv θ z.2 := by
  have hθ' : ContDiff ℝ 1 (fun w : Vec d × ℝ => θ w.2) := hθ.comp contDiff_snd
  have h1 := parTimeDeriv_mul hθ' hφ z
  have h2 := parSpaceGrad_mul hθ' hφ z
  rw [parTimeDeriv_snd hθ, parSpaceGrad_snd hθ] at *
  unfold renormalizedIntegrand
  rw [h1, h2, smul_zero, zero_add, vecDot_smul_right]
  ring

/-- The slice pairing `τ ↦ ∫_U F(u(x,τ)) φ(x,τ) dx`. -/
noncomputable def slicePairingF {U : Set (Vec d)} {I : Set ℝ} (u : ParH1Function U I)
    (F : ℝ → ℝ) (φ : Vec d × ℝ → ℝ) (τ : ℝ) : ℝ :=
  ∫ x in U, F (u.toFun (x, τ)) * φ (x, τ)

theorem abs_deriv_trap_le {p q ε M : ℝ} (hε : 0 < ε) (hM : ∀ x, |rampDeriv x| ≤ M) (τ : ℝ) :
    |deriv (trap p q ε) τ| ≤ 2 * (ε⁻¹ * M) := by
  rw [(trap_hasDerivAt hε τ).deriv]
  have h1 : ε⁻¹ * |rampDeriv ((τ - (p + 1 * ε)) / ε)| ≤ ε⁻¹ * M :=
    mul_le_mul_of_nonneg_left (hM _) (inv_pos.2 hε).le
  have h2 : ε⁻¹ * |rampDeriv ((τ - (q + (-2) * ε)) / ε)| ≤ ε⁻¹ * M :=
    mul_le_mul_of_nonneg_left (hM _) (inv_pos.2 hε).le
  calc |ε⁻¹ * rampDeriv ((τ - (p + 1 * ε)) / ε) - ε⁻¹ * rampDeriv ((τ - (q + (-2) * ε)) / ε)|
      ≤ |ε⁻¹ * rampDeriv ((τ - (p + 1 * ε)) / ε)| +
        |ε⁻¹ * rampDeriv ((τ - (q + (-2) * ε)) / ε)| := abs_sub _ _
    _ ≤ 2 * (ε⁻¹ * M) := by
      rw [abs_mul, abs_mul, abs_of_pos (inv_pos.2 hε)]
      linarith

section

variable {F : ℝ → ℝ} {φ : Vec d × ℝ → ℝ} {K : Set (Vec d)}

/-- The inequality of Target 1 for the weight `θ_ε(τ) φ(x,τ)`, in slice form. -/
theorem slice_epsilon_inequality (hU : IsOpen U) (hI : I.OrdConnected)
    (ha : IsParabolicCoeff lam Lam a U I) (u : ParH1Function U I)
    (hu : IsParabolicWeakSupersolution a U I u)
    (hF : ContDiff ℝ 2 F) (hFLip : ∃ C : NNReal, LipschitzWith C F)
    (hF'bound : ∃ C : NNReal, ∀ s, |deriv F s| ≤ C)
    (hF''bound : ∃ C : NNReal, ∀ s, |deriv (deriv F) s| ≤ C)
    (hFmono : ∀ s, 0 ≤ deriv F s)
    (hφ : ContDiff ℝ 1 φ) (hφ0 : ∀ z, 0 ≤ φ z) (hK : IsCompact K) (hKU : K ⊆ U)
    (hφK : ∀ x ∉ K, ∀ τ, φ (x, τ) = 0) {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) (hst : s < t)
    {ε : ℝ} (hε : 0 < ε) (h4 : 4 * ε ≤ t - s) :
    ∫ τ in Ioc s t, slicePairingF u F φ τ * deriv (trap s t ε) τ ≤
      ∫ z in U ×ˢ Ioc s t, trap s t ε z.2 * renormalizedIntegrand a u F φ z := by
  have h3 : 3 * ε ≤ t - s := by linarith
  set θ := trap s t ε with hθdef
  have hθC : ContDiff ℝ 1 θ := trap_contDiff
  have hθ0 : ∀ τ, 0 ≤ θ τ := trap_nonneg h3 hε
  have hθ1 : ∀ τ, θ τ ≤ 1 := fun τ => trap_le_one τ
  have hIcc : Icc s t ⊆ I := hI.out hs ht
  have hIoo : Ioo s t ⊆ interior I := interior_maximal (Ioo_subset_Icc_self.trans hIcc) isOpen_Ioo
  -- the test function
  have hsuppK : Function.support (fun w : Vec d × ℝ => θ w.2 * φ w) ⊆
      K ×ˢ Icc (s + ε) (t - ε) := by
    intro w hw
    have hw' : θ w.2 ≠ 0 ∧ φ w ≠ 0 := mul_ne_zero_iff.1 hw
    refine ⟨?_, ?_⟩
    · by_contra hx
      exact hw'.2 (by simpa using hφK w.1 hx w.2)
    · refine ⟨?_, ?_⟩
      · by_contra h; exact hw'.1 (trap_eq_zero_of_lt h3 hε (not_le.1 h))
      · by_contra h; exact hw'.1 (trap_eq_zero_of_gt h3 hε (by linarith [not_le.1 h]))
  have hcs : HasCompactSupport (fun w : Vec d × ℝ => θ w.2 * φ w) :=
    HasCompactSupport.of_support_subset_isCompact (hK.prod isCompact_Icc) hsuppK
  have hts : tsupport (fun w : Vec d × ℝ => θ w.2 * φ w) ⊆ U ×ˢ Ioo s t := by
    have : tsupport (fun w : Vec d × ℝ => θ w.2 * φ w) ⊆ K ×ˢ Icc (s + ε) (t - ε) :=
      closure_minimal hsuppK (hK.isClosed.prod isClosed_Icc)
    refine this.trans (prod_mono hKU ?_)
    intro τ hτ
    exact ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  let φε : ParTestFunction U (interior I) :=
    { toFun := fun w => θ w.2 * φ w
      contDiff := (hθC.comp contDiff_snd).mul hφ
      hasCompactSupport := hcs
      tsupport_subset := hts.trans (prod_mono subset_rfl hIoo) }
  obtain ⟨_, hge⟩ := weak_supersolution_renormalization_H1 hU hI ha u hu F hF hFLip hF'bound
    hF''bound hFmono φε (fun z => mul_nonneg (hθ0 _) (hφ0 _)) hs ht hst hts
  have hR : IntegrableOn (renormalizedIntegrand a u F φ) (U ×ˢ Ioc s t) :=
    integrableOn_renormalizedIntegrand hU ha u hF hFLip hF'bound hF''bound hφ hK hKU hφK hIcc
      Ioc_subset_Icc_self measurableSet_Ioc
  have hg : IntegrableOn (fun z => F (u.toFun z) * φ z) (U ×ˢ Ioc s t) :=
    integrableOn_Fu_mul hU u hFLip hφ.continuous hK hKU hφK hIcc Ioc_subset_Icc_self
      measurableSet_Ioc
  obtain ⟨M, hM0, hM⟩ := exists_abs_rampDeriv_le
  have hθ'b : ∀ τ, |deriv θ τ| ≤ 2 * (ε⁻¹ * M) := abs_deriv_trap_le hε hM
  have hθ'c : Continuous (deriv θ) := hθC.continuous_deriv le_rfl
  have hRθ : IntegrableOn (fun z => θ z.2 * renormalizedIntegrand a u F φ z)
      (U ×ˢ Ioc s t) := by
    have := hR.bdd_mul (f := fun z : Vec d × ℝ => θ z.2) (c := 1)
      (hθC.continuous.comp continuous_snd).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hθ0 _)]; exact hθ1 _)
    exact this
  have hgθ : IntegrableOn (fun z => F (u.toFun z) * φ z * deriv θ z.2) (U ×ˢ Ioc s t) :=
    hg.mul_bdd (c := 2 * (ε⁻¹ * M)) (hθ'c.comp continuous_snd).aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hθ'b _)
  have hpt : ∀ z, renormalizedIntegrand a u F φε.toFun z =
      θ z.2 * renormalizedIntegrand a u F φ z - F (u.toFun z) * φ z * deriv θ z.2 :=
    fun z => renormalizedIntegrand_timeCutoff u hφ hθC z
  have hge' : 0 ≤ ∫ z in U ×ˢ Ioc s t, (θ z.2 * renormalizedIntegrand a u F φ z -
      F (u.toFun z) * φ z * deriv θ z.2) := by
    simpa only [hpt] using hge
  rw [integral_sub hRθ hgθ] at hge'
  have hFub : ∫ z in U ×ˢ Ioc s t, F (u.toFun z) * φ z * deriv θ z.2 =
      ∫ τ in Ioc s t, slicePairingF u F φ τ * deriv θ τ := by
    obtain ⟨_, h⟩ := integral_prod_slices hgθ
    rw [h]
    refine setIntegral_congr_fun measurableSet_Ioc fun τ _ => ?_
    simp only [slicePairingF]
    exact integral_mul_const _ _
  rw [hFub] at hge'
  linarith

end

end PDE.Parabolic.Chain.Super

namespace PDE.Parabolic.Chain

open MeasureTheory Set Filter Topology PDE PDE.Parabolic.WeakSlice PDE.Parabolic.Chain.Super

variable {d : ℕ} {lam Lam : ℝ} {U : Set (Vec d)} {I : Set ℝ} {a : ParCoeffField d}

/-- The slice form of the renormalization inequality for `H¹`-parabolic weak supersolutions:
for almost every `s < t` in `I`,
`∫_U F(u(t)) φ(t) - ∫_U F(u(s)) φ(s) ≥ ∫∫_{U × (s,t]} [F(u) ∂ₜφ - F''(u) φ a∇u·∇u - F'(u) a∇u·∇φ]`.
The weight `φ ≥ 0` is `C¹` and vanishes outside a compact lateral set `K ⊆ U`; it need not vanish
at the time endpoints. -/
theorem weak_supersolution_renormalization_slice (hU : IsOpen U) (hI : I.OrdConnected)
    (ha : IsParabolicCoeff lam Lam a U I) (u : ParH1Function U I)
    (hu : IsParabolicWeakSupersolution a U I u)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hFLip : ∃ C : NNReal, LipschitzWith C F)
    (hF'bound : ∃ C : NNReal, ∀ s, |deriv F s| ≤ C)
    (hF''bound : ∃ C : NNReal, ∀ s, |deriv (deriv F) s| ≤ C)
    (hFmono : ∀ s, 0 ≤ deriv F s)
    (φ : Vec d × ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) (hφ0 : ∀ z, 0 ≤ φ z)
    {K : Set (Vec d)} (hK : IsCompact K) (hKU : K ⊆ U) (hφK : ∀ x ∉ K, ∀ τ, φ (x, τ) = 0) :
    ∃ N : Set ℝ, volume N = 0 ∧ ∀ s t : ℝ, s ∈ I → t ∈ I → s ∉ N → t ∉ N → s < t →
      IntegrableOn (fun z => F (u.toFun z) * parTimeDeriv φ z -
        deriv (deriv F) (u.toFun z) * φ z * vecDot (matVecMul (a z) (u.grad z)) (u.grad z) -
        deriv F (u.toFun z) * vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad φ z))
        (U ×ˢ Ioc s t) ∧
      IntegrableOn (fun x => F (u.toFun (x, s)) * φ (x, s)) U ∧
      IntegrableOn (fun x => F (u.toFun (x, t)) * φ (x, t)) U ∧
      (∫ z in U ×ˢ Ioc s t, (F (u.toFun z) * parTimeDeriv φ z -
        deriv (deriv F) (u.toFun z) * φ z * vecDot (matVecMul (a z) (u.grad z)) (u.grad z) -
        deriv F (u.toFun z) * vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad φ z))) ≤
      (∫ x in U, F (u.toFun (x, t)) * φ (x, t)) - ∫ x in U, F (u.toFun (x, s)) * φ (x, s) := by
  have hm : ∀ p ∈ I, ∀ q ∈ I, IntegrableOn (slicePairingF u F φ) (Icc p q) := by
    intro p hp q hq
    rcases le_or_gt p q with hpq | hpq
    · have hg := integrableOn_Fu_mul hU u hFLip hφ.continuous hK hKU hφK (hI.out hp hq)
        (subset_refl _) measurableSet_Icc
      exact (integral_prod_slices hg).1
    · rw [Icc_eq_empty (not_le.2 hpq)]
      exact integrableOn_empty
  obtain ⟨N, hN0, hN⟩ := exists_null_set_isLebPt hI hm
  refine ⟨N, hN0, fun s t hs ht hsN htN hst => ?_⟩
  obtain ⟨hLs, rs, hrs, hints⟩ := hN s hs hsN
  obtain ⟨hLt, rt, hrt, hintt⟩ := hN t ht htN
  have hIcc : Icc s t ⊆ I := hI.out hs ht
  have hR : IntegrableOn (renormalizedIntegrand a u F φ) (U ×ˢ Ioc s t) :=
    integrableOn_renormalizedIntegrand hU ha u hF hFLip hF'bound hF''bound hφ hK hKU hφK hIcc
      Ioc_subset_Icc_self measurableSet_Ioc
  have hexp : ∀ z, (F (u.toFun z) * parTimeDeriv φ z -
        deriv (deriv F) (u.toFun z) * φ z * vecDot (matVecMul (a z) (u.grad z)) (u.grad z) -
        deriv F (u.toFun z) * vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad φ z)) =
      -renormalizedIntegrand a u F φ z := by
    intro z; unfold renormalizedIntegrand; ring
  simp only [hexp]
  refine ⟨hR.neg, integrableOn_slice_Fu_mul hU u hFLip hφ.continuous hK hKU hφK hs,
    integrableOn_slice_Fu_mul hU u hFLip hφ.continuous hK hKU hφK ht, ?_⟩
  rw [integral_neg]
  set A := ∫ z in U ×ˢ Ioc s t, renormalizedIntegrand a u F φ z with hA
  have hmst : IntegrableOn (slicePairingF u F φ) (Icc s t) := hm s hs t ht
  -- the two ramp limits
  have hBs := tendsto_ramp_of_isLebPt hLs hrs hints (κ := 1) (by norm_num)
  have hBt := tendsto_ramp_of_isLebPt hLt hrt hintt (κ := -2) (by norm_num)
  have hevε : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ 4 * ε ≤ t - s := by
    filter_upwards [Ioc_mem_nhdsGT (by linarith : (0 : ℝ) < (t - s) / 4)] with ε hε
    exact ⟨hε.1, by linarith [hε.2]⟩
  -- the cutoff integrals
  have hAlim : Tendsto (fun ε : ℝ => ∫ z in U ×ˢ Ioc s t,
      trap s t ε z.2 * renormalizedIntegrand a u F φ z) (𝓝[>] 0) (𝓝 A) := by
    have hnull : ∀ᵐ z ∂(volume.restrict (U ×ˢ Ioc s t)), z.2 ≠ t := by
      refine ae_restrict_of_ae ?_
      have hz : volume {z : Vec d × ℝ | z.2 = t} = 0 := by
        have : {z : Vec d × ℝ | z.2 = t} = (univ : Set (Vec d)) ×ˢ {t} := by
          ext z; simp
        rw [this, Measure.volume_eq_prod, Measure.prod_prod]
        simp
      exact measure_eq_zero_iff_ae_notMem.1 hz
    refine tendsto_integral_filter_of_dominated_convergence (fun z => ‖renormalizedIntegrand a u F φ z‖)
      ?_ ?_ hR.norm ?_
    · exact Eventually.of_forall fun ε =>
        ((trap_contDiff.continuous.comp continuous_snd).aestronglyMeasurable).mul
          hR.aestronglyMeasurable
    · filter_upwards [hevε] with ε ⟨hε, h4⟩
      refine Eventually.of_forall fun z => ?_
      have h3 : 3 * ε ≤ t - s := by linarith
      rw [norm_mul, Real.norm_eq_abs (trap s t ε z.2), abs_of_nonneg (trap_nonneg h3 hε _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (trap_le_one _)
    · filter_upwards [hnull, ae_restrict_mem (hU.measurableSet.prod measurableSet_Ioc)] with z hz1 hz2
      have hz3 : z.2 ∈ Ioo s t := ⟨hz2.2.1, lt_of_le_of_ne hz2.2.2 hz1⟩
      have hpos : 0 < min (z.2 - s) (t - z.2) :=
        lt_min (by linarith [hz3.1]) (by linarith [hz3.2])
      have hD1 := min_le_left (z.2 - s) (t - z.2)
      have hD2 := min_le_right (z.2 - s) (t - z.2)
      refine (tendsto_const_nhds (x := renormalizedIntegrand a u F φ z)).congr' ?_
      filter_upwards [Ioc_mem_nhdsGT (by linarith : (0 : ℝ) < min (z.2 - s) (t - z.2) / 4),
        hevε] with ε hε ⟨hε0, h4⟩
      have h3 : 3 * ε ≤ t - s := by linarith
      rw [trap_eq_one h3 hε0 (by linarith [hε.2]) (by linarith [hε.2]), one_mul]
  have hBeq : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ∫ τ in Ioc s t, slicePairingF u F φ τ * deriv (trap s t ε) τ =
        (∫ τ, slicePairingF u F φ τ * (ε⁻¹ * rampDeriv ((τ - (s + 1 * ε)) / ε))) -
          ∫ τ, slicePairingF u F φ τ * (ε⁻¹ * rampDeriv ((τ - (t + (-2) * ε)) / ε)) := by
    filter_upwards [hevε] with ε ⟨hε, h4⟩
    have h3 : 3 * ε ≤ t - s := by linarith
    have hws : Icc (s + 1 * ε) (s + 1 * ε + ε) ⊆ Icc s t := fun τ hτ =>
      ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have hwt : Icc (t + (-2) * ε) (t + (-2) * ε + ε) ⊆ Icc s t := fun τ hτ =>
      ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have i1 := integrable_mul_ramp hε hmst hws
    have i2 := integrable_mul_ramp hε hmst hwt
    rw [← integral_sub i1 i2]
    have hz : ∀ τ, τ ∉ Ioc s t → slicePairingF u F φ τ * deriv (trap s t ε) τ = 0 := by
      intro τ hτ
      have hnot : τ ∉ tsupport (trap s t ε) := fun h => hτ (by
        have := tsupport_trap_subset h3 hε h
        exact ⟨by linarith [this.1], by linarith [this.2]⟩)
      have hd : deriv (trap s t ε) τ = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hnot (tsupport_deriv_subset h))
      rw [hd, mul_zero]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    simp only []
    rw [(trap_hasDerivAt hε τ).deriv]
    ring
  have hlim := hAlim.sub (hBs.sub hBt)
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 ≤
      (∫ z in U ×ˢ Ioc s t, trap s t ε z.2 * renormalizedIntegrand a u F φ z) -
        ((∫ τ, slicePairingF u F φ τ * (ε⁻¹ * rampDeriv ((τ - (s + 1 * ε)) / ε))) -
          ∫ τ, slicePairingF u F φ τ * (ε⁻¹ * rampDeriv ((τ - (t + (-2) * ε)) / ε))) := by
    filter_upwards [hevε, hBeq] with ε ⟨hε, h4⟩ hb
    rw [← hb]
    have := slice_epsilon_inequality hU hI ha u hu hF hFLip hF'bound hF''bound hFmono hφ hφ0 hK
      hKU hφK hs ht hst hε h4
    linarith
  have hfinal := ge_of_tendsto hlim hev
  have e1 : slicePairingF u F φ t = ∫ x in U, F (u.toFun (x, t)) * φ (x, t) := rfl
  have e2 : slicePairingF u F φ s = ∫ x in U, F (u.toFun (x, s)) * φ (x, s) := rfl
  rw [← e1, ← e2]
  linarith

end PDE.Parabolic.Chain
