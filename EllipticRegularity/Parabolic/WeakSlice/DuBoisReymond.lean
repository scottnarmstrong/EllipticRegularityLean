module

public import EllipticRegularity.Parabolic.WeakSlice.Ramp

/-!
# A du Bois-Reymond step

For continuous `m : ℝ → ℝ` and `g` integrable on `(p, q)`, if `∫ m θ' = ∫ g θ` over `(p, q)` for
all `C¹` compactly supported `θ` with `tsupport θ ⊆ (p, q)`, then `m p - m q = ∫_{(p,q)} g`.
-/

@[expose] public section

namespace PDE.Parabolic.WeakSlice

open MeasureTheory Set Filter Topology

/-- The trapezoid test function with `C¹` ramps of width `ε`. -/
noncomputable def trap (p q ε : ℝ) (τ : ℝ) : ℝ :=
  Real.smoothTransition ((τ - (p + ε)) / ε) - Real.smoothTransition ((τ - (q - 2 * ε)) / ε)

section
variable {p q ε : ℝ}

theorem trap_contDiff : ContDiff ℝ 1 (trap p q ε) := by
  unfold trap
  have h := Real.smoothTransition.contDiff (n := 1)
  exact (h.comp (by fun_prop)).sub (h.comp (by fun_prop))

theorem trap_hasDerivAt (_hε : 0 < ε) (τ : ℝ) :
    HasDerivAt (trap p q ε) (ε⁻¹ * rampDeriv ((τ - (p + 1 * ε)) / ε)
      - ε⁻¹ * rampDeriv ((τ - (q + (-2) * ε)) / ε)) τ := by
  unfold trap
  have h1 := (rampDeriv_hasDerivAt ((τ - (p + ε)) / ε)).comp τ
    (((hasDerivAt_id τ).sub_const (p + ε)).div_const ε)
  have h2 := (rampDeriv_hasDerivAt ((τ - (q - 2 * ε)) / ε)).comp τ
    (((hasDerivAt_id τ).sub_const (q - 2 * ε)).div_const ε)
  refine (h1.sub h2).congr_deriv ?_
  rw [one_mul, show q + (-2) * ε = q - 2 * ε by ring]
  ring

theorem trap_eq_zero_of_lt (h3 : 3 * ε ≤ q - p) (hε : 0 < ε) {τ : ℝ} (hτ : τ < p + ε) :
    trap p q ε τ = 0 := by
  unfold trap
  have a1 : (τ - (p + ε)) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  have a2 : (τ - (q - 2 * ε)) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  rw [Real.smoothTransition.zero_of_nonpos a1, Real.smoothTransition.zero_of_nonpos a2]; simp

theorem trap_eq_zero_of_gt (h3 : 3 * ε ≤ q - p) (hε : 0 < ε) {τ : ℝ} (hτ : q - ε < τ) :
    trap p q ε τ = 0 := by
  unfold trap
  have a1 : 1 ≤ (τ - (p + ε)) / ε := by rw [le_div_iff₀ hε]; linarith
  have a2 : 1 ≤ (τ - (q - 2 * ε)) / ε := by rw [le_div_iff₀ hε]; linarith
  rw [Real.smoothTransition.one_of_one_le a1, Real.smoothTransition.one_of_one_le a2]; simp

theorem trap_eq_one (_h3 : 3 * ε ≤ q - p) (hε : 0 < ε) {τ : ℝ} (h1 : p + 2 * ε ≤ τ)
    (h2 : τ ≤ q - 2 * ε) : trap p q ε τ = 1 := by
  unfold trap
  have a1 : 1 ≤ (τ - (p + ε)) / ε := by rw [le_div_iff₀ hε]; linarith
  have a2 : (τ - (q - 2 * ε)) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  rw [Real.smoothTransition.one_of_one_le a1, Real.smoothTransition.zero_of_nonpos a2]; simp

theorem trap_nonneg (h3 : 3 * ε ≤ q - p) (hε : 0 < ε) (τ : ℝ) : 0 ≤ trap p q ε τ := by
  unfold trap
  have : (τ - (q - 2 * ε)) / ε ≤ (τ - (p + ε)) / ε := by
    apply div_le_div_of_nonneg_right _ hε.le; linarith
  linarith [Real.smoothTransition.monotone this]

theorem trap_le_one (τ : ℝ) : trap p q ε τ ≤ 1 := by
  unfold trap
  linarith [Real.smoothTransition.le_one ((τ - (p + ε)) / ε),
    Real.smoothTransition.nonneg ((τ - (q - 2 * ε)) / ε)]

theorem tsupport_trap_subset (h3 : 3 * ε ≤ q - p) (hε : 0 < ε) :
    tsupport (trap p q ε) ⊆ Icc (p + ε) (q - ε) := by
  apply closure_minimal _ isClosed_Icc
  intro τ hτ
  by_contra hn
  apply hτ
  simp only [mem_Icc, not_and_or, not_le] at hn
  rcases hn with h | h
  · exact trap_eq_zero_of_lt h3 hε h
  · exact trap_eq_zero_of_gt h3 hε h

end

theorem integrable_ramp_term {m : ℝ → ℝ} (hm : Continuous m) (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun τ => m τ * (ε⁻¹ * rampDeriv ((τ - c) / ε))) := by
  refine Continuous.integrable_of_hasCompactSupport
    (hm.mul (continuous_const.mul (rampDeriv_continuous.comp (by fun_prop)))) ?_
  refine HasCompactSupport.of_support_subset_isCompact (K := Icc c (c + ε)) isCompact_Icc ?_
  intro τ hτ
  by_contra hn
  apply hτ
  have : (τ - c) / ε ∉ Icc (0:ℝ) 1 := by
    intro hh
    apply hn
    refine ⟨?_, ?_⟩
    · have := hh.1; rw [le_div_iff₀ hε] at this; linarith
    · have := hh.2; rw [div_le_iff₀ hε] at this; linarith
  simp [rampDeriv_eq_zero_of_notMem this]

/-- The du Bois-Reymond step. -/
theorem dubois_reymond {p q : ℝ} (hpq : p < q) (m g : ℝ → ℝ) (hm : Continuous m)
    (hg : IntegrableOn g (Ioo p q))
    (h : ∀ θ : ℝ → ℝ, ContDiff ℝ 1 θ → HasCompactSupport θ → tsupport θ ⊆ Ioo p q →
      ∫ τ in Ioo p q, m τ * deriv θ τ = ∫ τ in Ioo p q, g τ * θ τ) :
    m p - m q = ∫ τ in Ioo p q, g τ := by
  set δ : ℝ := (q - p) / 3 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  -- the family of test functions
  have hmem : ∀ᶠ ε in 𝓝[>] (0:ℝ), 0 < ε ∧ 3 * ε ≤ q - p := by
    filter_upwards [Ioc_mem_nhdsGT hδpos] with ε hε
    exact ⟨hε.1, by rw [hδ] at hε; linarith [hε.2]⟩
  have hL : ∀ᶠ ε in 𝓝[>] (0:ℝ),
      ∫ τ in Ioo p q, m τ * deriv (trap p q ε) τ = ∫ τ in Ioo p q, g τ * trap p q ε τ := by
    filter_upwards [hmem] with ε ⟨hε, h3⟩
    have hsub := tsupport_trap_subset h3 hε
    refine h _ trap_contDiff ?_ ?_
    · exact HasCompactSupport.of_support_subset_isCompact (K := Icc (p + ε) (q - ε)) isCompact_Icc
        (subset_tsupport _ |>.trans hsub)
    · refine hsub.trans ?_
      intro τ hτ; exact ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  -- right side tends to the integral of g
  have hR : Tendsto (fun ε => ∫ τ in Ioo p q, g τ * trap p q ε τ) (𝓝[>] 0)
      (𝓝 (∫ τ in Ioo p q, g τ)) := by
    have : ∫ τ in Ioo p q, g τ = ∫ τ in Ioo p q, g τ * 1 := by simp
    rw [this]
    refine tendsto_integral_filter_of_dominated_convergence (fun τ => ‖g τ‖) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun ε => ?_
      exact hg.aestronglyMeasurable.mul trap_contDiff.continuous.aestronglyMeasurable
    · filter_upwards [hmem] with ε ⟨hε, h3⟩
      refine Eventually.of_forall fun τ => ?_
      rw [norm_mul]
      have h0 := trap_nonneg h3 hε τ
      have h1 := trap_le_one (p := p) (q := q) (ε := ε) τ
      rw [Real.norm_of_nonneg h0]
      exact mul_le_of_le_one_right (norm_nonneg _) h1
    · exact hg.norm
    · refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun τ hτ => ?_)
      refine Tendsto.const_mul _ (tendsto_const_nhds.congr' ?_)
      have : ∀ᶠ ε in 𝓝[>] (0:ℝ), 0 < ε ∧ 3 * ε ≤ q - p ∧ 2 * ε ≤ τ - p ∧ 2 * ε ≤ q - τ := by
        have hpos : 0 < min (τ - p) (q - τ) := lt_min (by linarith [hτ.1]) (by linarith [hτ.2])
        filter_upwards [Ioc_mem_nhdsGT (show (0:ℝ) < min δ (min (τ - p) (q - τ)) / 2 from
          by have := lt_min hδpos hpos; linarith)] with ε hε
        have h1 := hε.2
        have h2 := min_le_left δ (min (τ - p) (q - τ))
        have h3 := (min_le_right δ (min (τ - p) (q - τ))).trans (min_le_left _ _)
        have h4 := (min_le_right δ (min (τ - p) (q - τ))).trans (min_le_right _ _)
        refine ⟨hε.1, ?_, ?_, ?_⟩ <;> [rw [hδ] at h2; skip; skip] <;> linarith
      filter_upwards [this] with ε ⟨hε, h3, h1, h2⟩
      exact (trap_eq_one h3 hε (by linarith) (by linarith)).symm
  -- left side tends to m p - m q
  have hLim : Tendsto (fun ε => ∫ τ in Ioo p q, m τ * deriv (trap p q ε) τ) (𝓝[>] 0)
      (𝓝 (m p - m q)) := by
    refine Tendsto.congr' (f₁ := fun ε : ℝ =>
      (∫ τ, m τ * (ε⁻¹ * rampDeriv ((τ - (p + 1 * ε)) / ε)))
          - ∫ τ, m τ * (ε⁻¹ * rampDeriv ((τ - (q + (-2) * ε)) / ε))) ?_
      ((tendsto_ramp_avg m hm p 1).sub (tendsto_ramp_avg m hm q (-2)))
    filter_upwards [hmem] with ε ⟨hε, h3⟩
    rw [← integral_sub (integrable_ramp_term hm _ hε) (integrable_ramp_term hm _ hε)]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioo p q)]
    · refine setIntegral_congr_fun measurableSet_Ioo fun τ _ => ?_
      rw [(trap_hasDerivAt hε τ).deriv]; ring
    · intro τ hτ
      have : τ ∉ tsupport (trap p q ε) := fun hh => hτ (by
        have := tsupport_trap_subset h3 hε hh
        exact ⟨by linarith [this.1], by linarith [this.2]⟩)
      have hd : deriv (trap p q ε) τ = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hh => this (tsupport_deriv_subset hh))
      rw [(trap_hasDerivAt hε τ).deriv] at hd
      rw [← mul_sub, hd, mul_zero]
  exact tendsto_nhds_unique (hLim.congr' (hL)) hR

end PDE.Parabolic.WeakSlice
