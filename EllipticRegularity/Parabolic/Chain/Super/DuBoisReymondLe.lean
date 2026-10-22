/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.WeakSlice.DuBoisReymond

/-! # A one-sided du Bois-Reymond step -/

@[expose] public section

namespace PDE.Parabolic.Chain.Super

open MeasureTheory Set Filter Topology PDE.Parabolic.WeakSlice

/-- One-sided du Bois-Reymond step: if `∫ m θ' ≤ ∫ g θ` for all nonnegative `C¹`
test functions `θ` supported in `(p, q)`, then `m p - m q ≤ ∫_{(p,q)} g`. -/
theorem dubois_reymond_le {p q : ℝ} (hpq : p < q) (m g : ℝ → ℝ) (hm : Continuous m)
    (hg : IntegrableOn g (Ioo p q))
    (h : ∀ θ : ℝ → ℝ, ContDiff ℝ 1 θ → HasCompactSupport θ → tsupport θ ⊆ Ioo p q → (∀ τ, 0 ≤ θ τ) →
      ∫ τ in Ioo p q, m τ * deriv θ τ ≤ ∫ τ in Ioo p q, g τ * θ τ) :
    m p - m q ≤ ∫ τ in Ioo p q, g τ := by
  set δ : ℝ := (q - p) / 3 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  -- the family of test functions
  have hmem : ∀ᶠ ε in 𝓝[>] (0:ℝ), 0 < ε ∧ 3 * ε ≤ q - p := by
    filter_upwards [Ioc_mem_nhdsGT hδpos] with ε hε
    exact ⟨hε.1, by rw [hδ] at hε; linarith [hε.2]⟩
  have hL : ∀ᶠ ε in 𝓝[>] (0:ℝ),
      ∫ τ in Ioo p q, m τ * deriv (trap p q ε) τ ≤ ∫ τ in Ioo p q, g τ * trap p q ε τ := by
    filter_upwards [hmem] with ε ⟨hε, h3⟩
    have hsub := tsupport_trap_subset h3 hε
    refine h _ trap_contDiff ?_ ?_ (trap_nonneg h3 hε)
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
  exact le_of_tendsto_of_tendsto hLim hR hL

end PDE.Parabolic.Chain.Super
