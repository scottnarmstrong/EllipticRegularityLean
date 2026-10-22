module

public import PDEFoundation.Monotonicity.FriedlandHayman.Gauss.BartaBoundary

/-!
# Friedland--Hayman: Barta's inequality for the Gaussian half-line

If `c` is admissible at `τ` then `c ∫ g² w ≤ ∫_{(τ,∞)} g'² w` for every admissible test function `g`.
-/

@[expose] public section

open Set MeasureTheory Filter Topology

namespace PDE.FHLane

noncomputable section

/-- Barta's inequality. -/
theorem barta {τ c : ℝ} {g g' : ℝ → ℝ} (hc : OUAdmissible τ c) (hg : GaussTest τ g g') :
    c * ∫ s, g s ^ 2 * gaussW s ≤ ∫ s in Set.Ioi τ, g' s ^ 2 * gaussW s := by
  obtain ⟨hc0, hpos⟩ := hc
  set h : ℝ → ℝ := fun x => g' x ^ 2 * gaussW x - c * (g x ^ 2 * gaussW x) with hh
  have hint_h : IntegrableOn h (Ioi τ) :=
    hg.int_dsq.sub (hg.int_sq.integrableOn.const_mul c)
  have hnn : ∀ L, max τ 0 < L → 0 ≤ bartaF c τ g L := by
    intro L hL
    have hLτ : τ < L := lt_of_le_of_lt (le_max_left _ _) hL
    unfold bartaF
    exact mul_nonneg (mul_nonneg (div_nonneg (ouSolDeriv_nonneg hc0 hpos L hL) (hpos L hLτ).le)
      (sq_nonneg _)) (gaussW_pos _).le
  have claim1 : ∀ a, τ < a → -bartaF c τ g a ≤ ∫ x in Ioi a, h x := by
    intro a ha
    have hint : IntegrableOn h (Ioi a) := hint_h.mono_set (Ioi_subset_Ioi ha.le)
    refine ge_of_tendsto (intervalIntegral_tendsto_integral_Ioi a hint tendsto_id) ?_
    filter_upwards [Ioi_mem_atTop (max a (max τ 0))] with L hL
    have hL1 : a < L := lt_of_le_of_lt (le_max_left _ _) hL
    have hL2 : max τ 0 < L := lt_of_le_of_lt (le_max_right _ _) hL
    have := bartaF_le_integral hg.cont hg.hasDeriv hg.cont' ha hL1.le hpos
    have := hnn L hL2
    simp only [id]
    linarith
  have claim2 : 0 ≤ ∫ x in Ioi τ, h x := by
    have hJ := tendsto_setIntegral_Ioc_zero hint_h
    have hF := bartaF_tendsto_zero hpos hg
    refine le_of_tendsto (by simpa using hJ.sub hF) ?_
    filter_upwards [self_mem_nhdsWithin] with a (ha : τ < a)
    have hsplit : ∫ x in Ioi τ, h x = (∫ x in Ioc τ a, h x) + ∫ x in Ioi a, h x := by
      rw [← setIntegral_union (s := Ioc τ a) (t := Ioi a) ?_ measurableSet_Ioi
        (hint_h.mono_set fun x hx => hx.1) (hint_h.mono_set (Ioi_subset_Ioi ha.le)),
        Ioc_union_Ioi_eq_Ioi ha.le]
      exact Set.disjoint_left.mpr fun x hx hx' => absurd hx.2 (not_le.mpr hx')
    have := claim1 a ha
    linarith
  have hsplit : ∫ x in Ioi τ, h x = (∫ x in Ioi τ, g' x ^ 2 * gaussW x)
      - c * ∫ x in Ioi τ, g x ^ 2 * gaussW x := by
    rw [hh]
    simp only
    rw [integral_sub hg.int_dsq (hg.int_sq.integrableOn.const_mul c), integral_const_mul]
  have hfull : ∫ s, g s ^ 2 * gaussW s = ∫ s in Ioi τ, g s ^ 2 * gaussW s := by
    symm
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    rw [hg.eq_zero x (not_lt.mp hx)]
    simp
  rw [hfull]
  linarith

end

end PDE.FHLane
