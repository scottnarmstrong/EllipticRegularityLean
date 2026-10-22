/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.WeakHarnack.EnergySobolev
public import EllipticRegularity.Parabolic.LocalMax.Cutoff

/-! # Product cutoffs for the power step -/

@[expose] public section

namespace PDE.Parabolic.WeakHarnack

open MeasureTheory Set PDE PDE.Parabolic.LocalMax PDE.Parabolic.WeakSlice

variable {d : ℕ}

/-- A product cutoff `θ(τ) ξ(x)` satisfies `PowCutoff` on `B_ρ × W`. -/
theorem powCutoff_product {U : Set (Vec d)} {ρ : ℝ} {W : Set ℝ} {ξ : Vec d → ℝ} {θ : ℝ → ℝ}
    (hξ : ContDiff ℝ (⊤ : ℕ∞) ξ) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hξ0 : ∀ x, 0 ≤ ξ x) (hξ1 : ∀ x, ξ x ≤ 1) (hθ0 : ∀ τ, 0 ≤ θ τ) (hθ1 : ∀ τ, θ τ ≤ 1)
    (hξs : tsupport ξ ⊆ euclideanBall (0 : Vec d) ρ) (hξc : HasCompactSupport ξ)
    (hρU : euclideanBall (0 : Vec d) ρ ⊆ U) {X T : ℝ} (hX : 0 ≤ X) (hT : 0 ≤ T)
    (hgrad : ∀ x, vecNormSq (classicalGradient ξ x) ≤ X) (htime : ∀ τ, |θ τ * deriv θ τ| ≤ T)
    (hθW : ∀ τ, τ ∉ W → θ τ = 0) :
    PowCutoff U (euclideanBall (0 : Vec d) ρ ×ˢ W) (fun z => θ z.2 * ξ z.1) X T := by
  have hθ1' : ContDiff ℝ 1 θ := hθ.of_le (by simp)
  have hξ1' : ContDiff ℝ 1 ξ := hξ.of_le (by simp)
  have hnot : ∀ x, x ∉ euclideanBall (0 : Vec d) ρ → ξ x = 0 ∧ spaceGradC1 ξ x = 0 := by
    intro x hx
    have hxs : x ∉ tsupport ξ := fun h => hx (hξs h)
    refine ⟨image_eq_zero_of_notMem_tsupport hxs, ?_⟩
    have : fderiv ℝ ξ x = 0 := fderiv_of_notMem_tsupport ℝ hxs
    ext i; simp [spaceGradC1, this]
  refine ⟨(hθ.comp contDiff_snd).mul (hξ.comp contDiff_fst), fun z => mul_nonneg (hθ0 _) (hξ0 _),
    fun z => ?_, ⟨tsupport ξ, hξc.isCompact, hξs.trans hρU, fun x t hx => ?_⟩, fun z => ?_,
    fun z => ?_, hX, hT⟩
  · calc θ z.2 * ξ z.1 ≤ 1 * 1 := mul_le_mul (hθ1 _) (hξ1 _) (hξ0 _) zero_le_one
      _ = 1 := one_mul 1
  · simp [image_eq_zero_of_notMem_tsupport hx]
  · rw [parSpaceGrad_prod hθ1' hξ1', vecNormSq_smul]
    by_cases hz : z ∈ euclideanBall (0 : Vec d) ρ ×ˢ W
    · simp only [Set.indicator_of_mem hz, mul_one]
      calc θ z.2 ^ 2 * vecNormSq (spaceGradC1 ξ z.1) ≤ 1 * X := by
            refine mul_le_mul ?_ (hgrad z.1) (vecNormSq_nonneg _) zero_le_one
            nlinarith [hθ0 z.2, hθ1 z.2]
        _ = X := one_mul X
    · simp only [Set.indicator_of_notMem hz, mul_zero]
      rw [mem_prod, not_and_or] at hz
      rcases hz with hz | hz
      · rw [(hnot _ hz).2]; simp [vecNormSq, vecDot]
      · rw [hθW _ hz]; simp
  · rw [parTimeDeriv_prod hθ1' hξ1']
    by_cases hz : z ∈ euclideanBall (0 : Vec d) ρ ×ˢ W
    · simp only [Set.indicator_of_mem hz, mul_one]
      have h1 : θ z.2 * ξ z.1 * (deriv θ z.2 * ξ z.1) = ξ z.1 ^ 2 * (θ z.2 * deriv θ z.2) := by ring
      rw [h1, abs_mul, abs_of_nonneg (sq_nonneg _)]
      calc ξ z.1 ^ 2 * |θ z.2 * deriv θ z.2| ≤ 1 * T :=
            mul_le_mul (by nlinarith [hξ0 z.1, hξ1 z.1]) (htime _) (abs_nonneg _) zero_le_one
        _ = T := one_mul T
    · simp only [Set.indicator_of_notMem hz, mul_zero]
      rw [mem_prod, not_and_or] at hz
      rcases hz with hz | hz
      · rw [(hnot _ hz).1]; simp
      · rw [hθW _ hz]; simp

end PDE.Parabolic.WeakHarnack
