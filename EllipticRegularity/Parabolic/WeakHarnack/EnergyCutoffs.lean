/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.WeakHarnack.EnergyRamp

/-! # Concrete cutoffs between nested cylinders -/

@[expose] public section

namespace PDE.Parabolic.WeakHarnack

open MeasureTheory Set PDE

variable {d : ℕ}

/-- The spatial factor: all the hypotheses of `powCutoff_product` for `canonicalBallCutoff`. -/
theorem ballCutoff_facts {r' ρ : ℝ} (hr : 0 ≤ r') (hrρ : r' < ρ) :
    ContDiff ℝ (⊤ : ℕ∞) (canonicalBallCutoff (0 : Vec d) r' ρ) ∧
      (∀ x, 0 ≤ canonicalBallCutoff (0 : Vec d) r' ρ x) ∧
      (∀ x, canonicalBallCutoff (0 : Vec d) r' ρ x ≤ 1) ∧
      tsupport (canonicalBallCutoff (0 : Vec d) r' ρ) ⊆ euclideanBall (0 : Vec d) ρ ∧
      HasCompactSupport (canonicalBallCutoff (0 : Vec d) r' ρ) ∧
      (∀ x, vecNormSq (classicalGradient (canonicalBallCutoff (0 : Vec d) r' ρ) x) ≤
        1024 / (ρ - r') ^ 2) ∧
      (∀ x ∈ euclideanBall (0 : Vec d) r', canonicalBallCutoff (0 : Vec d) r' ρ x = 1) := by
  refine ⟨canonicalBallCutoff_smooth _ hr hrρ, canonicalBallCutoff_nonneg _ _ _,
    canonicalBallCutoff_le_one _ _ _, canonicalBallCutoff_tsupport_subset_outer hr hrρ,
    canonicalBallCutoff_hasCompactSupport hr hrρ, fun x => ?_,
    fun x hx => canonicalBallCutoff_eq_one_on_inner hr hrρ hx⟩
  have hgrad := canonicalBallCutoff_gradient_bound (x₀ := (0 : Vec d)) hr hrρ x
  have : vecNormSq (classicalGradient (canonicalBallCutoff (0 : Vec d) r' ρ) x) ≤
      (32 / (ρ - r')) ^ 2 := by
    rw [← vecEuclideanNorm_sq]
    exact pow_le_pow_left₀ (vecEuclideanNorm_nonneg _) hgrad 2
  refine this.trans (le_of_eq ?_)
  rw [div_pow]; ring

/-- Cutoffs for positive powers: vanishing at both time ends of `B_ρ × (s,t)`, equal to one on
`B_{r'} × [s', t']`. -/
theorem exists_powCutoff_pos :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {U : Set (Vec d)} {r' ρ s s' t' t : ℝ}, euclideanBall (0 : Vec d) ρ ⊆ U →
      0 ≤ r' → r' < ρ → s < s' → s' < t' → t' < t →
      ∃ η : Vec d × ℝ → ℝ, PowCutoff U (euclideanBall (0 : Vec d) ρ ×ˢ Ioo s t) η
          (1024 / (ρ - r') ^ 2) (B / (s' - s) + B / (t - t')) ∧
        (∀ x τ, τ ≤ s → η (x, τ) = 0) ∧ (∀ x τ, t ≤ τ → η (x, τ) = 0) ∧
        (∀ z ∈ euclideanBall (0 : Vec d) r' ×ˢ Icc s' t', η z = 1) := by
  obtain ⟨B, hB0, hB⟩ := exists_deriv_bound
  refine ⟨B, hB0, fun {U r' ρ s s' t' t} hρU hr hrρ hss' hst hlt => ?_⟩
  obtain ⟨hξ, hξ0, hξ1, hξs, hξc, hξg, hξ1'⟩ := ballCutoff_facts (d := d) hr hrρ
  set θ : ℝ → ℝ := fun τ => upRamp s s' τ * downRamp t' t τ with hθ
  have hθs : ContDiff ℝ (⊤ : ℕ∞) θ := (upRamp_contDiff _ _).mul (downRamp_contDiff _ _)
  have hθ0 : ∀ τ, 0 ≤ θ τ := fun τ => mul_nonneg (upRamp_nonneg _ _ _) (downRamp_nonneg _ _ _)
  have hθ1 : ∀ τ, θ τ ≤ 1 := fun τ => by
    calc θ τ ≤ 1 * 1 := mul_le_mul (upRamp_le_one _ _ _) (downRamp_le_one _ _ _)
          (downRamp_nonneg _ _ _) zero_le_one
      _ = 1 := one_mul 1
  have hdθ : ∀ τ, deriv θ τ = deriv (upRamp s s') τ * downRamp t' t τ +
      upRamp s s' τ * deriv (downRamp t' t) τ := by
    intro τ
    exact deriv_mul (((upRamp_contDiff s s').differentiable (by simp)) τ)
      (((downRamp_contDiff t' t).differentiable (by simp)) τ)
  have hθt : ∀ τ, |θ τ * deriv θ τ| ≤ B / (s' - s) + B / (t - t') := by
    intro τ
    have h1 := abs_deriv_upRamp_le hB (show s < s' from hss') τ
    have h2 := abs_deriv_downRamp_le hB (show t' < t from hlt) τ
    have hb1 : |downRamp t' t τ| ≤ 1 := by
      rw [abs_of_nonneg (downRamp_nonneg _ _ _)]; exact downRamp_le_one _ _ _
    have hb2 : |upRamp s s' τ| ≤ 1 := by
      rw [abs_of_nonneg (upRamp_nonneg _ _ _)]; exact upRamp_le_one _ _ _
    have hθ1' : |θ τ| ≤ 1 := by rw [abs_of_nonneg (hθ0 τ)]; exact hθ1 τ
    have h3 : |deriv θ τ| ≤ B / (s' - s) + B / (t - t') := by
      rw [hdθ, show s' - s = s' - s from rfl]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]
        calc _ ≤ |deriv (upRamp s s') τ| * 1 := mul_le_mul_of_nonneg_left hb1 (abs_nonneg _)
          _ ≤ _ := by rw [mul_one]; exact h1
      · rw [abs_mul]
        calc _ ≤ 1 * |deriv (downRamp t' t) τ| := mul_le_mul_of_nonneg_right hb2 (abs_nonneg _)
          _ ≤ _ := by rw [one_mul]; exact h2
    rw [abs_mul]
    calc _ ≤ 1 * |deriv θ τ| := mul_le_mul_of_nonneg_right hθ1' (abs_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact h3
  have hθW : ∀ τ, τ ∉ Ioo s t → θ τ = 0 := by
    intro τ hτ
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at hτ
    rcases hτ with h | h
    · simp [hθ, upRamp_eq_zero hss' h]
    · simp [hθ, downRamp_eq_zero hlt h]
  have hX : (0 : ℝ) ≤ 1024 / (ρ - r') ^ 2 := by positivity
  have hT : 0 ≤ B / (s' - s) + B / (t - t') := by
    have : 0 < s' - s := by linarith
    have : 0 < t - t' := by linarith
    positivity
  refine ⟨fun z => θ z.2 * canonicalBallCutoff (0 : Vec d) r' ρ z.1,
    powCutoff_product hξ hθs hξ0 hξ1 hθ0 hθ1 hξs hξc hρU hX hT hξg hθt hθW, ?_, ?_, ?_⟩
  · intro x τ h; simp [hθ, upRamp_eq_zero hss' h]
  · intro x τ h; simp [hθ, downRamp_eq_zero hlt h]
  · rintro ⟨x, τ⟩ ⟨hx, hτ1, hτ2⟩
    simp [hθ, upRamp_eq_one hss' hτ1, downRamp_eq_one hlt hτ2, hξ1' x hx]

/-- Cutoffs for negative powers: vanishing at the bottom time of `B_ρ × (s, ∞)`, equal to one on
`B_{r'} × [s', ∞)`. -/
theorem exists_powCutoff_neg :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {U : Set (Vec d)} {r' ρ s s' : ℝ}, euclideanBall (0 : Vec d) ρ ⊆ U →
      0 ≤ r' → r' < ρ → s < s' →
      ∃ η : Vec d × ℝ → ℝ, PowCutoff U (euclideanBall (0 : Vec d) ρ ×ˢ Ioi s) η
          (1024 / (ρ - r') ^ 2) (B / (s' - s)) ∧
        (∀ x τ, τ ≤ s → η (x, τ) = 0) ∧
        (∀ z ∈ euclideanBall (0 : Vec d) r' ×ˢ Ici s', η z = 1) := by
  obtain ⟨B, hB0, hB⟩ := exists_deriv_bound
  refine ⟨B, hB0, fun {U r' ρ s s'} hρU hr hrρ hss' => ?_⟩
  obtain ⟨hξ, hξ0, hξ1, hξs, hξc, hξg, hξ1'⟩ := ballCutoff_facts (d := d) hr hrρ
  have hθt : ∀ τ, |upRamp s s' τ * deriv (upRamp s s') τ| ≤ B / (s' - s) := by
    intro τ
    have h1 := abs_deriv_upRamp_le hB hss' τ
    rw [abs_mul]
    have hb2 : |upRamp s s' τ| ≤ 1 := by
      rw [abs_of_nonneg (upRamp_nonneg _ _ _)]; exact upRamp_le_one _ _ _
    calc _ ≤ 1 * |deriv (upRamp s s') τ| := mul_le_mul_of_nonneg_right hb2 (abs_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact h1
  have hθW : ∀ τ, τ ∉ Ioi s → upRamp s s' τ = 0 := fun τ hτ =>
    upRamp_eq_zero hss' (not_lt.1 hτ)
  have hX : (0 : ℝ) ≤ 1024 / (ρ - r') ^ 2 := by positivity
  have hT : 0 ≤ B / (s' - s) := by
    have : 0 < s' - s := by linarith
    positivity
  refine ⟨fun z => upRamp s s' z.2 * canonicalBallCutoff (0 : Vec d) r' ρ z.1,
    powCutoff_product hξ (upRamp_contDiff _ _) hξ0 hξ1 (upRamp_nonneg _ _) (upRamp_le_one _ _)
      hξs hξc hρU hX hT hξg hθt hθW, ?_, ?_⟩
  · intro x τ h; simp [upRamp_eq_zero hss' h]
  · rintro ⟨x, τ⟩ ⟨hx, hτ⟩
    simp [upRamp_eq_one hss' hτ, hξ1' x hx]

end PDE.Parabolic.WeakHarnack
