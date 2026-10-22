module

public import PDEFoundation.Analysis.Inequalities.JohnNirenbergBall.Distribution
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The John–Nirenberg inequality on balls

Proposition 1.17, deduced from the Lemma 1.16
(`PDE.JohnNirenberg.volume_lt_abs_sub_integralAverage_le`), in the `M`-form of the statement of Proposition 1.17.
-/

@[expose] public section

namespace PDE.JohnNirenbergBall

open BoxIntegral MeasureTheory Set PDE.JohnNirenberg
open scoped ENNReal

/-- The John–Nirenberg inequality on balls (Proposition 1.17); `M` is any
upper bound for the `BMO(B)` seminorm. -/
theorem exists_johnNirenberg_constant_full (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : Vec d) (R : ℝ), 0 < R → ∀ (u : Vec d → ℝ) (M : ℝ), 0 < M →
      LocallyIntegrableOn u (euclideanBall x R) volume →
      (∀ (y : Vec d) (r : ℝ), 0 < r → closure (euclideanBall y r) ⊆ euclideanBall x R →
        integralAverage (euclideanBall y r) (fun z => |u z - integralAverage (euclideanBall y r) u|) ≤ M) →
      IntegrableOn u (euclideanBall x R) volume ∧
      ∀ t : ℝ, 0 < t →
        (volume {z ∈ euclideanBall x R | t < |u z - integralAverage (euclideanBall x R) u|}).toReal ≤
          C * Real.exp (-(t / (C * M))) * (volume (euclideanBall x R)).toReal := by
  have hd' : 0 < d := hd
  have hθ := jnTheta_pos hd'
  have hS := intSeries_nonneg hd'
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd'
  set κ : ℝ := 2 * d * intSeries d with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set A1 : ℝ := 2 * d * (2 * Real.exp 2 + 4) with hA1
  have hA1pos : 0 < A1 := by positivity
  set C : ℝ := A1 + 2 / jnTheta d + 2 * κ + 3 with hC
  have hCpos : 0 < C := by positivity
  refine ⟨C, hCpos, ?_⟩
  intro x R hR u M hMpos hloc hM
  have hint := integrableOn_ball hd' hR hloc hM hMpos
  refine ⟨hint, ?_⟩
  intro t ht
  set h := integralAverage (euclideanBall x (3 * R / 4)) u
  set ub := integralAverage (euclideanBall x R) u
  have hBtop := volume_euclideanBall_ne_top x hR.le
  have hBpos := volume_euclideanBall_toReal_pos x hR
  have hcmp := abs_integralAverage_ball_sub_H_le hd' hR hloc hM hMpos
  by_cases hcase : 2 * κ * M ≤ t
  · have hsub : {z ∈ euclideanBall x R | t < |u z - ub|} ⊆
        {z ∈ euclideanBall x R | t / 2 < |u z - h|} := by
      rintro z ⟨hz, hzt⟩
      refine ⟨hz, ?_⟩
      have : |u z - ub| ≤ |u z - h| + |h - ub| := by
        calc |u z - ub| = |(u z - h) + (h - ub)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      rw [abs_sub_comm h ub] at this
      have hκM : κ * M ≤ t / 2 := by linarith
      linarith [mul_le_mul_of_nonneg_right hcmp le_rfl]
    have hmono := ENNReal.toReal_mono
      (ne_top_of_le_ne_top hBtop (measure_mono fun z hz => hz.1)) (measure_mono hsub)
    have htail := volume_tail_H_le hd' hR hloc hM hMpos (t := t / 2) (by positivity)
    refine hmono.trans (htail.trans ?_)
    have hexp : Real.exp (-(jnTheta d * (t / 2 / M))) ≤ Real.exp (-(t / (C * M))) := by
      apply Real.exp_le_exp.mpr
      have h2 : t / (C * M) ≤ jnTheta d * (t / 2 / M) := by
        rw [div_le_iff₀ (by positivity)]
        have : 2 / jnTheta d ≤ C := by rw [hC]; linarith
        rw [div_le_iff₀ hθ] at this
        have hp : 0 < t / M := by positivity
        have e1 : jnTheta d * (t / 2 / M) * (C * M) = (jnTheta d * C / 2) * t := by
          field_simp
        rw [e1]
        nlinarith
      linarith
    have hA : 2 * (d : ℝ) * ((2 * Real.exp 2 + 4) * Real.exp (-(jnTheta d * (t / 2 / M)))) ≤
        C * Real.exp (-(t / (C * M))) := by
      have : 2 * (d : ℝ) * ((2 * Real.exp 2 + 4) * Real.exp (-(jnTheta d * (t / 2 / M)))) =
          A1 * Real.exp (-(jnTheta d * (t / 2 / M))) := by rw [hA1]; ring
      rw [this]
      have hAC : A1 ≤ C := by rw [hC]; have : 0 < 2 / jnTheta d := by positivity
                              linarith
      calc _ ≤ A1 * Real.exp (-(t / (C * M))) :=
            mul_le_mul_of_nonneg_left hexp hA1pos.le
        _ ≤ C * Real.exp (-(t / (C * M))) := mul_le_mul_of_nonneg_right hAC (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_right hA hBpos.le
  · push Not at hcase
    have hle : (volume {z ∈ euclideanBall x R | t < |u z - ub|}).toReal ≤
        (volume (euclideanBall x R)).toReal :=
      ENNReal.toReal_mono hBtop (measure_mono fun z hz => hz.1)
    refine hle.trans ?_
    have hq : t / (C * M) ≤ 1 := by
      rw [div_le_iff₀ (by positivity)]
      have : 2 * κ ≤ C := by rw [hC]; have : 0 < 2 / jnTheta d := by positivity
                             linarith
      nlinarith
    have he : 1 / 3 ≤ Real.exp (-(t / (C * M))) := by
      have h1 : Real.exp (-1) ≤ Real.exp (-(t / (C * M))) := Real.exp_le_exp.mpr (by linarith)
      have h3 : Real.exp 1 ≤ 3 := (Real.exp_one_lt_d9).le.trans (by norm_num)
      have : 1 / 3 ≤ Real.exp (-1) := by
        rw [Real.exp_neg]
        rw [← one_div]
        exact one_div_le_one_div_of_le (Real.exp_pos 1) h3
      linarith
    have hC3 : 3 ≤ C := by rw [hC]; have : 0 < 2 / jnTheta d := by positivity
                           linarith
    have : 1 ≤ C * Real.exp (-(t / (C * M))) := by nlinarith
    nlinarith

end PDE.JohnNirenbergBall
