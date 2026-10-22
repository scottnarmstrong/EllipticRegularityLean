module

public import PDEFoundation.Analysis.Inequalities.JohnNirenberg.BallBasic

/-!
# The chain of balls (Step 2 of Proposition 1.17)

For a ball `B = B_R(x)`, put `H = B_{3R/4}(x)` and `σ(p) = R - |p - x|`. We compare the average of
`u` over the ball `B_{σ(p)/2}(p)` with the average over `H` by moving radially towards `x` while
doubling the distance to the boundary; each doubling costs `2 · 3 ^ d M`.
-/

@[expose] public section

namespace PDE.JohnNirenbergBall

open BoxIntegral MeasureTheory Set PDE.JohnNirenberg
open scoped ENNReal

variable {d : ℕ} {u : Vec d → ℝ} {M R : ℝ} {x : Vec d}

/-- A closed ball whose radius plus center distance is less than `R` lies in `B_R(x)`. -/
theorem euclideanClosedBall_subset_ball_of_norm_add_lt {y : Vec d} {r : ℝ} (hr : 0 ≤ r)
    (h : vecEuclideanNorm (y - x) + r < R) : euclideanClosedBall y r ⊆ euclideanBall x R :=
  (euclideanClosedBall_subset_of_norm_add_le hr le_rfl).trans
    (euclideanClosedBall_subset_euclideanBall
      (by linarith [vecEuclideanNorm_nonneg (y - x)]) h)

/-- Display (1.32) in the ball `B_R(x)`. -/
theorem abs_integralAverage_ball_sub_le (hloc : LocallyIntegrableOn u (euclideanBall x R) volume)
    (hM : BMOBound (euclideanBall x R) u M) {z y : Vec d} {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hEG : euclideanBall z ρ ⊆ euclideanBall y r)
    (hG : vecEuclideanNorm (y - x) + r < R) :
    |integralAverage (euclideanBall z ρ) u - integralAverage (euclideanBall y r) u| ≤
      (r / ρ) ^ d * M :=
  abs_integralAverage_sub_le_of_ball_subset hloc hM hρ hr hEG
    (euclideanClosedBall_subset_ball_of_norm_add_lt hr.le hG)

/-- The radial chain: if `σ(p) ≥ R / 2 ^ (j + 1)`, then the average of `u` over
`B_{σ(p)/2}(p)` differs from the average over `H = B_{3R/4}(x)` by at most `(1 + 2 j) 3 ^ d M`. -/
theorem abs_integralAverage_sub_integralAverage_H_le (hR : 0 < R)
    (hloc : LocallyIntegrableOn u (euclideanBall x R) volume)
    (hM : BMOBound (euclideanBall x R) u M) (hM0 : 0 ≤ M) (j : ℕ) :
    ∀ p : Vec d, R / 2 ^ (j + 1) ≤ R - vecEuclideanNorm (p - x) →
      |integralAverage (euclideanBall p ((R - vecEuclideanNorm (p - x)) / 2)) u -
          integralAverage (euclideanBall x (3 * R / 4)) u| ≤
        ((3 : ℝ) ^ d + 2 * (3 : ℝ) ^ d * j) * M := by
  have h3 : (1 : ℝ) ≤ 3 ^ d := one_le_pow₀ (by norm_num)
  induction j with
  | zero =>
      intro p hp
      simp only [zero_add, pow_one] at hp
      set σ := R - vecEuclideanNorm (p - x) with hσ
      have hσpos : 0 < σ := lt_of_lt_of_le (by positivity) hp
      have hsub : euclideanBall p (σ / 2) ⊆ euclideanBall x (3 * R / 4) := by
        apply euclideanBall_subset_of_center_norm_add_le (by positivity) (by positivity)
        rw [hσ] at hp ⊢; linarith
      have hn := abs_integralAverage_ball_sub_le hloc hM (z := p) (y := x) (ρ := σ / 2)
        (r := 3 * R / 4) (by positivity) (by positivity) hsub
        (by simp [vecEuclideanNorm_eq_zero_iff.mpr rfl]; linarith)
      have hratio : (3 * R / 4 / (σ / 2)) ^ d ≤ 3 ^ d := by
        apply pow_le_pow_left₀ (by positivity)
        rw [div_le_iff₀ (by positivity)]; linarith
      simp only [Nat.cast_zero, mul_zero, add_zero]
      calc _ ≤ _ := hn
        _ ≤ _ := mul_le_mul_of_nonneg_right hratio hM0
  | succ j ih =>
      intro p hp
      set σ := R - vecEuclideanNorm (p - x) with hσ
      have hσpos : 0 < σ := lt_of_lt_of_le (by positivity) hp
      have hmono : ((3 : ℝ) ^ d + 2 * (3 : ℝ) ^ d * j) * M ≤
          ((3 : ℝ) ^ d + 2 * (3 : ℝ) ^ d * ((j + 1 : ℕ) : ℝ)) * M := by
        apply mul_le_mul_of_nonneg_right _ hM0
        push_cast; nlinarith
      by_cases hcase : R / 2 ^ (j + 1) ≤ σ
      · exact (ih p hcase).trans hmono
      · push Not at hcase
        have hpow : (2 : ℝ) ^ (j + 1) ≥ 2 := by
          calc (2 : ℝ) ^ (j + 1) ≥ 2 ^ 1 := pow_le_pow_right₀ (by norm_num) (by omega)
            _ = 2 := by norm_num
        have hσR : σ < R / 2 := by
          refine hcase.trans_le ?_
          rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
        have hnorm : vecEuclideanNorm (p - x) = R - σ := by rw [hσ]; ring
        have hnormpos : 0 < vecEuclideanNorm (p - x) := by linarith
        set p' : Vec d := x + (1 - σ / vecEuclideanNorm (p - x)) • (p - x) with hp'
        have hp'x : p' - x = (1 - σ / vecEuclideanNorm (p - x)) • (p - x) := by
          rw [hp']; abel
        have hpp' : p - p' = (σ / vecEuclideanNorm (p - x)) • (p - x) := by
          rw [hp']; module
        have hfac : 0 ≤ 1 - σ / vecEuclideanNorm (p - x) := by
          rw [sub_nonneg, div_le_one hnormpos]; linarith
        have hnorm' : vecEuclideanNorm (p' - x) = R - 2 * σ := by
          rw [hp'x, vecEuclideanNorm_smul, abs_of_nonneg hfac]
          field_simp
          rw [hnorm]; ring
        have hdist : vecEuclideanNorm (p - p') = σ := by
          rw [hpp', vecEuclideanNorm_smul, abs_of_nonneg (by positivity)]
          field_simp
        have hσ' : R / 2 ^ (j + 1) ≤ R - vecEuclideanNorm (p' - x) := by
          rw [hnorm']
          have : R / 2 ^ (j + 2) * 2 = R / 2 ^ (j + 1) := by
            rw [pow_succ _ (j + 1)]; field_simp
          have h2 : R / 2 ^ (j + 2) ≤ σ := hp
          linarith
        have hih := ih p' hσ'
        have hhalf : (R - vecEuclideanNorm (p' - x)) / 2 = σ := by rw [hnorm']; ring
        rw [hhalf] at hih
        have hGR : vecEuclideanNorm (p' - x) + 3 * σ / 2 < R := by rw [hnorm']; linarith
        have hE1 : euclideanBall p (σ / 2) ⊆ euclideanBall p' (3 * σ / 2) := by
          apply euclideanBall_subset_of_center_norm_add_le (by positivity) (by positivity)
          rw [hdist]; linarith
        have hE2 : euclideanBall p' σ ⊆ euclideanBall p' (3 * σ / 2) :=
          euclideanBall_mono hσpos.le (by linarith)
        have n1 := abs_integralAverage_ball_sub_le hloc hM (z := p) (y := p') (ρ := σ / 2)
          (r := 3 * σ / 2) (by positivity) (by positivity) hE1 hGR
        have n2 := abs_integralAverage_ball_sub_le hloc hM (z := p') (y := p') (ρ := σ)
          (r := 3 * σ / 2) hσpos (by positivity) hE2 hGR
        have r1 : (3 * σ / 2 / (σ / 2)) = 3 := by field_simp
        have r2 : (3 * σ / 2 / σ) ^ d ≤ 3 ^ d := by
          apply pow_le_pow_left₀ (by positivity)
          rw [div_le_iff₀ hσpos]; linarith
        rw [r1] at n1
        have n2' : |integralAverage (euclideanBall p' σ) u -
            integralAverage (euclideanBall p' (3 * σ / 2)) u| ≤ 3 ^ d * M :=
          n2.trans (mul_le_mul_of_nonneg_right r2 hM0)
        set a := integralAverage (euclideanBall p (σ / 2)) u
        set g := integralAverage (euclideanBall p' (3 * σ / 2)) u
        set e' := integralAverage (euclideanBall p' σ) u
        set h := integralAverage (euclideanBall x (3 * R / 4)) u
        have : |a - h| ≤ |a - g| + |g - e'| + |e' - h| := by
          calc |a - h| = |(a - g) + (g - e') + (e' - h)| := by ring_nf
            _ ≤ |(a - g) + (g - e')| + |e' - h| := abs_add_le _ _
            _ ≤ |a - g| + |g - e'| + |e' - h| := by gcongr; exact abs_add_le _ _
        have hge : |g - e'| = |e' - g| := abs_sub_comm _ _
        push_cast
        nlinarith [hge]

end PDE.JohnNirenbergBall
