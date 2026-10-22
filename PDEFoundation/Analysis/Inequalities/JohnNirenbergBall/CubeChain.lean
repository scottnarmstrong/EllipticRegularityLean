module

public import PDEFoundation.Analysis.Inequalities.JohnNirenbergBall.Chain

/-!
# Comparison of a boundary-layer cube average with the average over `H` (Step 2)

For a cube `Q` of side `ℓ` with `√d ℓ / 2 = R 2⁻ᵏ / 8` whose center `c` has boundary distance
`σ(c) = R - |c - x| ∈ [3/8, 9/8] R 2⁻ᵏ`, we show that the closed circumscribed ball of `Q` lies in
`B_R(x)` and `|(u)_Q - (u)_H| ≤ K (k + 1) M` with `K = ω + 5 ^ d + 3 ^ (d + 1)`.
-/

@[expose] public section

namespace PDE.JohnNirenbergBall

open BoxIntegral MeasureTheory Set PDE.JohnNirenberg
open scoped ENNReal

variable {d : ℕ} {u : Vec d → ℝ} {M R : ℝ} {x : Vec d}

/-- The constant `K(d)` of display (1.35). -/
noncomputable def chainConst (d : ℕ) : ℝ := cubeBallRatio d + 5 ^ d + 3 ^ (d + 1)

theorem chainConst_pos (hd : 0 < d) : 0 < chainConst d := by
  have := cubeBallRatio_pos hd
  unfold chainConst; positivity

/-- The closed circumscribed ball of a boundary-layer cube lies in `B_R(x)`. -/
theorem closedBall_subset_of_boundaryLayer (hR : 0 < R) (k : ℕ) {c : Vec d}
    (hσ : 3 / 8 * (R / 2 ^ k) ≤ R - vecEuclideanNorm (c - x)) :
    euclideanClosedBall c (R / 2 ^ k / 8) ⊆ euclideanBall x R := by
  have hp : 0 < R / 2 ^ k := by positivity
  apply euclideanClosedBall_subset_ball_of_norm_add_lt (by positivity)
  linarith

/-- Step 2: comparison `|(u)_Q - (u)_H| ≤ K (k + 1) M`. -/
theorem abs_integralAverage_box_sub_H_le (hd : 0 < d) (hR : 0 < R)
    (hloc : LocallyIntegrableOn u (euclideanBall x R) volume)
    (hM : BMOBound (euclideanBall x R) u M) (hM0 : 0 ≤ M) (k : ℕ) (Q : Box (Fin d)) {ℓ : ℝ}
    (hwidth : ∀ i, Q.upper i - Q.lower i = ℓ) (hℓ : Real.sqrt d * ℓ / 2 = R / 2 ^ k / 8)
    (hσ : 3 / 8 * (R / 2 ^ k) ≤ R - vecEuclideanNorm (boxCenter Q - x))
    (hσ' : R - vecEuclideanNorm (boxCenter Q - x) ≤ 9 / 8 * (R / 2 ^ k)) :
    |integralAverage (Q : Set (Vec d)) u - integralAverage (euclideanBall x (3 * R / 4)) u| ≤
      chainConst d * (k + 1) * M := by
  set c := boxCenter Q
  set σ := R - vecEuclideanNorm (c - x) with hσdef
  set ρ := R / 2 ^ k / 8 with hρdef
  have hp : 0 < R / 2 ^ k := by positivity
  have hρ : 0 < ρ := by positivity
  have hQU : euclideanClosedBall c (Real.sqrt d * ℓ / 2) ⊆ euclideanBall x R := by
    rw [hℓ]; exact closedBall_subset_of_boundaryLayer hR k hσ
  have hb := (box_oscillation_bounds hd hloc hM Q hwidth hQU).2.1
  rw [hℓ] at hb
  have hσpos : 0 < σ := by linarith
  have hsub : euclideanBall c ρ ⊆ euclideanBall c (σ / 2) :=
    euclideanBall_mono hρ.le (by rw [hρdef]; linarith)
  have hG : vecEuclideanNorm (c - x) + σ / 2 < R := by rw [hσdef]; linarith
  have n1 := abs_integralAverage_ball_sub_le hloc hM (z := c) (y := c) (ρ := ρ) (r := σ / 2)
    hρ (by positivity) hsub hG
  have hratio : (σ / 2 / ρ) ^ d ≤ 5 ^ d := by
    apply pow_le_pow_left₀ (by positivity)
    rw [div_le_iff₀ hρ, hρdef]; nlinarith
  have hchain := abs_integralAverage_sub_integralAverage_H_le hR hloc hM hM0 (k + 1) c
    (by
      have : R / 2 ^ (k + 1 + 1) ≤ 3 / 8 * (R / 2 ^ k) := by
        rw [pow_succ, pow_succ]
        rw [show R / (2 ^ k * 2 * 2) = 1 / 4 * (R / 2 ^ k) by field_simp; norm_num]
        linarith
      linarith)
  set a := integralAverage (Q : Set (Vec d)) u
  set b := integralAverage (euclideanBall c ρ) u
  set e := integralAverage (euclideanBall c (σ / 2)) u
  set h := integralAverage (euclideanBall x (3 * R / 4)) u
  have hK : 1 ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
  have hω := cubeBallRatio_pos hd
  have h1 : (1 : ℝ) ≤ 3 ^ d := one_le_pow₀ (by norm_num)
  have h5 : (1 : ℝ) ≤ 5 ^ d := one_le_pow₀ (by norm_num)
  have n1' : |b - e| ≤ 5 ^ d * M := n1.trans (mul_le_mul_of_nonneg_right hratio hM0)
  have htri : |a - h| ≤ |a - b| + |b - e| + |e - h| := by
    calc |a - h| = |(a - b) + (b - e) + (e - h)| := by ring_nf
      _ ≤ |(a - b) + (b - e)| + |e - h| := abs_add_le _ _
      _ ≤ |a - b| + |b - e| + |e - h| := by gcongr; exact abs_add_le _ _
  have hchain' : |e - h| ≤ (3 ^ d + 2 * 3 ^ d * ((k + 1 : ℕ) : ℝ)) * M := hchain
  unfold chainConst
  push_cast at hK hchain' ⊢
  have h3d : (3 : ℝ) ^ (d + 1) = 3 * 3 ^ d := by ring
  rw [h3d]
  nlinarith [mul_nonneg hM0 (sub_nonneg.mpr hK), mul_nonneg hM0 (sub_nonneg.mpr h1),
    mul_nonneg hM0 (sub_nonneg.mpr h5), mul_nonneg hM0 hω.le,
    mul_nonneg (mul_nonneg hM0 (sub_nonneg.mpr hK)) hω.le,
    mul_nonneg (mul_nonneg hM0 (sub_nonneg.mpr hK)) (sub_nonneg.mpr h5),
    mul_nonneg (mul_nonneg hM0 (sub_nonneg.mpr hK)) (sub_nonneg.mpr h1)]

end PDE.JohnNirenbergBall
