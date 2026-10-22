module

public import EllipticRegularity.DeGiorgi.MoserIter.Hypotheses
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Algebra.BigOperators.Field

/-!
# Chains of one-step estimates

Abstract iteration of `a (n+1) ≤ ofReal (k n) * a n`, monotonicity of `L^p` norms in the ball
radius, finiteness of the ball measures, and the geometry of the shrinking radii
`1/2 + c 2^{-n}`.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal

namespace PDE.DGNMMoser

/-- Iterating one-step multiplicative estimates gives a product estimate. -/
theorem chain_le (a : ℕ → ℝ≥0∞) (k : ℕ → ℝ) (hk : ∀ n, 0 ≤ k n) (N : ℕ)
    (h : ∀ n < N, a (n + 1) ≤ ENNReal.ofReal (k n) * a n) :
    a N ≤ ENNReal.ofReal (∏ n ∈ range N, k n) * a 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h1 := ih fun n hn => h n (Nat.lt_succ_of_lt hn)
    calc a (N + 1) ≤ ENNReal.ofReal (k N) * a N := h N (Nat.lt_succ_self N)
      _ ≤ ENNReal.ofReal (k N) * (ENNReal.ofReal (∏ n ∈ range N, k n) * a 0) :=
          mul_le_mul' le_rfl h1
      _ = ENNReal.ofReal (∏ n ∈ range (N + 1), k n) * a 0 := by
          rw [prod_range_succ, ENNReal.ofReal_mul (prod_nonneg fun n _ => hk n), ← mul_assoc,
            mul_comm (ENNReal.ofReal (k N))]

/-- The `L^p` seminorm on balls is monotone in the radius. -/
theorem eLpNorm_ball_mono {d : ℕ} (f : Vec d → ℝ) (p : ℝ≥0∞) {r s : ℝ} (hr : 0 ≤ r)
    (hrs : r ≤ s) :
    eLpNorm f p (volumeOn (euclideanBall (0 : Vec d) r)) ≤
      eLpNorm f p (volumeOn (euclideanBall (0 : Vec d) s)) :=
  eLpNorm_mono_measure f (Measure.restrict_mono (euclideanBall_mono hr hrs) le_rfl)

/-- Ball measures are finite. -/
theorem isFiniteMeasure_volumeOn_ball (d : ℕ) {r : ℝ} (hr : 0 < r) :
    IsFiniteMeasure (volumeOn (euclideanBall (0 : Vec d) r)) :=
  (isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) hr).isFiniteMeasure_volumeOn

/-- The shrinking radii `1/2 + c 2^{-n}`. -/
noncomputable def rad (c : ℝ) (n : ℕ) : ℝ := 1 / 2 + c * ((2 : ℝ) ^ n)⁻¹

theorem rad_zero (c : ℝ) : rad c 0 = 1 / 2 + c := by simp [rad]

theorem half_le_rad {c : ℝ} (hc : 0 < c) (n : ℕ) : 1 / 2 ≤ rad c n := by
  unfold rad; have : 0 < c * ((2 : ℝ) ^ n)⁻¹ := by positivity
  linarith

theorem rad_le {c : ℝ} (hc : 0 < c) (n : ℕ) : rad c n ≤ 1 / 2 + c := by
  unfold rad
  have : ((2 : ℝ) ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  nlinarith

theorem rad_sub {c : ℝ} (n : ℕ) : rad c n - rad c (n + 1) = c * ((2 : ℝ) ^ (n + 1))⁻¹ := by
  unfold rad
  rw [pow_succ]
  field_simp
  ring

theorem rad_succ_lt {c : ℝ} (hc : 0 < c) (n : ℕ) : rad c (n + 1) < rad c n := by
  have := rad_sub (c := c) n
  have : 0 < c * ((2 : ℝ) ^ (n + 1))⁻¹ := by positivity
  linarith

/-- `(rad n - rad (n+1))⁻² = (4 / c²) 4^n`. -/
theorem inv_rad_sub_sq {c : ℝ} (hc : 0 < c) (n : ℕ) :
    1 / (rad c n - rad c (n + 1)) ^ 2 = 4 / c ^ 2 * 4 ^ n := by
  rw [rad_sub]
  have h : ((4 : ℝ) ^ n) = ((2 : ℝ) ^ (n + 1)) ^ 2 / 4 := by
    have : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [← pow_mul, this, ← pow_mul]
    rw [show (n + 1) * 2 = n * 2 + 2 by ring, pow_add]; ring
  rw [h]
  field_simp

end PDE.DGNMMoser
