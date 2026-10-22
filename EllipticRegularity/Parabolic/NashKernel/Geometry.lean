module

public import PDEFoundation.Geometry.EuclideanBall.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Geometric and analytic lemmas for the pointwise Nash-Aronson kernel bounds

Self-contained (no PDE) lemmas used to pass from the integrated Gaussian bounds to pointwise kernel
bounds:

* the absorption inequality turning the `nashAronsonUpper` exponent into a pure Gaussian,
* inclusion of a supremum-norm ball (a cube, used on purpose for Lebesgue differentiation) in a
  round `euclideanBall`,
* the shrinking of the Euclidean distance between two cubes.

`Metric.closedBall` on `Vec d` is a cube; round balls are `euclideanBall`.
-/

@[expose] public section

namespace PDE.NashKernelGeometry

open Real

/-- AM-GM: `-ρ²/4 + kρ ≤ -ρ²/8 + 2k²`. -/
theorem absorb_aux (ρ k : ℝ) : -ρ ^ 2 / 4 + k * ρ ≤ -ρ ^ 2 / 8 + 2 * k ^ 2 := by
  nlinarith [sq_nonneg (ρ - 4 * k)]

/-- The absorption inequality with `k = √((d+2)/2)`, for `ρ ≥ 0` (in fact for all `ρ`). -/
theorem absorb (d : ℕ) (ρ : ℝ) :
    -ρ ^ 2 / 4 + Real.sqrt (((d : ℝ) + 2) / 2) * ρ ≤ -ρ ^ 2 / 8 + ((d : ℝ) + 2) := by
  have h := absorb_aux ρ (Real.sqrt (((d : ℝ) + 2) / 2))
  have hk : Real.sqrt (((d : ℝ) + 2) / 2) ^ 2 = ((d : ℝ) + 2) / 2 :=
    Real.sq_sqrt (by positivity)
  rw [hk] at h
  linarith

/-- The exponent of `nashAronsonUpper` is bounded by the Gaussian exponent plus `d + 2`. -/
theorem upper_exponent_le (d : ℕ) {r Lam h : ℝ} (hLam : 0 < Lam) (hh : 0 < h) :
    -r ^ 2 / (4 * Lam * h) +
        Real.sqrt (((d : ℝ) + 2) / 2) * r / Real.sqrt (Lam * h) ≤
      -r ^ 2 / (8 * Lam * h) + ((d : ℝ) + 2) := by
  have hpos : 0 < Lam * h := mul_pos hLam hh
  have hs : 0 < Real.sqrt (Lam * h) := Real.sqrt_pos.mpr hpos
  have hs2 : Real.sqrt (Lam * h) ^ 2 = Lam * h := Real.sq_sqrt hpos.le
  have key := absorb d (r / Real.sqrt (Lam * h))
  have e1 : (r / Real.sqrt (Lam * h)) ^ 2 = r ^ 2 / (Lam * h) := by
    rw [div_pow, hs2]
  rw [e1] at key
  have e2 : Real.sqrt (((d : ℝ) + 2) / 2) * (r / Real.sqrt (Lam * h)) =
      Real.sqrt (((d : ℝ) + 2) / 2) * r / Real.sqrt (Lam * h) := by ring
  rw [e2] at key
  have e3 : -r ^ 2 / (4 * Lam * h) = -(r ^ 2 / (Lam * h)) / 4 := by
    field_simp
  have e4 : -r ^ 2 / (8 * Lam * h) = -(r ^ 2 / (Lam * h)) / 8 := by
    field_simp
  rw [e3, e4]
  exact key

/-- The Gaussian factor of `nashAronsonUpper` is at most `e^{d+2}` times the pure Gaussian. -/
theorem exp_upper_le (d : ℕ) {r Lam h : ℝ} (hLam : 0 < Lam) (hh : 0 < h) :
    Real.exp (-r ^ 2 / (4 * Lam * h) +
        Real.sqrt (((d : ℝ) + 2) / 2) * r / Real.sqrt (Lam * h)) ≤
      Real.exp ((d : ℝ) + 2) * Real.exp (-r ^ 2 / (8 * Lam * h)) := by
  rw [← Real.exp_add, add_comm]
  exact Real.exp_le_exp.mpr (by simpa [add_comm] using upper_exponent_le d hLam hh)

/-- The bound of `nashAronsonUpper`, with the prefactor, absorbed: for `C ≥ 0`,
`C h^{-d/2} exp(...) ≤ C e^{d+2} h^{-d/2} exp(-r²/(8Λh))`. -/
theorem upper_bound_absorbed (d : ℕ) {C r Lam h : ℝ} (hC : 0 ≤ C) (hLam : 0 < Lam) (hh : 0 < h) :
    C * h ^ (-(d : ℝ) / 2) *
        Real.exp (-r ^ 2 / (4 * Lam * h) +
          Real.sqrt (((d : ℝ) + 2) / 2) * r / Real.sqrt (Lam * h)) ≤
      C * Real.exp ((d : ℝ) + 2) * h ^ (-(d : ℝ) / 2) * Real.exp (-r ^ 2 / (8 * Lam * h)) := by
  have hpow : 0 ≤ h ^ (-(d : ℝ) / 2) := Real.rpow_nonneg hh.le _
  have := mul_le_mul_of_nonneg_left (exp_upper_le d (r := r) hLam hh) (mul_nonneg hC hpow)
  calc _ ≤ C * h ^ (-(d : ℝ) / 2) *
        (Real.exp ((d : ℝ) + 2) * Real.exp (-r ^ 2 / (8 * Lam * h))) := this
    _ = _ := by ring

/-- `√(euclideanSqDist x y)` is the Euclidean norm of `x - y`. -/
theorem sqrt_euclideanSqDist {d : ℕ} (x y : Vec d) :
    Real.sqrt (euclideanSqDist x y) = vecEuclideanNorm (x - y) := rfl

/-- The Euclidean triangle inequality for `√(euclideanSqDist ·)`. -/
theorem sqrt_euclideanSqDist_triangle {d : ℕ} (x y z : Vec d) :
    Real.sqrt (euclideanSqDist x z) ≤
      Real.sqrt (euclideanSqDist x y) + Real.sqrt (euclideanSqDist y z) := by
  rw [sqrt_euclideanSqDist, sqrt_euclideanSqDist, sqrt_euclideanSqDist]
  have : x - z = (x - y) + (y - z) := by abel
  rw [this]
  exact vecEuclideanNorm_add_le _ _

/-- A supremum-norm ball (a cube) of radius `δ` lies in the round Euclidean ball of radius `R`
when `√d δ < R`.  (`Metric.closedBall` on `Vec d` is a cube on purpose.) -/
theorem closedBall_subset_euclideanBall {d : ℕ} {x : Vec d} {δ R : ℝ}
    (h : Real.sqrt d * δ < R) : Metric.closedBall x δ ⊆ euclideanBall x R := by
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have h1 : vecEuclideanNorm (z - x) ≤ Real.sqrt d * ‖z - x‖ :=
    vecEuclideanNorm_le_sqrt_natCast_mul_norm _
  have h2 : Real.sqrt d * ‖z - x‖ ≤ Real.sqrt d * δ :=
    mul_le_mul_of_nonneg_left hz (Real.sqrt_nonneg _)
  have h3 : vecEuclideanNorm (z - x) < R := lt_of_le_of_lt (h1.trans h2) h
  change euclideanSqDist z x < R ^ 2
  have h0 := vecEuclideanNorm_nonneg (z - x)
  have h4 := vecEuclideanNorm_sq (z - x)
  change vecNormSq (z - x) < R ^ 2
  rw [← h4]
  exact pow_lt_pow_left₀ h3 h0 two_ne_zero

/-- Distance shrink for two cubes: points of `closedBall x δ`, `closedBall y δ` have Euclidean
distance at least `√(euclideanSqDist x y) - 2 √d δ`. -/
theorem sqrt_euclideanSqDist_sub_le {d : ℕ} {x y x' y' : Vec d} {δ : ℝ}
    (hx : x' ∈ Metric.closedBall x δ) (hy : y' ∈ Metric.closedBall y δ) :
    Real.sqrt (euclideanSqDist x y) - 2 * Real.sqrt d * δ ≤
      Real.sqrt (euclideanSqDist x' y') := by
  have hx' : Real.sqrt (euclideanSqDist x x') ≤ Real.sqrt d * δ := by
    rw [sqrt_euclideanSqDist]
    rw [Metric.mem_closedBall, dist_eq_norm] at hx
    have := vecEuclideanNorm_le_sqrt_natCast_mul_norm (x - x')
    rw [← norm_neg, neg_sub] at hx
    exact this.trans (mul_le_mul_of_nonneg_left hx (Real.sqrt_nonneg _))
  have hy' : Real.sqrt (euclideanSqDist y' y) ≤ Real.sqrt d * δ := by
    rw [sqrt_euclideanSqDist]
    rw [Metric.mem_closedBall, dist_eq_norm] at hy
    exact (vecEuclideanNorm_le_sqrt_natCast_mul_norm (y' - y)).trans
      (mul_le_mul_of_nonneg_left hy (Real.sqrt_nonneg _))
  have t1 := sqrt_euclideanSqDist_triangle x x' y
  have t3 : Real.sqrt (euclideanSqDist x' y) ≤
      Real.sqrt (euclideanSqDist x' y') + Real.sqrt (euclideanSqDist y' y) :=
    sqrt_euclideanSqDist_triangle x' y' y
  have t4 : Real.sqrt (euclideanSqDist x y) ≤
      Real.sqrt (euclideanSqDist x x') + Real.sqrt (euclideanSqDist x' y) := t1
  linarith

/-- Squared form for the hypothesis `r² ≤ euclideanSqDist` of `nashAronsonUpper`, with
`r = max 0 (√(euclideanSqDist x y) - 2 √d δ)`. -/
theorem sq_max_le_euclideanSqDist {d : ℕ} {x y x' y' : Vec d} {δ : ℝ}
    (hx : x' ∈ Metric.closedBall x δ) (hy : y' ∈ Metric.closedBall y δ) :
    (max 0 (Real.sqrt (euclideanSqDist x y) - 2 * Real.sqrt d * δ)) ^ 2 ≤
      euclideanSqDist x' y' := by
  have h := sqrt_euclideanSqDist_sub_le hx hy
  have h0 := Real.sqrt_nonneg (euclideanSqDist x' y')
  have hm : max 0 (Real.sqrt (euclideanSqDist x y) - 2 * Real.sqrt d * δ) ≤
      Real.sqrt (euclideanSqDist x' y') := max_le h0 h
  calc _ ≤ Real.sqrt (euclideanSqDist x' y') ^ 2 :=
        pow_le_pow_left₀ (le_max_left _ _) hm 2
    _ = _ := Real.sq_sqrt (euclideanSqDist_nonneg _ _)

/-- Squared lower-bound form: points of the two cubes have
`euclideanSqDist x' y' ≤ (√(euclideanSqDist x y) + 2 √d δ)²`. -/
theorem euclideanSqDist_le_sq_add {d : ℕ} {x y x' y' : Vec d} {δ : ℝ}
    (hx : x' ∈ Metric.closedBall x δ) (hy : y' ∈ Metric.closedBall y δ) :
    euclideanSqDist x' y' ≤
      (Real.sqrt (euclideanSqDist x y) + 2 * Real.sqrt d * δ) ^ 2 := by
  have hx' : Real.sqrt (euclideanSqDist x' x) ≤ Real.sqrt d * δ := by
    rw [sqrt_euclideanSqDist]
    rw [Metric.mem_closedBall, dist_eq_norm] at hx
    exact (vecEuclideanNorm_le_sqrt_natCast_mul_norm (x' - x)).trans
      (mul_le_mul_of_nonneg_left hx (Real.sqrt_nonneg _))
  have hy' : Real.sqrt (euclideanSqDist y y') ≤ Real.sqrt d * δ := by
    rw [sqrt_euclideanSqDist]
    rw [Metric.mem_closedBall, dist_eq_norm] at hy
    rw [← norm_neg, neg_sub] at hy
    exact (vecEuclideanNorm_le_sqrt_natCast_mul_norm (y - y')).trans
      (mul_le_mul_of_nonneg_left hy (Real.sqrt_nonneg _))
  have hle : Real.sqrt (euclideanSqDist x' y') ≤
      Real.sqrt (euclideanSqDist x y) + 2 * Real.sqrt d * δ := by
    have := sqrt_euclideanSqDist_triangle x' x y
    have t5 := sqrt_euclideanSqDist_triangle x' y y'
    linarith
  have h0 := Real.sqrt_nonneg (euclideanSqDist x' y')
  calc euclideanSqDist x' y' = Real.sqrt (euclideanSqDist x' y') ^ 2 :=
        (Real.sq_sqrt (euclideanSqDist_nonneg _ _)).symm
    _ ≤ _ := pow_le_pow_left₀ h0 hle 2

end PDE.NashKernelGeometry
