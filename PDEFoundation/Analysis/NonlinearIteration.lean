module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Quantitative nonlinear iteration

This module contains the scalar real-analysis step used by De Giorgi and
Stampacchia iterations.  It deliberately has no geometric, measure-theoretic,
or PDE dependencies.
-/

@[expose] public section

namespace PDE

open Filter Topology

/-- A nonnegative sequence satisfying a compatible superlinear recurrence has
an explicit geometric upper bound. -/
theorem nonlinear_iteration_le_geometric
    {Y : ℕ → ℝ} {A B beta : ℝ}
    (hY0 : Y 0 ≤ 1) (hY_nonneg : ∀ n, 0 ≤ Y n) (hbeta : 0 < beta)
    (hB : 1 ≤ B) (hA : 0 ≤ A) (hAB : A ≤ B ^ (-(1 / beta)))
    (hrec : ∀ n, Y (n + 1) ≤ A * B ^ (n : ℝ) * Y n ^ (1 + beta)) :
    ∀ n, Y n ≤ B ^ (-(n : ℝ) / beta) := by
  have hB_pos : (0 : ℝ) < B := lt_of_lt_of_le one_pos hB
  have hB_nonneg : (0 : ℝ) ≤ B := hB_pos.le
  have hbeta_ne_zero : beta ≠ 0 := ne_of_gt hbeta
  intro n
  induction n with
  | zero =>
      simpa only [Nat.cast_zero, neg_zero, zero_div, Real.rpow_zero] using hY0
  | succ n ih =>
      have h_one_add_beta_nonneg : (0 : ℝ) ≤ 1 + beta := by linarith
      have hpower : Y n ^ (1 + beta) ≤
          (B ^ (-(n : ℝ) / beta)) ^ (1 + beta) :=
        Real.rpow_le_rpow (hY_nonneg n) ih h_one_add_beta_nonneg
      have hpower_eq :
          (B ^ (-(n : ℝ) / beta)) ^ (1 + beta) =
            B ^ ((-(n : ℝ) / beta) * (1 + beta)) :=
        (Real.rpow_mul hB_nonneg _ _).symm
      have hfactor_nonneg : 0 ≤ A * B ^ (n : ℝ) :=
        mul_nonneg hA (Real.rpow_nonneg hB_nonneg _)
      have hexponent :
          (n : ℝ) + (-(n : ℝ) / beta) * (1 + beta) = -(n : ℝ) / beta := by
        field_simp
        ring
      calc
        Y (n + 1) ≤ A * B ^ (n : ℝ) * Y n ^ (1 + beta) := hrec n
        _ ≤ A * B ^ (n : ℝ) * (B ^ (-(n : ℝ) / beta)) ^ (1 + beta) :=
          mul_le_mul_of_nonneg_left hpower hfactor_nonneg
        _ = A * B ^ (-(n : ℝ) / beta) := by
          rw [hpower_eq, mul_assoc, ← Real.rpow_add hB_pos, hexponent]
        _ ≤ B ^ (-(1 / beta)) * B ^ (-(n : ℝ) / beta) :=
          mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg hB_nonneg _)
        _ = B ^ (-((n + 1 : ℕ) : ℝ) / beta) := by
          rw [← Real.rpow_add hB_pos]
          congr 1
          push_cast
          ring

/-- A nonnegative sequence satisfying a compatible superlinear recurrence
converges to zero when its geometric base is strictly larger than one. -/
theorem nonlinear_iteration_tendsto_zero
    {Y : ℕ → ℝ} {A B beta : ℝ}
    (hY0 : Y 0 ≤ 1) (hY_nonneg : ∀ n, 0 ≤ Y n) (hbeta : 0 < beta)
    (hB : 1 < B) (hA : 0 ≤ A) (hAB : A ≤ B ^ (-(1 / beta)))
    (hrec : ∀ n, Y (n + 1) ≤ A * B ^ (n : ℝ) * Y n ^ (1 + beta)) :
    Tendsto Y atTop (𝓝 0) := by
  have hbound :=
    nonlinear_iteration_le_geometric hY0 hY_nonneg hbeta hB.le hA hAB hrec
  have hB_nonneg : (0 : ℝ) ≤ B := (lt_trans one_pos hB).le
  let q : ℝ := B ^ (-(1 / beta))
  have hq_nonneg : 0 ≤ q := Real.rpow_nonneg hB_nonneg _
  have hq_lt_one : q < 1 := by
    dsimp only [q]
    refine Real.rpow_lt_one_of_one_lt_of_neg hB ?_
    have h_inv_beta_pos : (0 : ℝ) < 1 / beta := by positivity
    linarith
  have hgeometric : Tendsto (fun n : ℕ => q ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq_nonneg hq_lt_one
  have hgeometric_eq : ∀ n : ℕ, B ^ (-(n : ℝ) / beta) = q ^ n := by
    intro n
    dsimp only [q]
    rw [← Real.rpow_natCast (B ^ (-(1 / beta))) n,
      ← Real.rpow_mul hB_nonneg]
    congr 1
    ring
  refine squeeze_zero hY_nonneg (fun n => ?_) hgeometric
  rw [← hgeometric_eq n]
  exact hbound n

/-- A superlinear recurrence with sufficiently small initial data has an
explicit geometric upper bound.  The smallness threshold is the exact factor
which makes the rescaled leading coefficient equal to `B ^ (-(1 / beta))`. -/
theorem nonlinear_iteration_le_geometric_of_initial_small
    {Y : ℕ → ℝ} {A B beta : ℝ}
    (hA_pos : 0 < A) (hB : 1 < B) (hbeta : 0 < beta)
    (hY0 : Y 0 ≤ A ^ (-(1 / beta)) * B ^ (-(1 / beta ^ 2)))
    (hY_nonneg : ∀ n, 0 ≤ Y n)
    (hrec : ∀ n, Y (n + 1) ≤ A * B ^ (n : ℝ) * Y n ^ (1 + beta)) :
    ∀ n, Y n ≤
      (A ^ (-(1 / beta)) * B ^ (-(1 / beta ^ 2))) *
        B ^ (-(n : ℝ) / beta) := by
  let C : ℝ := A ^ (-(1 / beta)) * B ^ (-(1 / beta ^ 2))
  let Z : ℕ → ℝ := fun n => Y n / C
  have hB_pos : (0 : ℝ) < B := lt_trans one_pos hB
  have hC_pos : 0 < C := by
    dsimp only [C]
    positivity
  have hC_nonneg : 0 ≤ C := hC_pos.le
  have hC_ne_zero : C ≠ 0 := hC_pos.ne'
  have hZ0 : Z 0 ≤ 1 := by
    rw [show Z 0 = Y 0 / C from rfl, div_le_one hC_pos]
    simpa only [C] using hY0
  have hZ_nonneg : ∀ n, 0 ≤ Z n := fun n =>
    div_nonneg (hY_nonneg n) hC_nonneg
  have hcoefficient : A * C ^ beta = B ^ (-(1 / beta)) := by
    have hA_exponent : 1 + (-(1 / beta)) * beta = 0 := by
      field_simp
      ring
    have hB_exponent : (-(1 / beta ^ 2)) * beta = -(1 / beta) := by
      field_simp
    have hA_rpow : (A ^ (-(1 / beta))) ^ beta =
        A ^ ((-(1 / beta)) * beta) :=
      (Real.rpow_mul hA_pos.le _ _).symm
    have hB_rpow : (B ^ (-(1 / beta ^ 2))) ^ beta =
        B ^ ((-(1 / beta ^ 2)) * beta) :=
      (Real.rpow_mul hB_pos.le _ _).symm
    have hA_cancel : A * A ^ ((-(1 / beta)) * beta) = 1 := by
      calc
        A * A ^ ((-(1 / beta)) * beta) =
            A ^ 1 * A ^ ((-(1 / beta)) * beta) := by
          rw [Real.rpow_one]
        _ = A ^ (1 + (-(1 / beta)) * beta) :=
          (Real.rpow_add hA_pos _ _).symm
        _ = 1 := by rw [hA_exponent, Real.rpow_zero]
    calc
      A * C ^ beta =
          A * (A ^ (-(1 / beta)) * B ^ (-(1 / beta ^ 2))) ^ beta := by
        rfl
      _ = A * ((A ^ (-(1 / beta))) ^ beta *
          (B ^ (-(1 / beta ^ 2))) ^ beta) := by
        rw [Real.mul_rpow
          (Real.rpow_nonneg hA_pos.le _)
          (Real.rpow_nonneg hB_pos.le _)]
      _ =
          (A * A ^ ((-(1 / beta)) * beta)) *
            B ^ ((-(1 / beta ^ 2)) * beta) := by
        rw [hA_rpow, hB_rpow]
        ring
      _ = B ^ (-(1 / beta)) := by
        rw [hA_cancel, one_mul, hB_exponent]
  have hZ_rec : ∀ n, Z (n + 1) ≤
      (A * C ^ beta) * B ^ (n : ℝ) * Z n ^ (1 + beta) := by
    intro n
    rw [show Z (n + 1) = Y (n + 1) / C from rfl,
      div_le_iff₀ hC_pos]
    calc
      Y (n + 1) ≤ A * B ^ (n : ℝ) * Y n ^ (1 + beta) := hrec n
      _ = ((A * C ^ beta) * B ^ (n : ℝ) * Z n ^ (1 + beta)) * C := by
        rw [show Z n = Y n / C from rfl,
          Real.div_rpow (hY_nonneg n) hC_nonneg]
        have hC_power : C ^ (1 + beta) = C * C ^ beta := by
          rw [Real.rpow_add hC_pos, Real.rpow_one]
        rw [hC_power]
        field_simp [hC_ne_zero]
  have hZ_bound := nonlinear_iteration_le_geometric
    hZ0 hZ_nonneg hbeta hB.le (by positivity) (by rw [hcoefficient]) hZ_rec
  intro n
  rw [show Y n = C * Z n by
    rw [show Z n = Y n / C from rfl]
    field_simp [hC_ne_zero]]
  apply mul_le_mul_of_nonneg_left (hZ_bound n) hC_nonneg

/-- A superlinear recurrence with sufficiently small initial data converges
to zero.  The threshold is displayed explicitly in terms of all recurrence
parameters. -/
theorem nonlinear_iteration_tendsto_zero_of_initial_small
    {Y : ℕ → ℝ} {A B beta : ℝ}
    (hA_pos : 0 < A) (hB : 1 < B) (hbeta : 0 < beta)
    (hY0 : Y 0 ≤ A ^ (-(1 / beta)) * B ^ (-(1 / beta ^ 2)))
    (hY_nonneg : ∀ n, 0 ≤ Y n)
    (hrec : ∀ n, Y (n + 1) ≤ A * B ^ (n : ℝ) * Y n ^ (1 + beta)) :
    Tendsto Y atTop (𝓝 0) := by
  have hbound := nonlinear_iteration_le_geometric_of_initial_small
    hA_pos hB hbeta hY0 hY_nonneg hrec
  let C : ℝ := A ^ (-(1 / beta)) * B ^ (-(1 / beta ^ 2))
  let q : ℝ := B ^ (-(1 / beta))
  have hC_nonneg : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hB_nonneg : (0 : ℝ) ≤ B := (lt_trans one_pos hB).le
  have hq_nonneg : 0 ≤ q := Real.rpow_nonneg hB_nonneg _
  have hq_lt_one : q < 1 := by
    dsimp only [q]
    refine Real.rpow_lt_one_of_one_lt_of_neg hB ?_
    have h_inv_beta_pos : (0 : ℝ) < 1 / beta := by positivity
    linarith
  have hgeometric : Tendsto (fun n : ℕ => C * q ^ n) atTop (𝓝 0) :=
    by simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq_nonneg hq_lt_one).const_mul C
  have hgeometric_eq : ∀ n : ℕ,
      C * q ^ n =
        (A ^ (-(1 / beta)) * B ^ (-(1 / beta ^ 2))) *
          B ^ (-(n : ℝ) / beta) := by
    intro n
    dsimp only [C, q]
    rw [← Real.rpow_natCast (B ^ (-(1 / beta))) n,
      ← Real.rpow_mul hB_nonneg]
    congr 1
    field_simp
  refine squeeze_zero hY_nonneg (fun n => ?_) hgeometric
  rw [hgeometric_eq n]
  exact hbound n

end PDE
