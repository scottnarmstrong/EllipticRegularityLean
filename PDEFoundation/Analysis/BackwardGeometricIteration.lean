module

public import PDEFoundation.Analysis.CoupledOscillationIteration
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Backward geometric forcing iteration -/

@[expose] public section

namespace PDE

open Filter

/-- Finite expansion of a backward affine recurrence with geometric forcing. -/
theorem backwardGeometricIteration_finite
    {φ : ℕ → ℝ} {A B η ρ : ℝ} (hη : 0 ≤ η) :
    ∀ N, (∀ j < N, φ j ≤ A * ρ ^ j + B + η * φ (j + 1)) → φ 0 ≤
      A * ∑ j ∈ Finset.range N, (η * ρ) ^ j +
        B * ∑ j ∈ Finset.range N, η ^ j + η ^ N * φ N := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      intro hrec
      have htail : η ^ N * φ N ≤
          η ^ N * (A * ρ ^ N + B + η * φ (N + 1)) :=
        mul_le_mul_of_nonneg_left (hrec N (Nat.lt_succ_self N))
          (pow_nonneg hη N)
      calc
        φ 0 ≤ A * ∑ j ∈ Finset.range N, (η * ρ) ^ j +
            B * ∑ j ∈ Finset.range N, η ^ j + η ^ N * φ N :=
          ih (fun j hj => hrec j (Nat.lt_succ_of_lt hj))
        _ ≤ A * ∑ j ∈ Finset.range N, (η * ρ) ^ j +
            B * ∑ j ∈ Finset.range N, η ^ j +
              η ^ N * (A * ρ ^ N + B + η * φ (N + 1)) :=
          add_le_add_right htail _
        _ = A * ∑ j ∈ Finset.range (N + 1), (η * ρ) ^ j +
            B * ∑ j ∈ Finset.range (N + 1), η ^ j +
              η ^ (N + 1) * φ (N + 1) := by
          rw [Finset.sum_range_succ, Finset.sum_range_succ, pow_succ]
          ring

/-- The source backward iteration with `sqrt 2` forcing and feedback at most
one half. The infinite estimate is derived from finite expansions and the
vanishing bounded remainder. -/
theorem backwardSqrtTwoIteration_bound
    {φ : ℕ → ℝ} {A B η M : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hη0 : 0 ≤ η) (hηhalf : η ≤ 1 / 2)
    (hbound : ∀ n, φ n ≤ M)
    (hrec : ∀ j, φ j ≤ A * (Real.sqrt 2) ^ j + B + η * φ (j + 1)) :
    φ 0 ≤ A / (1 - Real.sqrt 2 / 2) + 2 * B := by
  let c := Real.sqrt 2 / 2
  let C := A / (1 - c) + 2 * B
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hc0 : 0 ≤ c := div_nonneg hsqrt (by norm_num)
  have hc1 : c < 1 := by
    dsimp only [c]
    nlinarith
  have hη1 : η < 1 := hηhalf.trans_lt (by norm_num)
  have hq0 : 0 ≤ η * Real.sqrt 2 := mul_nonneg hη0 hsqrt
  have hqle : η * Real.sqrt 2 ≤ c := by
    dsimp only [c]
    nlinarith
  have hq1 : η * Real.sqrt 2 < 1 := hqle.trans_lt hc1
  have hsumq (N : ℕ) :
      (∑ j ∈ Finset.range N, (η * Real.sqrt 2) ^ j) ≤ (1 - c)⁻¹ := by
    have hsum := geometric_sum_le_inv_one_sub hq0 hq1 N
    refine hsum.trans ?_
    have hden : 0 < 1 - c := sub_pos.mpr hc1
    have hdenq : 0 < 1 - η * Real.sqrt 2 := sub_pos.mpr hq1
    rw [inv_le_inv₀ hdenq hden]
    linarith only [hqle]
  have hsumη (N : ℕ) : (∑ j ∈ Finset.range N, η ^ j) ≤ 2 := by
    have hsum := geometric_sum_le_inv_one_sub hη0 hη1 N
    calc
      _ ≤ (1 - η)⁻¹ := hsum
      _ ≤ 2 := by
        have hden : 1 / 2 ≤ 1 - η := by linarith
        calc
          (1 - η)⁻¹ ≤ ((1 / 2 : ℝ))⁻¹ :=
            inv_anti₀ (by norm_num) hden
          _ = 2 := by norm_num
  have hfinite (N : ℕ) : φ 0 ≤ C + η ^ N * M := by
    have hiter := backwardGeometricIteration_finite hη0 N
      (fun j _ => hrec j)
    calc
      φ 0 ≤ A * ∑ j ∈ Finset.range N, (η * Real.sqrt 2) ^ j +
          B * ∑ j ∈ Finset.range N, η ^ j + η ^ N * φ N := hiter
      _ ≤ A * (1 - c)⁻¹ + B * 2 + η ^ N * M := by
        exact add_le_add
          (add_le_add (mul_le_mul_of_nonneg_left (hsumq N) hA)
            (mul_le_mul_of_nonneg_left (hsumη N) hB))
          (mul_le_mul_of_nonneg_left (hbound N) (pow_nonneg hη0 N))
      _ = C + η ^ N * M := by
        dsimp only [C]
        rw [div_eq_mul_inv]
        ring
  have hlim : Tendsto (fun N : ℕ => C + η ^ N * M) atTop (nhds C) := by
    simpa only [zero_mul, add_zero] using
      tendsto_const_nhds.add
        ((tendsto_pow_atTop_nhds_zero_of_lt_one hη0 hη1).mul_const M)
  exact ge_of_tendsto hlim (Eventually.of_forall hfinite)

end PDE
