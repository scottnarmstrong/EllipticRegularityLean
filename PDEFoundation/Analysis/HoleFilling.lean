module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Quantitative hole-filling iteration

This module isolates the scalar arithmetic behind a hole-filling argument.
If an inner energy and an outer energy satisfy

```text
inner ≤ K * (outer - inner),
```

then the exact contraction ratio is `K / (K + 1)`.  Its dyadic iteration is
bounded by a power law with the explicit exponent `1 / (K + 1)`.

The module contains no geometry or PDE data.  A PDE-specific hole-filling
theorem must separately prove the displayed one-step inequality; in the
two-dimensional elliptic application that step uses Poincaré on an annulus.
-/

@[expose] public section

namespace PDE

/-- The exact contraction ratio produced by a hole-filling inequality with
constant `K`. -/
noncomputable def holeFillingRatio (K : ℝ) : ℝ :=
  K / (K + 1)

/-- A safe explicit exponent for converting `holeFillingRatio K` into decay
on dyadic scales. -/
noncomputable def holeFillingDyadicExponent (K : ℝ) : ℝ :=
  1 / (K + 1)

/-- A nonnegative hole-filling constant gives a nonnegative contraction
ratio. -/
theorem holeFillingRatio_nonneg {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ holeFillingRatio K := by
  exact div_nonneg hK (add_nonneg hK zero_le_one)

/-- A nonnegative hole-filling constant gives a strict contraction. -/
theorem holeFillingRatio_lt_one {K : ℝ} (hK : 0 ≤ K) :
    holeFillingRatio K < 1 := by
  exact (div_lt_one (by linarith : 0 < K + 1)).2 (by linarith)

/-- The dyadic decay exponent is positive for every nonnegative hole-filling
constant. -/
theorem holeFillingDyadicExponent_pos {K : ℝ} (hK : 0 ≤ K) :
    0 < holeFillingDyadicExponent K := by
  exact div_pos zero_lt_one (by linarith)

/-- The dyadic decay exponent is at most one for every nonnegative
hole-filling constant. -/
theorem holeFillingDyadicExponent_le_one {K : ℝ} (hK : 0 ≤ K) :
    holeFillingDyadicExponent K ≤ 1 := by
  unfold holeFillingDyadicExponent
  exact (div_le_one (by linarith : 0 < K + 1)).2 (by linarith)

/-- The exact contraction ratio, displayed as `1 - 1 / (K + 1)`. -/
theorem holeFillingRatio_eq_one_sub_inv {K : ℝ} (hK : 0 ≤ K) :
    holeFillingRatio K = 1 - 1 / (K + 1) := by
  unfold holeFillingRatio
  field_simp [show K + 1 ≠ 0 by nlinarith]
  ring

/-- The exact contraction ratio in terms of the named dyadic exponent. -/
theorem holeFillingRatio_eq_one_sub_exponent {K : ℝ} (hK : 0 ≤ K) :
    holeFillingRatio K = 1 - holeFillingDyadicExponent K := by
  simpa only [holeFillingDyadicExponent] using
    (holeFillingRatio_eq_one_sub_inv hK)

/-- Reorganize one hole-filling inequality into its exact contraction form. -/
theorem inner_le_holeFillingRatio_mul_outer
    {K inner outer : ℝ} (hK : 0 ≤ K)
    (hfill : inner ≤ K * (outer - inner)) :
    inner ≤ holeFillingRatio K * outer := by
  unfold holeFillingRatio
  rw [show K / (K + 1) * outer = (K * outer) / (K + 1) by
    field_simp]
  apply (le_div_iff₀ (by nlinarith : 0 < K + 1)).2
  nlinarith

/-- Reorganize one hole-filling inequality with the contraction displayed as
`1 - 1 / (K + 1)`. -/
theorem inner_le_one_sub_inv_mul_outer
    {K inner outer : ℝ} (hK : 0 ≤ K)
    (hfill : inner ≤ K * (outer - inner)) :
    inner ≤ (1 - 1 / (K + 1)) * outer := by
  rw [← holeFillingRatio_eq_one_sub_inv hK]
  exact inner_le_holeFillingRatio_mul_outer hK hfill

/-- Iterate a nonnegative one-step contraction, retaining the exact factor
`q ^ n`. -/
theorem iterate_contraction
    {E : ℕ → ℝ} {q : ℝ} (hq : 0 ≤ q)
    (hstep : ∀ n, E (n + 1) ≤ q * E n) :
    ∀ n, E n ≤ q ^ n * E 0 := by
  intro n
  induction n with
  | zero =>
      simpa only [pow_zero, one_mul] using (le_refl (E 0))
  | succ n ih =>
      calc
        E (n + 1) ≤ q * E n := hstep n
        _ ≤ q * (q ^ n * E 0) :=
          mul_le_mul_of_nonneg_left ih hq
        _ = q ^ (n + 1) * E 0 := by
          rw [pow_succ]
          ring

/-- Iterate a hole-filling inequality while retaining the exact ratio
`(K / (K + 1)) ^ n`. -/
theorem holeFilling_iterate
    {E : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hfill : ∀ n, E (n + 1) ≤ K * (E n - E (n + 1))) :
    ∀ n, E n ≤ holeFillingRatio K ^ n * E 0 := by
  apply iterate_contraction (holeFillingRatio_nonneg hK)
  intro n
  exact inner_le_holeFillingRatio_mul_outer hK (hfill n)

/-- The elementary comparison `1 - δ ≤ 2⁻ᵟ`, used to turn a contraction
into decay on dyadic scales. -/
theorem one_sub_le_two_rpow_neg {δ : ℝ} (hδ : 0 ≤ δ) :
    1 - δ ≤ (2 : ℝ) ^ (-δ) := by
  have hlog_two_le_one : Real.log 2 ≤ 1 := by
    have hlog :=
      Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at hlog ⊢
    exact hlog
  calc
    1 - δ ≤ Real.exp (-δ) := Real.one_sub_le_exp_neg δ
    _ ≤ Real.exp (Real.log 2 * (-δ)) := by
      rw [Real.exp_le_exp]
      nlinarith
    _ = (2 : ℝ) ^ (-δ) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- The exact hole-filling ratio is no larger than the dyadic power-law
factor carrying exponent `1 / (K + 1)`. -/
theorem holeFillingRatio_le_two_rpow_neg_exponent
    {K : ℝ} (hK : 0 ≤ K) :
    holeFillingRatio K ≤
      (2 : ℝ) ^ (-holeFillingDyadicExponent K) := by
  rw [holeFillingRatio_eq_one_sub_exponent hK]
  exact one_sub_le_two_rpow_neg
    (holeFillingDyadicExponent_pos hK).le

/-- The `n`th power of the exact contraction is bounded by the explicit
dyadic power law. -/
theorem holeFillingRatio_pow_le_dyadicPower
    {K : ℝ} (hK : 0 ≤ K) (n : ℕ) :
    holeFillingRatio K ^ n ≤
      (2 : ℝ) ^ (-holeFillingDyadicExponent K * (n : ℝ)) := by
  calc
    holeFillingRatio K ^ n ≤
        ((2 : ℝ) ^ (-holeFillingDyadicExponent K)) ^ n :=
      pow_le_pow_left₀ (holeFillingRatio_nonneg hK)
        (holeFillingRatio_le_two_rpow_neg_exponent hK) n
    _ = (2 : ℝ) ^
        (-holeFillingDyadicExponent K * (n : ℝ)) :=
      (Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)
        (-holeFillingDyadicExponent K) n).symm

/-- Quantitative dyadic decay from a hole-filling inequality.  The exponent
is exactly the displayed quantity `1 / (K + 1)`; no asymptotic dependence is
hidden in the theorem. -/
theorem holeFilling_dyadic_decay
    {E : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K) (hE0 : 0 ≤ E 0)
    (hfill : ∀ n, E (n + 1) ≤ K * (E n - E (n + 1))) :
    ∀ n, E n ≤
      (2 : ℝ) ^ (-holeFillingDyadicExponent K * (n : ℝ)) * E 0 := by
  intro n
  calc
    E n ≤ holeFillingRatio K ^ n * E 0 :=
      holeFilling_iterate hK hfill n
    _ ≤ (2 : ℝ) ^
        (-holeFillingDyadicExponent K * (n : ℝ)) * E 0 :=
      mul_le_mul_of_nonneg_right
        (holeFillingRatio_pow_le_dyadicPower hK n) hE0

/-- For `K ≥ 1`, the explicit dyadic exponent has the sharp lower order
`1 / K`, with numerical factor `1 / 2`. -/
theorem holeFillingDyadicExponent_lowerBound
    {K : ℝ} (hK : 1 ≤ K) :
    1 / (2 * K) ≤ holeFillingDyadicExponent K := by
  unfold holeFillingDyadicExponent
  exact one_div_le_one_div_of_le (by nlinarith : 0 < K + 1) (by nlinarith)

/-- If the one-step constant is `C * sqrt κ`, the dyadic decay exponent has
the required sharp order `κ⁻¹ᐟ²`, with every factor displayed. -/
theorem holeFillingDyadicExponent_mul_sqrt_lowerBound
    {C κ : ℝ} (hlarge : 1 ≤ C * Real.sqrt κ) :
    1 / (2 * C * Real.sqrt κ) ≤
      holeFillingDyadicExponent (C * Real.sqrt κ) := by
  simpa only [mul_assoc] using
    (holeFillingDyadicExponent_lowerBound
      (K := C * Real.sqrt κ) hlarge)

end PDE
