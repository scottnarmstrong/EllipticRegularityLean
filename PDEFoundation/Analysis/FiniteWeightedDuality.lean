module

public import PDEFoundation.Analysis.FiniteWeightedInterpolation

@[expose] public section

open scoped BigOperators

namespace PDE

variable {κ : Type*}

private theorem abs_sign_mul_rpow (x r : ℝ) (hr : 0 < r) :
    |(SignType.sign x : ℝ) * |x| ^ r| = |x| ^ r := by
  by_cases hx : x = 0
  · subst x
    simp [Real.zero_rpow hr.ne']
  · rcases lt_or_gt_of_ne hx with hxNeg | hxPos
    · rw [sign_neg hxNeg]
      simp [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) _)]
    · rw [sign_pos hxPos]
      simp [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) _)]

/-- A bound against every normalized weighted dual vector controls the finite
weighted `L^p` norm. -/
theorem weighted_lp_le_of_normalized_pairing
    [Fintype κ] (v : κ → ℝ) (hv : ∀ j, 0 ≤ v j)
    (p M : ℝ) (hp : 1 < p) (hM : 0 ≤ M) (y : κ → ℝ)
    (hpair : ∀ g : κ → ℝ,
      ∑ j, v j * |g j| ^ (p / (p - 1)) = 1 →
        |∑ j, v j * y j * g j| ≤ M) :
    (∑ j, v j * |y j| ^ p) ^ (1 / p) ≤ M := by
  let S : ℝ := ∑ j, v j * |y j| ^ p
  have hpPos : 0 < p := zero_lt_one.trans hp
  have hpSubPos : 0 < p - 1 := sub_pos.mpr hp
  have hSNonneg : 0 ≤ S :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hv j) (Real.rpow_nonneg (abs_nonneg _) _)
  obtain hS | hS := hSNonneg.eq_or_lt
  · change S ^ (1 / p) ≤ M
    rw [← hS, Real.zero_rpow (one_div_ne_zero hpPos.ne')]
    exact hM
  · let q : ℝ := p / (p - 1)
    let D : ℝ := S ^ ((p - 1) / p)
    have hqPos : 0 < q := div_pos hpPos hpSubPos
    have hDPos : 0 < D := Real.rpow_pos_of_pos hS _
    let g : κ → ℝ := fun j =>
      (SignType.sign (y j) : ℝ) * |y j| ^ (p - 1) / D
    have habs (j : κ) : |g j| = |y j| ^ (p - 1) / D := by
      dsimp only [g]
      rw [abs_div, abs_of_pos hDPos, abs_sign_mul_rpow (y j) (p - 1) hpSubPos]
    have hgpow (j : κ) : |g j| ^ q = |y j| ^ p / S := by
      rw [habs, Real.div_rpow (Real.rpow_nonneg (abs_nonneg _) _) hDPos.le,
        ← Real.rpow_mul (abs_nonneg _), ← Real.rpow_mul hS.le]
      dsimp only [q, D]
      rw [show (p - 1) * (p / (p - 1)) = p by
        field_simp [hpSubPos.ne']]
      rw [show (p - 1) / p * (p / (p - 1)) = 1 by
        field_simp [hpSubPos.ne', hpPos.ne'], Real.rpow_one]
    have hgnorm : ∑ j, v j * |g j| ^ q = 1 := by
      simp_rw [hgpow]
      simp_rw [show ∀ j, v j * (|y j| ^ p / S) = (v j * |y j| ^ p) / S by
        intro j; ring]
      rw [← Finset.sum_div]
      change S / S = 1
      exact div_self hS.ne'
    have hypair (j : κ) : y j * g j = |y j| ^ p / D := by
      dsimp only [g]
      rw [← mul_div_assoc]
      congr 1
      rcases lt_trichotomy (y j) 0 with hyNeg | hyZero | hyPos
      · rw [sign_neg hyNeg, abs_of_neg hyNeg]
        simp only [SignType.coe_neg, SignType.coe_one]
        calc
          y j * (-1 * (-y j) ^ (p - 1)) = (-y j) * (-y j) ^ (p - 1) := by ring
          _ = (-y j) ^ (1 : ℝ) * (-y j) ^ (p - 1) := by rw [Real.rpow_one]
          _ = (-y j) ^ (1 + (p - 1)) :=
            (Real.rpow_add (neg_pos.mpr hyNeg) 1 (p - 1)).symm
          _ = (-y j) ^ p := by
            congr 1
            ring
      · rw [hyZero]
        simp [Real.zero_rpow hpPos.ne', Real.zero_rpow hpSubPos.ne']
      · rw [sign_pos hyPos, abs_of_pos hyPos]
        simp only [SignType.coe_one]
        calc
          y j * (1 * y j ^ (p - 1)) = y j * y j ^ (p - 1) := by ring
          _ = y j ^ (1 : ℝ) * y j ^ (p - 1) := by rw [Real.rpow_one]
          _ = y j ^ (1 + (p - 1)) := (Real.rpow_add hyPos 1 (p - 1)).symm
          _ = y j ^ p := by
            congr 1
            ring
    have hpairValue : ∑ j, v j * y j * g j = S ^ (1 / p) := by
      simp_rw [mul_assoc]
      simp_rw [hypair]
      simp_rw [show ∀ j, v j * (|y j| ^ p / D) = (v j * |y j| ^ p) / D by
        intro j; ring]
      rw [← Finset.sum_div]
      change S / D = S ^ (1 / p)
      apply (div_eq_iff hDPos.ne').mpr
      dsimp only [D]
      rw [← Real.rpow_add hS]
      rw [show 1 / p + (p - 1) / p = 1 by
        field_simp [hpPos.ne']
        ring, Real.rpow_one]
    have h := hpair g (by simpa only [q] using hgnorm)
    rw [hpairValue, abs_of_nonneg (Real.rpow_nonneg hS.le _)] at h
    exact h

end PDE
