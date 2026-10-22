module

public import PDEFoundation.Analysis.FiniteWeightedDuality

@[expose] public section

open scoped BigOperators

namespace PDE

variable {ι κ : Type*}

theorem weighted_lp_operator_le_of_two_four
    [Fintype ι] [Fintype κ]
    (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ))
    (w : ι → ℝ) (v : κ → ℝ) (hw : ∀ i, 0 ≤ w i) (hv : ∀ j, 0 ≤ v j)
    (p M : ℝ) (hp : 2 ≤ p) (hpFour : p ≤ 4) (hM : 1 ≤ M)
    (hTwo : ∀ x : ι → ℝ,
      ∑ j, v j * (T x j) ^ 2 ≤ M ^ 2 * ∑ i, w i * (x i) ^ 2)
    (hFour : ∀ x : ι → ℝ,
      ∑ j, v j * (T x j) ^ 4 ≤ M ^ 4 * ∑ i, w i * (x i) ^ 4)
    (f : ι → ℝ) :
    (∑ j, v j * |T f j| ^ p) ^ (1 / p) ≤
      M * (∑ i, w i * |f i| ^ p) ^ (1 / p) := by
  let S : ℝ := ∑ i, w i * |f i| ^ p
  have hpPos : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hSNonneg : 0 ≤ S :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (Real.rpow_nonneg (abs_nonneg _) _)
  obtain hS | hS := hSNonneg.eq_or_lt
  · have hterm (i : ι) : w i * |f i| ^ p = 0 := by
      apply (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
        mul_nonneg (hw i) (Real.rpow_nonneg (abs_nonneg _) _)).mp
        (by simpa only [S] using hS.symm)
      simp
    have hinTwo : ∑ i, w i * (f i) ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rcases mul_eq_zero.mp (hterm i) with hwi | hfi
      · simp [hwi]
      · have : f i = 0 := by
          have habs : |f i| = 0 :=
            (Real.rpow_eq_zero (abs_nonneg _) hpPos.ne').mp hfi
          exact abs_eq_zero.mp habs
        simp [this]
    have houtTwo : ∑ j, v j * (T f j) ^ 2 = 0 := by
      apply le_antisymm
      · simpa [hinTwo] using hTwo f
      · exact Finset.sum_nonneg fun j _ => mul_nonneg (hv j) (sq_nonneg _)
    have hout : ∑ j, v j * |T f j| ^ p = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      have htermTwo : v j * (T f j) ^ 2 = 0 := by
        apply (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
          mul_nonneg (hv j) (sq_nonneg _)).mp houtTwo
        simp
      rcases mul_eq_zero.mp htermTwo with hvj | hy
      · simp [hvj]
      · have hy0 : T f j = 0 := (sq_eq_zero_iff).mp hy
        simp [hy0, Real.zero_rpow hpPos.ne']
    rw [show (∑ j, v j * |T f j| ^ p) = 0 from hout]
    change 0 ^ (1 / p) ≤ M * S ^ (1 / p)
    rw [Real.zero_rpow (one_div_ne_zero hpPos.ne'), ← hS,
      Real.zero_rpow (one_div_ne_zero hpPos.ne'), mul_zero]
  · let D : ℝ := S ^ (1 / p)
    have hDPos : 0 < D := Real.rpow_pos_of_pos hS _
    let f' : ι → ℝ := fun i => f i / D
    have hfNorm : ∑ i, w i * |f' i| ^ p = 1 := by
      have hpowD : D ^ p = S := by
        dsimp only [D]
        rw [← Real.rpow_mul hS.le]
        rw [show 1 / p * p = 1 by field_simp [hpPos.ne'], Real.rpow_one]
      simp_rw [f', abs_div, abs_of_pos hDPos,
        Real.div_rpow (abs_nonneg _) hDPos.le, hpowD]
      simp_rw [show ∀ i, w i * (|f i| ^ p / S) = (w i * |f i| ^ p) / S by
        intro i; ring]
      rw [← Finset.sum_div]
      change S / S = 1
      exact div_self hS.ne'
    have hnorm : (∑ j, v j * |T f' j| ^ p) ^ (1 / p) ≤ M := by
      apply weighted_lp_le_of_normalized_pairing v hv p M
        (lt_of_lt_of_le (by norm_num) hp) (zero_le_one.trans hM) (T f')
      intro g hg
      exact abs_weighted_pairing_le_of_two_four T w v hw hv p M hp hpFour hM
        hTwo hFour f' g hfNorm hg
    have hTf' (j : κ) : T f' j = T f j / D := by
      have hf' : f' = D⁻¹ • f := by
        funext i
        simp [f', div_eq_mul_inv, mul_comm]
      rw [hf', T.map_smul]
      simp [div_eq_mul_inv, mul_comm]
    have houtScale : ∑ j, v j * |T f' j| ^ p =
        (∑ j, v j * |T f j| ^ p) / S := by
      simp_rw [hTf', abs_div, abs_of_pos hDPos,
        Real.div_rpow (abs_nonneg _) hDPos.le]
      have hpowD : D ^ p = S := by
        dsimp only [D]
        rw [← Real.rpow_mul hS.le]
        rw [show 1 / p * p = 1 by field_simp [hpPos.ne'], Real.rpow_one]
      rw [hpowD]
      simp_rw [show ∀ j, v j * (|T f j| ^ p / S) =
          (v j * |T f j| ^ p) / S by intro j; ring]
      rw [Finset.sum_div]
    rw [houtScale] at hnorm
    have houtNonneg : 0 ≤ ∑ j, v j * |T f j| ^ p :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hv j) (Real.rpow_nonneg (abs_nonneg _) _)
    rw [Real.div_rpow houtNonneg hS.le] at hnorm
    have hrootS : S ^ (1 / p) = D := rfl
    rw [hrootS] at hnorm ⊢
    -- Clear the normalized denominator using positivity of the input norm.
    calc
      (∑ j, v j * |T f j| ^ p) ^ (1 / p) =
          ((∑ j, v j * |T f j| ^ p) ^ (1 / p) / D) * D := by
            field_simp [hDPos.ne']
      _ ≤ M * D := mul_le_mul_of_nonneg_right hnorm hDPos.le

end PDE
