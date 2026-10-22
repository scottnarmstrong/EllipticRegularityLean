module

public import PDEFoundation.Analysis.AnalyticPowerFamily
public import PDEFoundation.Analysis.ComplexWeightedEndpoints
public import PDEFoundation.Analysis.FiniteWeightedHolder

@[expose] public section

open scoped BigOperators

namespace PDE

variable {ι κ : Type*}

private theorem rpow_inv_nat_sq (M : ℝ) (hM : 0 ≤ M) (n : ℕ) (hn : n ≠ 0) :
    (M ^ n) ^ (1 / (n : ℝ)) = M := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hM]
  rw [show (n : ℝ) * (1 / (n : ℝ)) = 1 by
    field_simp [Nat.cast_ne_zero.mpr hn], Real.rpow_one]

/-- The normalized analytic pairing obeys the quadratic boundary estimate. -/
theorem norm_powerFamilyPairing_zero_le
    [Fintype ι] [Fintype κ]
    (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ))
    (w : ι → ℝ) (v : κ → ℝ) (hw : ∀ i, 0 ≤ w i) (hv : ∀ j, 0 ≤ v j)
    (p M : ℝ) (hp : 2 ≤ p) (hM : 1 ≤ M)
    (hT : ∀ x : ι → ℝ,
      ∑ j, v j * (T x j) ^ 2 ≤ M ^ 2 * ∑ i, w i * (x i) ^ 2)
    (f : ι → ℝ) (g : κ → ℝ)
    (hf : ∑ i, w i * |f i| ^ p = 1)
    (hg : ∑ j, v j * |g j| ^ (p / (p - 1)) = 1)
    (z : ℂ) (hz : z.re = 0) :
    ‖∑ j, (v j : ℂ) *
      coordinatewiseComplexification T
        (fun i => analyticPowerFamilyTerm (f i) (-(p / 4)) (p / 2) z) j *
      analyticPowerFamilyTerm (g j) ((p / (p - 1)) / 4)
        ((p / (p - 1)) / 2) z‖ ≤ M := by
  let F : ι → ℂ := fun i => analyticPowerFamilyTerm (f i) (-(p / 4)) (p / 2) z
  let G : κ → ℂ := fun j => analyticPowerFamilyTerm (g j) ((p / (p - 1)) / 4)
    ((p / (p - 1)) / 2) z
  have hFsumNat : ∑ i, w i * ‖F i‖ ^ (2 : ℕ) = 1 := by
    calc
      ∑ i, w i * ‖F i‖ ^ 2 = ∑ i, w i * |f i| ^ p := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [F]
        rw [norm_analyticPowerFamilyTerm_input_zero (f i) p hp z hz]
      _ = 1 := hf
  have hFsum : ∑ i, w i * ‖F i‖ ^ (2 : ℝ) = 1 := by
    calc
      ∑ i, w i * ‖F i‖ ^ (2 : ℝ) = ∑ i, w i * ‖F i‖ ^ (2 : ℕ) := by
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg (fun y : ℝ => w i * y) (Real.rpow_natCast ‖F i‖ 2)
      _ = 1 := hFsumNat
  have hOneNonneg : (0 : ℝ) ≤ 1 := by
    rw [← hFsumNat]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)
  have hGsumNat : ∑ j, v j * ‖G j‖ ^ (2 : ℕ) = 1 := by
    calc
      ∑ j, v j * ‖G j‖ ^ 2 = ∑ j, v j * |g j| ^ (p / (p - 1)) := by
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [G]
        rw [norm_analyticPowerFamilyTerm_dual_zero (g j) p hp z hz]
      _ = 1 := hg
  have hGsum : ∑ j, v j * ‖G j‖ ^ (2 : ℝ) = 1 := by
    calc
      ∑ j, v j * ‖G j‖ ^ (2 : ℝ) = ∑ j, v j * ‖G j‖ ^ (2 : ℕ) := by
        apply Finset.sum_congr rfl
        intro j _
        exact congrArg (fun y : ℝ => v j * y) (Real.rpow_natCast ‖G j‖ 2)
      _ = 1 := hGsumNat
  have hOut : ∑ j, v j * ‖coordinatewiseComplexification T F j‖ ^ 2 ≤ M ^ 2 := by
    have h := weighted_norm_sq_coordinatewiseComplexification_le T w v (M ^ 2) hT F
    rw [hFsumNat, mul_one] at h
    exact h
  have hholder := norm_weighted_sum_mul_le Finset.univ v
    (coordinatewiseComplexification T F) G Real.HolderConjugate.two_two
    (fun j _ => hv j)
  have hMNonneg : 0 ≤ M := zero_le_one.trans hM
  calc
    ‖∑ j, (v j : ℂ) * coordinatewiseComplexification T F j * G j‖ ≤
        (∑ j, v j * ‖coordinatewiseComplexification T F j‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∑ j, v j * ‖G j‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := hholder
    _ ≤ (M ^ 2) ^ (1 / (2 : ℝ)) * 1 := by
      rw [hGsum, Real.one_rpow]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow
          (Finset.sum_nonneg fun j _ =>
            mul_nonneg (hv j) (Real.rpow_nonneg (norm_nonneg _) _))
          (calc
            ∑ j, v j * ‖coordinatewiseComplexification T F j‖ ^ (2 : ℝ) =
                ∑ j, v j * ‖coordinatewiseComplexification T F j‖ ^ (2 : ℕ) := by
              apply Finset.sum_congr rfl
              intro j _
              exact congrArg (fun y : ℝ => v j * y)
                (Real.rpow_natCast ‖coordinatewiseComplexification T F j‖ 2)
            _ ≤ M ^ 2 := hOut) (by norm_num)) hOneNonneg
    _ = M := by
      rw [mul_one]
      exact rpow_inv_nat_sq M hMNonneg 2 (by norm_num)

/-- The normalized analytic pairing obeys the fourth-power boundary estimate. -/
theorem norm_powerFamilyPairing_one_le
    [Fintype ι] [Fintype κ]
    (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ))
    (w : ι → ℝ) (v : κ → ℝ) (hw : ∀ i, 0 ≤ w i) (hv : ∀ j, 0 ≤ v j)
    (p M : ℝ) (hp : 2 ≤ p) (hM : 1 ≤ M)
    (hT : ∀ x : ι → ℝ,
      ∑ j, v j * (T x j) ^ 4 ≤ M ^ 4 * ∑ i, w i * (x i) ^ 4)
    (f : ι → ℝ) (g : κ → ℝ)
    (hf : ∑ i, w i * |f i| ^ p = 1)
    (hg : ∑ j, v j * |g j| ^ (p / (p - 1)) = 1)
    (z : ℂ) (hz : z.re = 1) :
    ‖∑ j, (v j : ℂ) *
      coordinatewiseComplexification T
        (fun i => analyticPowerFamilyTerm (f i) (-(p / 4)) (p / 2) z) j *
      analyticPowerFamilyTerm (g j) ((p / (p - 1)) / 4)
        ((p / (p - 1)) / 2) z‖ ≤ M := by
  let F : ι → ℂ := fun i => analyticPowerFamilyTerm (f i) (-(p / 4)) (p / 2) z
  let G : κ → ℂ := fun j => analyticPowerFamilyTerm (g j) ((p / (p - 1)) / 4)
    ((p / (p - 1)) / 2) z
  have hFsumNat : ∑ i, w i * ‖F i‖ ^ (4 : ℕ) = 1 := by
    calc
      ∑ i, w i * ‖F i‖ ^ 4 = ∑ i, w i * |f i| ^ p := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [F]
        rw [norm_analyticPowerFamilyTerm_input_one (f i) p hp z hz]
      _ = 1 := hf
  have hFsum : ∑ i, w i * ‖F i‖ ^ (4 : ℝ) = 1 := by
    calc
      ∑ i, w i * ‖F i‖ ^ (4 : ℝ) = ∑ i, w i * ‖F i‖ ^ (4 : ℕ) := by
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg (fun y : ℝ => w i * y) (Real.rpow_natCast ‖F i‖ 4)
      _ = 1 := hFsumNat
  have hGsum : ∑ j, v j * ‖G j‖ ^ (4 / 3 : ℝ) = 1 := by
    calc
      ∑ j, v j * ‖G j‖ ^ (4 / 3 : ℝ) =
          ∑ j, v j * |g j| ^ (p / (p - 1)) := by
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [G]
        rw [norm_analyticPowerFamilyTerm_dual_one (g j) p hp z hz]
      _ = 1 := hg
  have hOneNonneg : (0 : ℝ) ≤ 1 := by
    rw [← hFsumNat]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (by positivity)
  have hOut : ∑ j, v j * ‖coordinatewiseComplexification T F j‖ ^ 4 ≤ M ^ 4 := by
    have h := weighted_norm_four_coordinatewiseComplexification_le T w v (M ^ 4) hT F
    rw [hFsumNat, mul_one] at h
    exact h
  have hpq : (4 : ℝ).HolderConjugate (4 / 3 : ℝ) :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hholder := norm_weighted_sum_mul_le Finset.univ v
    (coordinatewiseComplexification T F) G hpq (fun j _ => hv j)
  have hMNonneg : 0 ≤ M := zero_le_one.trans hM
  calc
    ‖∑ j, (v j : ℂ) * coordinatewiseComplexification T F j * G j‖ ≤
        (∑ j, v j * ‖coordinatewiseComplexification T F j‖ ^ (4 : ℝ)) ^ (1 / (4 : ℝ)) *
          (∑ j, v j * ‖G j‖ ^ (4 / 3 : ℝ)) ^ (1 / (4 / 3 : ℝ)) := hholder
    _ ≤ (M ^ 4) ^ (1 / (4 : ℝ)) * 1 := by
      rw [hGsum, Real.one_rpow]
      apply mul_le_mul_of_nonneg_right _ hOneNonneg
      apply Real.rpow_le_rpow
      · exact Finset.sum_nonneg fun j _ =>
          mul_nonneg (hv j) (Real.rpow_nonneg (norm_nonneg _) _)
      · calc
          ∑ j, v j * ‖coordinatewiseComplexification T F j‖ ^ (4 : ℝ) =
              ∑ j, v j * ‖coordinatewiseComplexification T F j‖ ^ (4 : ℕ) := by
            apply Finset.sum_congr rfl
            intro j _
            exact congrArg (fun y : ℝ => v j * y)
              (Real.rpow_natCast ‖coordinatewiseComplexification T F j‖ 4)
          _ ≤ M ^ 4 := hOut
      · norm_num
    _ = M := by
      rw [mul_one]
      exact rpow_inv_nat_sq M hMNonneg 4 (by norm_num)

end PDE
