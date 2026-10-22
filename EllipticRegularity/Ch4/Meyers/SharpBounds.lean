module

public import EllipticRegularity.Ch4.Meyers.SharpEq

/-!
# Bounds and linearity for the Dirichlet part of the planar-type example
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4Meyers

open MeasureTheory Set

variable {d : ℕ} {w : Fin d → ℝ} {i0 i1 : Fin d}

theorem matVecMul_comb (A : Mat d) (s t : ℝ) (F H : Vec d) (i : Fin d) :
    matVecMul A (s • F + t • H) i = s * matVecMul A F i + t * matVecMul A H i := by
  simp only [matVecMul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun j _ => by ring

theorem vecDot_comb (s t : ℝ) (F H η : Vec d) :
    vecDot (s • F + t • H) η = s * vecDot F η + t * vecDot H η := by
  simp only [vecDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun j _ => by ring

theorem abs_meyersCoeff_le (hw : ∀ i, w i = 0 ∨ w i = 1) {Λ : ℝ} (hΛ : 1 ≤ Λ) (x : Vec d)
    (i j : Fin d) : |meyersCoeff w Λ x i j| ≤ Λ := by
  rcases (axisSq_nonneg hw x).eq_or_lt with hs | hs
  · rw [meyersCoeff_of_axisSq_eq_zero w Λ hs.symm]
    by_cases h : i = j
    · subst h; simp; linarith
    · simp [h]; linarith
  · unfold meyersCoeff
    have hq : |(w i * x i) * (w j * x j)| ≤ axisSq w x := by
      rw [abs_mul]
      calc |w i * x i| * |w j * x j| ≤ Real.sqrt (axisSq w x) * Real.sqrt (axisSq w x) :=
            mul_le_mul (abs_wx_le_sqrt hw x i) (abs_wx_le_sqrt hw x j) (abs_nonneg _)
              (Real.sqrt_nonneg _)
        _ = axisSq w x := Real.mul_self_sqrt hs.le
    have h2 : |(Λ - 1) * (w i * x i) * (w j * x j) / axisSq w x| ≤ Λ - 1 := by
      rw [abs_div, abs_of_pos hs, div_le_iff₀ hs, mul_assoc, abs_mul,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ Λ - 1)]
      exact mul_le_mul_of_nonneg_left hq (by linarith)
    calc |(if i = j then (1 : ℝ) else 0) + (Λ - 1) * (w i * x i) * (w j * x j) / axisSq w x|
        ≤ |(if i = j then (1 : ℝ) else 0)| +
          |(Λ - 1) * (w i * x i) * (w j * x j) / axisSq w x| := abs_add_le _ _
      _ ≤ 1 + (Λ - 1) := by
          gcongr
          split_ifs <;> simp
      _ = Λ := by ring

theorem abs_matVecMul_le (hw : ∀ i, w i = 0 ∨ w i = 1) {Λ : ℝ} (hΛ : 1 ≤ Λ) (x : Vec d)
    {ξ : Vec d} {K : ℝ} (hξ : ∀ j, |ξ j| ≤ K) (_hK : 0 ≤ K) (i : Fin d) :
    |matVecMul (meyersCoeff w Λ x) ξ i| ≤ d * (Λ * K) := by
  rw [matVecMul_apply]
  calc |∑ j, meyersCoeff w Λ x i j * ξ j| ≤ ∑ j, |meyersCoeff w Λ x i j * ξ j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin d, Λ * K := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul (abs_meyersCoeff_le hw hΛ x i j) (hξ j) (abs_nonneg _)
          (by linarith)
    _ = d * (Λ * K) := by simp

theorem abs_rot_apply_le {ξ : Vec d} {K : ℝ} (hξ : ∀ j, |ξ j| ≤ K) (hK : 0 ≤ K) (i : Fin d) :
    |rot i0 i1 ξ i| ≤ K := by
  unfold rot
  split_ifs
  · exact hξ _
  · rw [abs_neg]; exact hξ _
  · simpa using hK

theorem measurable_rot_apply {G : Vec d → Vec d} (hG : ∀ j, Measurable fun x => G x j)
    (i : Fin d) : Measurable fun x => rot i0 i1 (G x) i := by
  unfold rot
  split_ifs
  · exact hG _
  · exact (hG _).neg
  · exact measurable_const

theorem measurable_matVecMul_meyersCoeff_apply (w : Fin d → ℝ) (Λ : ℝ) {G : Vec d → Vec d}
    (hG : ∀ j, Measurable fun x => G x j) (i : Fin d) :
    Measurable fun x => matVecMul (meyersCoeff w Λ x) (G x) i := by
  simp only [matVecMul_apply]
  exact Finset.measurable_sum _ fun j _ => (measurable_meyersCoeff_apply w Λ i j).mul (hG j)

end PDE.Ch4Meyers
