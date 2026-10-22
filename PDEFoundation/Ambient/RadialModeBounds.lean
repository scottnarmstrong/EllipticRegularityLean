module

public import PDEFoundation.Ambient.PlanarRadialProjection
public import PDEFoundation.Ambient.Basis
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Bounds for coordinate radial modes -/

@[expose] public section

open scoped BigOperators

namespace PDE

noncomputable section

/-- The coordinate radial mode attached to `k`. -/
def radialModeVector {d : ℕ} (k : Fin d) (β : ℝ) (x : Vec d) : Vec d :=
  basisVec k + ((β - 1) * (x k / vecNormSq x)) • x

/-- The homogeneous radial power field attached to a coordinate mode. -/
def radialModePowerField {d : ℕ} (k : Fin d) (β : ℝ) (x : Vec d) : Vec d :=
  Real.rpow (vecEuclideanNorm x) (β - 1) • radialModeVector k β x

@[simp]
theorem radialModeVector_zero {d : ℕ} (k : Fin d) (β : ℝ) :
    radialModeVector k β 0 = basisVec k := by
  simp [radialModeVector]

theorem radialModeVector_eq_projection_action {d : ℕ}
    (k : Fin d) (β : ℝ) (x : Vec d) :
    radialModeVector k β x = basisVec k +
      (β - 1) • matVecMul (radialProjectionMatrix x) (basisVec k) := by
  rw [matVecMul_radialProjectionMatrix, vecDot_basisVec_right]
  ext i
  simp [radialModeVector]
  ring

private theorem vecNormSq_radialModeVector_of_ne_zero {d : ℕ}
    (k : Fin d) (β : ℝ) {x : Vec d} (hx : x ≠ 0) :
    vecNormSq (radialModeVector k β x) =
      1 + (β ^ 2 - 1) * (x k) ^ 2 / vecNormSq x := by
  have hR : vecNormSq x ≠ 0 := by
    exact fun h => hx (vecNormSq_eq_zero h)
  rw [radialModeVector, vecNormSq_add_expand, vecNormSq_basisVec,
    vecNormSq_smul, vecDot_basisVec_left]
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

private theorem radialMode_coordinate_ratio_bounds {d : ℕ}
    (k : Fin d) {x : Vec d} (hx : x ≠ 0) :
    0 ≤ (x k) ^ 2 / vecNormSq x ∧ (x k) ^ 2 / vecNormSq x ≤ 1 := by
  have hR : 0 < vecNormSq x :=
    lt_of_le_of_ne (vecNormSq_nonneg x)
      (Ne.symm (fun h => hx (vecNormSq_eq_zero h)))
  constructor
  · exact div_nonneg (sq_nonneg _) hR.le
  · exact (div_le_one hR).mpr (sq_apply_le_vecNormSq x k)

theorem radialModeVector_norm_bounds {d : ℕ}
    (k : Fin d) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (x : Vec d) :
    β ≤ vecEuclideanNorm (radialModeVector k β x) ∧
      vecEuclideanNorm (radialModeVector k β x) ≤ 1 := by
  by_cases hx : x = 0
  · subst x
    simp [radialModeVector_zero, vecEuclideanNorm_basisVec, hβ1]
  · obtain ⟨ht0, ht1⟩ := radialMode_coordinate_ratio_bounds k hx
    have hsq := vecNormSq_radialModeVector_of_ne_zero k β hx
    have hβsq_le : β ^ 2 ≤ 1 := by nlinarith
    have hβsq : β ^ 2 ≤ vecNormSq (radialModeVector k β x) := by
      rw [hsq]
      have hm : 0 ≤ (1 - β ^ 2) * (1 - (x k) ^ 2 / vecNormSq x) :=
        mul_nonneg (sub_nonneg.mpr hβsq_le) (sub_nonneg.mpr ht1)
      calc
        β ^ 2 ≤ β ^ 2 + (1 - β ^ 2) *
            (1 - (x k) ^ 2 / vecNormSq x) := le_add_of_nonneg_right hm
        _ = 1 + (β ^ 2 - 1) * (x k) ^ 2 / vecNormSq x := by ring
    have hsq1 : vecNormSq (radialModeVector k β x) ≤ 1 := by
      rw [hsq]
      have hm : 0 ≤ (1 - β ^ 2) * ((x k) ^ 2 / vecNormSq x) :=
        mul_nonneg (sub_nonneg.mpr hβsq_le) ht0
      calc
        1 + (β ^ 2 - 1) * (x k) ^ 2 / vecNormSq x =
            1 - (1 - β ^ 2) * ((x k) ^ 2 / vecNormSq x) := by ring
        _ ≤ 1 := sub_le_self 1 hm
    constructor
    · have hn := vecEuclideanNorm_nonneg (radialModeVector k β x)
      have he := vecEuclideanNorm_sq (radialModeVector k β x)
      nlinarith
    · have hn := vecEuclideanNorm_nonneg (radialModeVector k β x)
      have he := vecEuclideanNorm_sq (radialModeVector k β x)
      nlinarith

theorem radialModePowerField_norm_bounds {d : ℕ}
    (k : Fin d) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (x : Vec d) :
    β * Real.rpow (vecEuclideanNorm x) (β - 1) ≤
        vecEuclideanNorm (radialModePowerField k β x) ∧
      vecEuclideanNorm (radialModePowerField k β x) ≤
        Real.rpow (vecEuclideanNorm x) (β - 1) := by
  obtain ⟨hlow, hupp⟩ := radialModeVector_norm_bounds k hβ0 hβ1 x
  rw [radialModePowerField, vecEuclideanNorm_smul]
  have hc : 0 ≤ Real.rpow (vecEuclideanNorm x) (β - 1) :=
    Real.rpow_nonneg (vecEuclideanNorm_nonneg x) (β - 1)
  rw [abs_of_nonneg hc]
  constructor
  · calc
      β * Real.rpow (vecEuclideanNorm x) (β - 1) =
          Real.rpow (vecEuclideanNorm x) (β - 1) * β := by ring
      _ ≤ Real.rpow (vecEuclideanNorm x) (β - 1) *
          vecEuclideanNorm (radialModeVector k β x) :=
        mul_le_mul_of_nonneg_left hlow hc
  · calc
      Real.rpow (vecEuclideanNorm x) (β - 1) *
          vecEuclideanNorm (radialModeVector k β x) ≤
          Real.rpow (vecEuclideanNorm x) (β - 1) * 1 :=
        mul_le_mul_of_nonneg_left hupp hc
      _ = Real.rpow (vecEuclideanNorm x) (β - 1) := mul_one _

end

end PDE
