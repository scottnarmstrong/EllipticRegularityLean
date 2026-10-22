module

public import PDEFoundation.Analysis.NativeRadialDerivatives
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Divergence of a radial forcing field
-/

@[expose] public section

open scoped BigOperators

namespace PDE

/-- The bounded radial forcing used by the logarithmic sharpness mode. -/
noncomputable def radialForcing {d : ℕ} (k : Fin d) (x : Vec d) : Vec d :=
  (-2 * (x k / vecNormSq x)) • x

@[simp]
theorem radialForcing_zero {d : ℕ} (k : Fin d) :
    radialForcing k 0 = 0 := by
  simp [radialForcing]

private theorem differentiableAt_vecNormSq {d : ℕ} (x : Vec d) :
    DifferentiableAt ℝ vecNormSq x := by
  unfold vecNormSq vecDot
  fun_prop

private theorem differentiableAt_coordinate_div_vecNormSq
    {d : ℕ} (k : Fin d) (x : Vec d) (hx : x ≠ 0) :
    DifferentiableAt ℝ (fun y : Vec d => y k / vecNormSq y) x := by
  have hR : vecNormSq x ≠ 0 :=
    fun h => hx (vecNormSq_eq_zero h)
  exact (hasFDerivAt_apply (𝕜 := ℝ) k x).differentiableAt.mul
    ((differentiableAt_vecNormSq x).inv hR)

private theorem classicalGradient_radialForcing_component
    {d : ℕ} (k i : Fin d) (x : Vec d) (hx : x ≠ 0) :
    classicalGradient (fun y : Vec d => radialForcing k y i) x i =
      -2 * (x k / vecNormSq x +
        x i * ((if i = k then (vecNormSq x)⁻¹ else 0) -
          2 * x k * x i / (vecNormSq x) ^ 2)) := by
  have hR : vecNormSq x ≠ 0 :=
    fun h => hx (vecNormSq_eq_zero h)
  have hbase := classicalGradient_coordinate_mul_vecNormSq_rpow
    k x hx (-1)
  have hbaseFun :
      (fun y : Vec d => y k * (vecNormSq y) ^ (-1 : ℝ)) =
        fun y => y k / vecNormSq y := by
    funext y
    rw [Real.rpow_neg_one, div_eq_mul_inv]
  rw [hbaseFun] at hbase
  have hbase_i := congrFun hbase i
  have hbaseDiff := differentiableAt_coordinate_div_vecNormSq k x hx
  have hcoordDiff : DifferentiableAt ℝ (fun y : Vec d => y i) x :=
    (hasFDerivAt_apply (𝕜 := ℝ) i x).differentiableAt
  rw [classicalGradient_apply]
  simp only [radialForcing, Pi.smul_apply, smul_eq_mul]
  have hfun :
      (fun y : Vec d => -2 * (y k / vecNormSq y) * y i) =
        fun y => -2 * ((y k / vecNormSq y) * y i) := by
    funext y
    ring
  rw [hfun]
  change (fderiv ℝ
    (fun y : Vec d => -2 * ((y k / vecNormSq y) * y i)) x)
      (basisVec i) = _
  have hconst : fderiv ℝ
      (fun y : Vec d => -2 * ((y k / vecNormSq y) * y i)) x =
      (-2 : ℝ) • fderiv ℝ
        (fun y : Vec d => (y k / vecNormSq y) * y i) x := by
    simpa only [Pi.mul_apply] using!
      fderiv_const_mul (hbaseDiff.mul hcoordDiff) (-2 : ℝ)
  rw [hconst]
  have hmul : fderiv ℝ (fun y : Vec d => (y k / vecNormSq y) * y i) x =
      (x k / vecNormSq x) • fderiv ℝ (fun y : Vec d => y i) x +
        x i • fderiv ℝ (fun y : Vec d => y k / vecNormSq y) x := by
    simpa only [Pi.mul_apply] using! fderiv_mul hbaseDiff hcoordDiff
  rw [hmul]
  simp only [smul_apply, add_apply,
    smul_eq_mul]
  have hcoordApply :
      (fderiv ℝ (fun y : Vec d => y i) x) (basisVec i) = 1 := by
    rw [(hasFDerivAt_apply (𝕜 := ℝ) i x).fderiv]
    simp [basisVec_apply]
  have hgrad :
      (fderiv ℝ (fun y : Vec d => y k / vecNormSq y) x) (basisVec i) =
        (if i = k then (vecNormSq x)⁻¹ else 0) -
          2 * x k * x i / (vecNormSq x) ^ 2 := by
    rw [← classicalGradient_apply]
    have hRnonneg : 0 ≤ vecNormSq x := vecNormSq_nonneg x
    rw [show (-1 : ℝ) - 1 = -(2 : ℝ) by norm_num,
      Real.rpow_neg hRnonneg 2, Real.rpow_two] at hbase_i
    rw [Real.rpow_neg_one] at hbase_i
    convert hbase_i using 1
    field_simp [hR]
    ring
  rw [hgrad]
  rw [hcoordApply]
  ring

/-- The coordinate divergence of the literal radial forcing, away from the
origin. In dimension two this is `-2 * x_k / |x|²`. -/
theorem sum_classicalGradient_radialForcing_component
    {d : ℕ} (k : Fin d) (x : Vec d) (hx : x ≠ 0) :
    (∑ i : Fin d,
      classicalGradient (fun y : Vec d => radialForcing k y i) x i) =
      -2 * ((d : ℝ) - 1) * x k / vecNormSq x := by
  simp_rw [classicalGradient_radialForcing_component k _ x hx]
  have hR : vecNormSq x ≠ 0 :=
    fun h => hx (vecNormSq_eq_zero h)
  rw [show (∑ i : Fin d, -2 *
      (x k / vecNormSq x +
        x i * ((if i = k then (vecNormSq x)⁻¹ else 0) -
          2 * x k * x i / vecNormSq x ^ 2))) =
      -2 * ∑ i : Fin d,
        (x k / vecNormSq x +
          x i * ((if i = k then (vecNormSq x)⁻¹ else 0) -
            2 * x k * x i / vecNormSq x ^ 2)) by
      rw [Finset.mul_sum]]
  simp only [Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hfirst :
      (∑ i : Fin d, x i * (if i = k then (vecNormSq x)⁻¹ else 0)) =
        x k / vecNormSq x := by
    rw [Finset.sum_eq_single k]
    · simp [div_eq_mul_inv]
    · intro i _hi hik
      simp [hik]
    · simp
  rw [hfirst]
  have hsquares : ∑ i : Fin d, x i * (2 * x k * x i / vecNormSq x ^ 2) =
      2 * x k / vecNormSq x := by
    rw [show (∑ i : Fin d, x i * (2 * x k * x i / vecNormSq x ^ 2)) =
        (2 * x k / vecNormSq x ^ 2) * ∑ i : Fin d, x i * x i by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring]
    rw [show (∑ i : Fin d, x i * x i) = vecNormSq x by rfl]
    field_simp
  rw [hsquares]
  field_simp
  ring

/-- The literal radial forcing has global Euclidean magnitude at most two. -/
theorem vecEuclideanNorm_radialForcing_le_two
    {d : ℕ} (k : Fin d) (x : Vec d) :
    vecEuclideanNorm (radialForcing k x) ≤ 2 := by
  by_cases hx : x = 0
  · subst x
    rw [radialForcing_zero]
    show vecEuclideanNorm (0 : Vec d) ≤ (2 : ℝ)
    simp [vecEuclideanNorm, vecNormSq, vecDot]
  · have hR : 0 < vecNormSq x :=
      lt_of_le_of_ne (vecNormSq_nonneg x)
        (Ne.symm (fun h => hx (vecNormSq_eq_zero h)))
    have hn : 0 < vecEuclideanNorm x := vecEuclideanNorm_pos_iff.mpr hx
    have hk : |x k| ≤ vecEuclideanNorm x :=
      abs_apply_le_vecEuclideanNorm x k
    rw [radialForcing, vecEuclideanNorm_smul, abs_mul]
    norm_num only [abs_neg, abs_of_nonneg]
    rw [abs_div,
      abs_of_nonneg hR.le, ← vecEuclideanNorm_sq]
    calc
      2 * (|x k| / vecEuclideanNorm x ^ 2) * vecEuclideanNorm x =
          2 * |x k| / vecEuclideanNorm x := by field_simp
      _ ≤ 2 * vecEuclideanNorm x / vecEuclideanNorm x :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hk (by norm_num)) hn.le
      _ = 2 := by field_simp

end PDE
