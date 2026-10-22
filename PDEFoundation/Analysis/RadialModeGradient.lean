module

public import PDEFoundation.Analysis.NativeRadialDerivatives
public import PDEFoundation.Ambient.RadialModeBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Gradients of coordinate radial modes
-/

@[expose] public section

namespace PDE

private theorem vecEuclideanNorm_rpow_eq_vecNormSq_rpow_half
    {d : ℕ} (x : Vec d) (a : ℝ) :
    Real.rpow (vecEuclideanNorm x) a =
      Real.rpow (vecNormSq x) (a / 2) := by
  have hn : 0 ≤ vecEuclideanNorm x := vecEuclideanNorm_nonneg x
  rw [← vecEuclideanNorm_sq]
  change (vecEuclideanNorm x) ^ a =
    ((vecEuclideanNorm x) ^ 2) ^ (a / 2)
  rw [← Real.rpow_natCast_mul hn 2 (a / 2)]
  congr 1
  ring

private theorem log_vecEuclideanNorm_eq_half_log_vecNormSq
    {d : ℕ} (x : Vec d) :
    Real.log (vecEuclideanNorm x) =
      (1 / 2 : ℝ) * Real.log (vecNormSq x) := by
  rw [← vecEuclideanNorm_sq, Real.log_pow]
  ring

/-- Away from the origin, the gradient of a coordinate homogeneous radial
mode is the literal native radial power field. -/
theorem classicalGradient_coordinate_mul_vecEuclideanNorm_rpow
    {d : ℕ} (k : Fin d) (β : ℝ) (x : Vec d) (hx : x ≠ 0) :
    classicalGradient
        (fun y : Vec d => y k * Real.rpow (vecEuclideanNorm y) (β - 1)) x =
      radialModePowerField k β x := by
  let s : ℝ := (β - 1) / 2
  have hfun :
      (fun y : Vec d => y k * Real.rpow (vecEuclideanNorm y) (β - 1)) =
        fun y => y k * Real.rpow (vecNormSq y) s := by
    funext y
    rw [vecEuclideanNorm_rpow_eq_vecNormSq_rpow_half]
  rw [hfun]
  change classicalGradient (fun y : Vec d => y k * (vecNormSq y) ^ s) x = _
  rw [classicalGradient_coordinate_mul_vecNormSq_rpow k x hx s]
  have hR : 0 < vecNormSq x :=
    lt_of_le_of_ne (vecNormSq_nonneg x)
      (Ne.symm (fun h => hx (vecNormSq_eq_zero h)))
  have hs : 2 * s = β - 1 := by
    dsimp only [s]
    ring
  have hpow : (vecNormSq x) ^ s =
      Real.rpow (vecEuclideanNorm x) (β - 1) := by
    change Real.rpow (vecNormSq x) s = _
    rw [← vecEuclideanNorm_rpow_eq_vecNormSq_rpow_half]
  have hderiv :
      s * (vecNormSq x) ^ (s - 1) * 2 =
        (β - 1) * (vecNormSq x) ^ s / vecNormSq x := by
    rw [Real.rpow_sub_one hR.ne' s]
    rw [← hs]
    field_simp
  ext i
  simp only [radialModePowerField, radialModeVector, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, basisVec_apply]
  have hderiv_i :
      s * (vecNormSq x) ^ (s - 1) * (2 * x i) =
        ((β - 1) * Real.rpow (vecEuclideanNorm x) (β - 1) /
          vecNormSq x) * x i := by
    calc
      s * (vecNormSq x) ^ (s - 1) * (2 * x i) =
          (s * (vecNormSq x) ^ (s - 1) * 2) * x i := by ring
      _ = ((β - 1) * (vecNormSq x) ^ s / vecNormSq x) * x i := by
        rw [hderiv]
      _ = ((β - 1) * Real.rpow (vecEuclideanNorm x) (β - 1) /
          vecNormSq x) * x i := by rw [hpow]
  rw [hpow]
  by_cases hik : i = k
  · subst i
    simp only [ite_true]
    rw [hderiv_i]
    ring
  · simp only [hik, ite_false]
    rw [hderiv_i]
    ring

/-- Away from the origin, the logarithmic coordinate mode has the expected
radial gradient. -/
theorem classicalGradient_coordinate_mul_log_vecEuclideanNorm
    {d : ℕ} (k : Fin d) (x : Vec d) (hx : x ≠ 0) :
    classicalGradient
        (fun y : Vec d => y k * Real.log (vecEuclideanNorm y)) x =
      fun i => basisVec k i * Real.log (vecEuclideanNorm x) +
        x k * x i / vecNormSq x := by
  have hfun :
      (fun y : Vec d => y k * Real.log (vecEuclideanNorm y)) =
        fun y => y k * ((1 / 2 : ℝ) * Real.log (vecNormSq y)) := by
    funext y
    rw [log_vecEuclideanNorm_eq_half_log_vecNormSq]
  rw [hfun,
    classicalGradient_coordinate_mul_half_log_vecNormSq k x hx]
  funext i
  rw [← log_vecEuclideanNorm_eq_half_log_vecNormSq x]
  by_cases hik : i = k
  · subst i
    simp [basisVec_apply]
  · simp [basisVec_apply, hik]

end PDE
