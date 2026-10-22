module

public import PDEFoundation.Sobolev.ClassicalGradient
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Derivatives of native radial powers
-/

@[expose] public section

open scoped BigOperators

namespace PDE

private theorem hasFDerivAt_vecNormSq {d : ℕ} (x : Vec d) :
    ∃ L : Vec d →L[ℝ] ℝ, HasFDerivAt vecNormSq L x := by
  let e : Fin d → Vec d →L[ℝ] ℝ := fun i =>
    ContinuousLinearMap.proj i
  refine ⟨∑ i : Fin d, (x i • e i + x i • e i), ?_⟩
  unfold vecNormSq vecDot
  exact HasFDerivAt.fun_sum fun i _hi =>
    (hasFDerivAt_apply (𝕜 := ℝ) i x).mul
      (hasFDerivAt_apply (𝕜 := ℝ) i x)

private theorem fderiv_vecNormSq_apply_basisVec {d : ℕ}
    (x : Vec d) (i : Fin d) :
    (fderiv ℝ vecNormSq x) (basisVec i) = 2 * x i := by
  obtain ⟨L, hL⟩ := hasFDerivAt_vecNormSq x
  rw [hL.fderiv]
  let e : Fin d → Vec d →L[ℝ] ℝ := fun j =>
    ContinuousLinearMap.proj j
  have hLeq : L = ∑ j : Fin d, (x j • e j + x j • e j) := by
    simpa only [e] using hL.unique (by
      unfold vecNormSq vecDot
      exact HasFDerivAt.fun_sum fun j _hj =>
        (hasFDerivAt_apply (𝕜 := ℝ) j x).mul
          (hasFDerivAt_apply (𝕜 := ℝ) j x))
  rw [hLeq]
  simp [e, basisVec_apply]
  rw [Finset.sum_eq_single i]
  · simp only [ite_true]
    ring
  · intro j _hj hji
    simp [hji]
  · simp

/-- Coordinate derivative of a coordinate times an arbitrary real radial
power, away from the origin. -/
theorem classicalGradient_coordinate_mul_vecNormSq_rpow
    {d : ℕ} (k : Fin d) (x : Vec d) (hx : x ≠ 0) (s : ℝ) :
    classicalGradient (fun y : Vec d => y k * (vecNormSq y) ^ s) x =
      fun i =>
        (if i = k then (vecNormSq x) ^ s else 0) +
          x k * (s * (vecNormSq x) ^ (s - 1) * (2 * x i)) := by
  have hnormNe : vecNormSq x ≠ 0 := by
    exact vecNormSq_eq_zero_iff.not.mpr hx
  have hcoord := hasFDerivAt_apply (𝕜 := ℝ) k x
  obtain ⟨L, hnorm⟩ := hasFDerivAt_vecNormSq x
  have hpower := hnorm.rpow_const
    (p := s) (Or.inl hnormNe)
  rw [← hnorm.fderiv] at hpower
  have hproduct := hcoord.mul hpower
  funext i
  rw [classicalGradient_apply]
  have hf : fderiv ℝ (fun y : Vec d => y k * (vecNormSq y) ^ s) x =
      x k • (s * (vecNormSq x) ^ (s - 1)) • fderiv ℝ vecNormSq x +
        (vecNormSq x) ^ s • ContinuousLinearMap.proj k := by
    simpa only [Pi.mul_apply] using! hproduct.fderiv
  rw [hf]
  simp only [add_apply, smul_apply,
    smul_eq_mul, fderiv_vecNormSq_apply_basisVec,
    ContinuousLinearMap.proj_apply]
  by_cases hik : i = k
  · subst i
    simp [basisVec_apply]
    ring
  · simp [basisVec_apply, hik, Ne.symm hik]

/-- Coordinate derivative of `y_k log |y|`, written using
`log |y| = (1 / 2) log |y|²`, away from the origin. -/
theorem classicalGradient_coordinate_mul_half_log_vecNormSq
    {d : ℕ} (k : Fin d) (x : Vec d) (hx : x ≠ 0) :
    classicalGradient
        (fun y : Vec d => y k * ((1 / 2 : ℝ) * Real.log (vecNormSq y))) x =
      fun i =>
        (if i = k then (1 / 2 : ℝ) * Real.log (vecNormSq x) else 0) +
          x k * x i / vecNormSq x := by
  have hnormNe : vecNormSq x ≠ 0 := by
    exact vecNormSq_eq_zero_iff.not.mpr hx
  have hcoord := hasFDerivAt_apply (𝕜 := ℝ) k x
  obtain ⟨L, hnorm⟩ := hasFDerivAt_vecNormSq x
  have hlog := hnorm.log hnormNe
  rw [← hnorm.fderiv] at hlog
  have hhalf := hlog.const_mul (1 / 2 : ℝ)
  have hproduct := hcoord.mul hhalf
  funext i
  rw [classicalGradient_apply]
  have hf : fderiv ℝ
      (fun y : Vec d => y k * ((1 / 2 : ℝ) * Real.log (vecNormSq y))) x =
      x k • ((1 / 2 : ℝ) • (vecNormSq x)⁻¹ • fderiv ℝ vecNormSq x) +
        ((1 / 2 : ℝ) * Real.log (vecNormSq x)) •
          ContinuousLinearMap.proj k := by
    simpa only [Pi.mul_apply] using! hproduct.fderiv
  rw [hf]
  simp only [add_apply, smul_apply,
    smul_eq_mul, fderiv_vecNormSq_apply_basisVec,
    ContinuousLinearMap.proj_apply]
  by_cases hik : i = k
  · subst i
    simp [basisVec_apply]
    field_simp
    ring
  · simp [basisVec_apply, hik, Ne.symm hik]
    field_simp

end PDE
