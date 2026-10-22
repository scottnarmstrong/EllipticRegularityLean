module

public import PDEFoundation.Analysis.NativeRadialDerivatives
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Derivatives of quadratic radial modes
-/

@[expose] public section

open scoped BigOperators

namespace PDE

private theorem hasFDerivAt_vecNormSq_quadratic {d : ℕ} (x : Vec d) :
    ∃ L : Vec d →L[ℝ] ℝ, HasFDerivAt vecNormSq L x := by
  let e : Fin d → Vec d →L[ℝ] ℝ := fun i =>
    ContinuousLinearMap.proj i
  refine ⟨∑ i : Fin d, (x i • e i + x i • e i), ?_⟩
  unfold vecNormSq vecDot
  exact HasFDerivAt.fun_sum fun i _hi =>
    (hasFDerivAt_apply (𝕜 := ℝ) i x).mul
      (hasFDerivAt_apply (𝕜 := ℝ) i x)

private theorem fderiv_vecNormSq_apply_basisVec_quadratic {d : ℕ}
    (x : Vec d) (i : Fin d) :
    (fderiv ℝ vecNormSq x) (basisVec i) = 2 * x i := by
  obtain ⟨L, hL⟩ := hasFDerivAt_vecNormSq_quadratic x
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

/-- Coordinate derivative of an arbitrary real power of the squared radius,
away from the origin. -/
theorem classicalGradient_vecNormSq_rpow
    {d : ℕ} (s : ℝ) (x : Vec d) (hx : x ≠ 0) :
    classicalGradient (fun y : Vec d => (vecNormSq y) ^ s) x =
      fun i => s * (vecNormSq x) ^ (s - 1) * (2 * x i) := by
  have hR : vecNormSq x ≠ 0 :=
    fun h => hx (vecNormSq_eq_zero h)
  obtain ⟨L, hq⟩ := hasFDerivAt_vecNormSq_quadratic x
  have hp := hq.rpow_const (p := s) (Or.inl hR)
  rw [← hq.fderiv] at hp
  funext i
  rw [classicalGradient_apply, hp.fderiv]
  simp only [smul_apply, smul_eq_mul,
    fderiv_vecNormSq_apply_basisVec_quadratic]

/-- Coordinate derivative of `y_k y_j |y|^(2s)`, away from the origin. -/
theorem classicalGradient_coordinate_mul_coordinate_mul_vecNormSq_rpow
    {d : ℕ} (k j : Fin d) (s : ℝ) (x : Vec d) (hx : x ≠ 0) :
    classicalGradient
        (fun y : Vec d => y k * y j * (vecNormSq y) ^ s) x =
      fun i =>
        ((if i = k then x j else 0) + (if i = j then x k else 0)) *
            (vecNormSq x) ^ s +
          x k * x j *
            (s * (vecNormSq x) ^ (s - 1) * (2 * x i)) := by
  have hR : vecNormSq x ≠ 0 :=
    fun h => hx (vecNormSq_eq_zero h)
  obtain ⟨L, hq⟩ := hasFDerivAt_vecNormSq_quadratic x
  have hp := hq.rpow_const (p := s) (Or.inl hR)
  rw [← hq.fderiv] at hp
  have hk := hasFDerivAt_apply (𝕜 := ℝ) k x
  have hj := hasFDerivAt_apply (𝕜 := ℝ) j x
  have hprod := (hk.mul hj).mul hp
  funext i
  rw [classicalGradient_apply]
  have hf : fderiv ℝ
      (fun y : Vec d => y k * y j * (vecNormSq y) ^ s) x =
      (x k * x j) •
          ((s * (vecNormSq x) ^ (s - 1)) • fderiv ℝ vecNormSq x) +
        (vecNormSq x) ^ s •
          (x k • ContinuousLinearMap.proj j +
            x j • ContinuousLinearMap.proj k) := by
    simpa only [Pi.mul_apply] using! hprod.fderiv
  rw [hf]
  simp only [add_apply, smul_apply,
    smul_eq_mul, ContinuousLinearMap.proj_apply,
    fderiv_vecNormSq_apply_basisVec_quadratic, basisVec_apply]
  simp only [eq_comm]
  by_cases hki : k = i <;> by_cases hji : j = i <;>
    simp [hki, hji] <;> ring

end PDE
