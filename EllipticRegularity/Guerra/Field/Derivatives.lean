module

public import EllipticRegularity.Guerra.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Guerra sharpness: ambient differentiation of `r` and `t`

For `x ≠ 0`: `∂_i r = x_i / r`, `∂_i t = δ_{ij}/r - x_j x_i / r³`; hence
`∑ x_i ∂_i r = r`, `∑ x_i ∂_i t = 0`, `∂_j t = (1 - t²)/r`.
-/

@[expose] public section

open scoped BigOperators

namespace PDE.Guerra

noncomputable section

variable {d : ℕ}

/-- The linear functional `v ↦ x · v`. -/
def dotCLM (x : Vec d) : Vec d →L[ℝ] ℝ := ∑ i, x i • ContinuousLinearMap.proj i

theorem dotCLM_apply (x v : Vec d) : dotCLM x v = vecDot x v := by
  simp [dotCLM, vecDot]

theorem hasFDerivAt_vecNormSq' (x : Vec d) :
    HasFDerivAt vecNormSq ((2 : ℝ) • dotCLM x) x := by
  have h : HasFDerivAt (fun y : Vec d => ∑ i, y i * y i)
      (∑ i : Fin d, (x i • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ) +
        x i • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ))) x :=
    HasFDerivAt.fun_sum fun i _ =>
      (hasFDerivAt_apply (𝕜 := ℝ) i x).mul (hasFDerivAt_apply (𝕜 := ℝ) i x)
  have e : (∑ i : Fin d, (x i • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ) +
      x i • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ))) = (2 : ℝ) • dotCLM x := by
    ext v
    simp [dotCLM, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e] at h
  exact h

/-- Derivative of the radius. -/
theorem hasFDerivAt_rad {x : Vec d} (hx : x ≠ 0) :
    ∃ L : Vec d →L[ℝ] ℝ, HasFDerivAt (rad : Vec d → ℝ) L x ∧
      ∀ v, L v = vecDot x v / rad x := by
  have hne : vecNormSq x ≠ 0 := vecNormSq_eq_zero_iff.not.mpr hx
  have h := (hasFDerivAt_vecNormSq' x).sqrt hne
  refine ⟨_, h, fun v => ?_⟩
  have hr : rad x = √(vecNormSq x) := rfl
  simp only [smul_apply, dotCLM_apply, smul_eq_mul, hr]
  have : 0 < √(vecNormSq x) := Real.sqrt_pos.mpr (lt_of_le_of_ne (vecNormSq_nonneg x) hne.symm)
  field_simp

/-- Derivative of the latitude. -/
theorem hasFDerivAt_lat (j : Fin d) {x : Vec d} (hx : x ≠ 0) :
    ∃ L : Vec d →L[ℝ] ℝ, HasFDerivAt (lat j : Vec d → ℝ) L x ∧
      ∀ v, L v = v j / rad x - x j * vecDot x v / rad x ^ 3 := by
  obtain ⟨LR, hLR, hLRv⟩ := hasFDerivAt_rad hx
  have hr := (rad_pos hx).ne'
  have hinv := (hasDerivAt_inv hr).comp_hasFDerivAt x hLR
  have hm := (hasFDerivAt_apply (𝕜 := ℝ) j x).mul hinv
  have e : (lat j : Vec d → ℝ) = fun y => y j * (rad y)⁻¹ := by
    funext y; simp [lat, div_eq_mul_inv]
  rw [e]
  refine ⟨_, hm, fun v => ?_⟩
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.proj_apply, Function.comp_apply, hLRv, smul_eq_mul]
  field_simp
  ring

/-- `∂_i r = x_i / r`. -/
theorem classicalGradient_rad {x : Vec d} (hx : x ≠ 0) (i : Fin d) :
    classicalGradient (rad : Vec d → ℝ) x i = x i / rad x := by
  obtain ⟨L, hL, hLv⟩ := hasFDerivAt_rad hx
  rw [classicalGradient_apply, hL.fderiv, hLv, vecDot_basisVec_right]

/-- `∂_i t = δ_{ij}/r - x_j x_i / r³`. -/
theorem classicalGradient_lat (j : Fin d) {x : Vec d} (hx : x ≠ 0) (i : Fin d) :
    classicalGradient (lat j : Vec d → ℝ) x i =
      (if i = j then 1 else 0) / rad x - x j * x i / rad x ^ 3 := by
  obtain ⟨L, hL, hLv⟩ := hasFDerivAt_lat j hx
  rw [classicalGradient_apply, hL.fderiv, hLv, vecDot_basisVec_right]
  by_cases hij : i = j
  · subst hij; simp [basisVec_apply]
  · simp [basisVec_apply, hij, Ne.symm hij]

theorem sum_mul_classicalGradient_rad {x : Vec d} (hx : x ≠ 0) :
    ∑ i, x i * classicalGradient (rad : Vec d → ℝ) x i = rad x := by
  have hr := (rad_pos hx).ne'
  simp only [classicalGradient_rad hx]
  have : ∑ i, x i * (x i / rad x) = vecNormSq x / rad x := by
    rw [vecNormSq_eq_sum_sq, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this, ← rad_sq]
  field_simp

theorem sum_mul_classicalGradient_lat (j : Fin d) {x : Vec d} (hx : x ≠ 0) :
    ∑ i, x i * classicalGradient (lat j : Vec d → ℝ) x i = 0 := by
  have hr := (rad_pos hx).ne'
  simp only [classicalGradient_lat j hx]
  have h1 : ∑ i, x i * ((if i = j then (1:ℝ) else 0) / rad x - x j * x i / rad x ^ 3) =
      x j / rad x - x j * vecNormSq x / rad x ^ 3 := by
    have e1 : ∑ i, x i * ((if i = j then (1:ℝ) else 0) / rad x) = x j / rad x := by
      simp [div_eq_mul_inv, Finset.sum_ite_eq']
    have e2 : ∑ i, x i * (x j * x i / rad x ^ 3) = x j * vecNormSq x / rad x ^ 3 := by
      rw [vecNormSq_eq_sum_sq, Finset.mul_sum, Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp only [mul_sub, Finset.sum_sub_distrib, e1, e2]
  rw [h1, ← rad_sq]
  field_simp
  ring

/-- `∂_j t = (1 - t²)/r`. -/
theorem classicalGradient_lat_self (j : Fin d) {x : Vec d} (hx : x ≠ 0) :
    classicalGradient (lat j : Vec d → ℝ) x j = (1 - lat j x ^ 2) / rad x := by
  have hr := (rad_pos hx).ne'
  rw [classicalGradient_lat j hx]
  simp only [ite_true, lat]
  field_simp

end

end PDE.Guerra
