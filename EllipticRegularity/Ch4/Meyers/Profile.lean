module

public import EllipticRegularity.Ch4.Meyers.Calculus

/-!
# The profiles `s^γ x_k`, their gradients, and the coefficient field
-/

@[expose] public section

namespace PDE.Ch4Meyers

open MeasureTheory Set

variable {d : ℕ} {w : Fin d → ℝ}

/-- The profile `s^γ x_k`. -/
noncomputable def prof (w : Fin d → ℝ) (γ : ℝ) (k : Fin d) (x : Vec d) : ℝ :=
  axisSq w x ^ γ * x k

/-- The gradient of `s^γ x_k` off the singular set (used everywhere as the chosen gradient). -/
noncomputable def profGrad (w : Fin d → ℝ) (γ : ℝ) (k : Fin d) (x : Vec d) : Vec d :=
  fun i => axisSq w x ^ γ * (if k = i then 1 else 0) +
    2 * γ * axisSq w x ^ (γ - 1) * x k * (w i * x i)

/-- The flux `a ∇(s^γ x_k)` off the singular set. -/
noncomputable def profFlux (w : Fin d → ℝ) (Λ γ : ℝ) (k : Fin d) (x : Vec d) : Vec d :=
  fun i => axisSq w x ^ γ * (if k = i then 1 else 0) +
    (Λ - 1 + 2 * γ * Λ) * axisSq w x ^ (γ - 1) * x k * (w i * x i)

/-- The coefficient field `I + (Λ - 1) (Px)(Px)ᵀ / s` (equal to `I` on the singular set). -/
noncomputable def meyersCoeff (w : Fin d → ℝ) (Λ : ℝ) : CoeffField d := fun x i j =>
  (if i = j then 1 else 0) + (Λ - 1) * (w i * x i) * (w j * x j) / axisSq w x

theorem contDiffAt_prof {x : Vec d} (hs : 0 < axisSq w x) (γ : ℝ) (k : Fin d) (n : ℕ∞) :
    ContDiffAt ℝ n (prof w γ k) x := by
  have h1 : ContDiffAt ℝ n (axisSq w) x := (contDiff_axisSq w).contDiffAt.of_le (by
    exact_mod_cast le_top)
  exact (h1.rpow_const_of_ne hs.ne').mul (contDiff_apply ℝ ℝ k).contDiffAt

theorem classicalGradient_prof (hw : ∀ i, w i = 0 ∨ w i = 1) {x : Vec d}
    (hs : 0 < axisSq w x) (γ : ℝ) (k : Fin d) :
    classicalGradient (prof w γ k) x = profGrad w γ k x := by
  funext i
  rw [classicalGradient_apply]
  have := fderiv_rpow_mul_basisVec hw hs γ (hasFDerivAt_coord x k) i
  change fderiv ℝ (fun y => axisSq w y ^ γ * y k) x (basisVec i) = _
  rw [this]
  simp only [profGrad, ContinuousLinearMap.proj_apply, basisVec_apply]
  ring

theorem meyersCoeff_symm (w : Fin d → ℝ) (Λ : ℝ) (x : Vec d) (i j : Fin d) :
    meyersCoeff w Λ x i j = meyersCoeff w Λ x j i := by
  unfold meyersCoeff
  have : (i = j) ↔ (j = i) := eq_comm
  simp only [this]
  ring

theorem meyersCoeff_matVecMul_profGrad (hw : ∀ i, w i = 0 ∨ w i = 1) {x : Vec d}
    (hs : 0 < axisSq w x) (Λ γ : ℝ) {k : Fin d} (hk : w k = 1) :
    matVecMul (meyersCoeff w Λ x) (profGrad w γ k x) = profFlux w Λ γ k x := by
  funext i
  have hsum : ∑ j, (w j * x j) * profGrad w γ k x j =
      (1 + 2 * γ) * axisSq w x ^ γ * x k := by
    have h1 : ∀ j, (w j * x j) * profGrad w γ k x j =
        axisSq w x ^ γ * ((if k = j then 1 else 0) * (w j * x j)) +
        2 * γ * axisSq w x ^ (γ - 1) * x k * (w j * x j) ^ 2 := by
      intro j; unfold profGrad; ring
    simp_rw [h1]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_wx_sq hw]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, hk]
    rw [Real.rpow_sub_one hs.ne']
    field_simp
  have h2 : matVecMul (meyersCoeff w Λ x) (profGrad w γ k x) i =
      profGrad w γ k x i + (Λ - 1) * (w i * x i) / axisSq w x *
        ∑ j, (w j * x j) * profGrad w γ k x j := by
    simp only [matVecMul_apply, meyersCoeff, add_mul, Finset.sum_add_distrib, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h2, hsum]
  simp only [profGrad, profFlux]
  rw [Real.rpow_sub_one hs.ne']
  field_simp
  ring

end PDE.Ch4Meyers
