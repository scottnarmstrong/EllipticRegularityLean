module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic


/-!
# Weighted Cauchy--Schwarz step for Nash--Aronson

This module proves the purely measure-theoretic middle-time estimate. The
evolution and its adjoint enter only through the two weighted `L²` bounds.
-/

@[expose] public section

namespace PDE.Parabolic.Cauchy.Weights

open MeasureTheory

/-- If two nonnegative distances have sum at least `r`, their squared sum is
at least `r²/2`. -/
theorem half_square_sum_of_sum_le {ρ₁ ρ₂ r : ℝ}
    (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) (hr : 0 ≤ r)
    (hsep : r ≤ ρ₁ + ρ₂) : r ^ 2 / 2 ≤ ρ₁ ^ 2 + ρ₂ ^ 2 := by
  have hsum : r ^ 2 ≤ (ρ₁ + ρ₂) ^ 2 := by nlinarith
  nlinarith [sq_nonneg (ρ₁ - ρ₂)]

set_option linter.style.haveILetI false in

/-- Weighted `L²` estimates for forward and backward solutions imply a
bilinear off-diagonal estimate. The distance functions need only be
nonnegative and have pointwise sum at least `r`; their Euclidean geometric
construction is supplied by the caller. -/
theorem weighted_bilinear_offDiagonal {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {A h r : ℝ}
    (hA : 0 < A) (hh : 0 < h) (hr : 0 ≤ r)
    (f g ρ₁ ρ₂ : α → ℝ)
    (hρ₁ : ∀ x, 0 ≤ ρ₁ x) (hρ₂ : ∀ x, 0 ≤ ρ₂ x)
    (hsep : ∀ x, r ≤ ρ₁ x + ρ₂ x)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hF : MemLp (fun x => Real.exp (ρ₁ x ^ 2 / (4 * A * h)) * f x) 2 μ)
    (hG : MemLp (fun x => Real.exp (ρ₂ x ^ 2 / (4 * A * h)) * g x) 2 μ) :
    |∫ x, f x * g x ∂μ| ≤
      Real.exp (-r ^ 2 / (8 * A * h)) *
        (∫ x, |Real.exp (ρ₁ x ^ 2 / (4 * A * h)) * f x| ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
        (∫ x, |Real.exp (ρ₂ x ^ 2 / (4 * A * h)) * g x| ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
  let F : α → ℝ := fun x => Real.exp (ρ₁ x ^ 2 / (4 * A * h)) * f x
  let G : α → ℝ := fun x => Real.exp (ρ₂ x ^ 2 / (4 * A * h)) * g x
  let S : α → ℝ := fun x => ρ₁ x ^ 2 / (4 * A * h) + ρ₂ x ^ 2 / (4 * A * h)
  have hHolderTriple : Real.HolderTriple 2 2 1 := by
    constructor <;> norm_num
  letI : Real.HolderTriple 2 2 1 := hHolderTriple
  have hfgMem : MemLp (fun x => f x * g x) 1 μ := by
    change MemLp (f * g) 1 μ
    exact hf.mul hg
  have hfgInt : Integrable (fun x => f x * g x) μ :=
    memLp_one_iff_integrable.mp hfgMem
  have hFG : MemLp (fun x => F x * G x) 1 μ := by
    change MemLp (F * G) 1 μ
    exact hF.mul hG
  have hFGInt : Integrable (fun x => F x * G x) μ :=
    memLp_one_iff_integrable.mp hFG
  have hF' : MemLp F (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa [F] using hF
  have hG' : MemLp G (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa [G] using hG
  have hNormFG : Integrable (fun x => |F x| * |G x|) μ := by
    convert hFGInt.norm using 1
    ext x
    simp
  have hHolder := integral_mul_norm_le_Lp_mul_Lq
    (f := F) (g := G) (p := 2) (q := 2)
    Real.HolderConjugate.two_two hF' hG'
  have hHolder' :
      ∫ x, |F x| * |G x| ∂μ ≤
        (∫ x, |F x| ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
          (∫ x, |G x| ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
    simpa only [Real.norm_eq_abs] using hHolder
  have hCoeff : ∀ x, Real.exp (-S x) ≤ Real.exp (-r ^ 2 / (8 * A * h)) := by
    intro x
    apply Real.exp_le_exp.mpr
    have hsq := half_square_sum_of_sum_le (hρ₁ x) (hρ₂ x) hr (hsep x)
    have hden : 0 < 8 * A * h := by positivity
    have hsumSq : r ^ 2 / 2 ≤ ρ₁ x ^ 2 + ρ₂ x ^ 2 := hsq
    have hdiv : r ^ 2 / (8 * A * h) ≤ S x := by
      dsimp [S]
      have hden' : 0 < 4 * A * h := by positivity
      rw [← add_div]
      calc
        r ^ 2 / (8 * A * h) = (r ^ 2 / 2) / (4 * A * h) := by
          field_simp [ne_of_gt hden, ne_of_gt hden']
          ring
        _ ≤ (ρ₁ x ^ 2 + ρ₂ x ^ 2) / (4 * A * h) :=
          div_le_div_of_nonneg_right hsumSq (le_of_lt hden')
    have hneg := neg_le_neg hdiv
    rw [← neg_div] at hneg
    exact hneg
  have hfactor : ∀ x, f x * g x = Real.exp (-S x) * (F x * G x) := by
    intro x
    have harg : -(S x) + ρ₁ x ^ 2 / (4 * A * h) +
        ρ₂ x ^ 2 / (4 * A * h) = 0 := by
      dsimp [S]
      ring
    have hexp : Real.exp (-S x) *
        Real.exp (ρ₁ x ^ 2 / (4 * A * h)) *
        Real.exp (ρ₂ x ^ 2 / (4 * A * h)) = 1 := by
      calc
        _ = Real.exp (-(S x) + ρ₁ x ^ 2 / (4 * A * h) +
            ρ₂ x ^ 2 / (4 * A * h)) := by
              rw [← Real.exp_add, ← Real.exp_add]
        _ = 1 := by rw [harg, Real.exp_zero]
    dsimp [F, G]
    calc
      f x * g x =
          (Real.exp (-(S x)) *
            Real.exp (ρ₁ x ^ 2 / (4 * A * h)) *
            Real.exp (ρ₂ x ^ 2 / (4 * A * h))) * (f x * g x) := by
              rw [hexp]
              ring
      _ = Real.exp (-(S x)) *
          (Real.exp (ρ₁ x ^ 2 / (4 * A * h)) * f x *
            (Real.exp (ρ₂ x ^ 2 / (4 * A * h)) * g x)) := by ring
      _ = Real.exp (-(S x)) * (F x * G x) := by rfl
  have hpoint : ∀ x, |f x * g x| ≤
      Real.exp (-r ^ 2 / (8 * A * h)) * (|F x| * |G x|) := by
    intro x
    rw [hfactor x, abs_mul, abs_of_pos (Real.exp_pos _), abs_mul]
    exact mul_le_mul_of_nonneg_right (hCoeff x)
      (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hleftNorm : Integrable (fun x => |f x * g x|) μ := hfgInt.norm
  have hscaledNorm : Integrable
      (fun x => Real.exp (-r ^ 2 / (8 * A * h)) * (|F x| * |G x|)) μ :=
    hNormFG.const_mul _
  have hmono := integral_mono_ae hleftNorm hscaledNorm (ae_of_all μ hpoint)
  calc
    |∫ x, f x * g x ∂μ| = ‖∫ x, f x * g x ∂μ‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∫ x, |f x * g x| ∂μ :=
      norm_integral_le_integral_norm (fun x => f x * g x)
    _ ≤ ∫ x, Real.exp (-r ^ 2 / (8 * A * h)) * (|F x| * |G x|) ∂μ := hmono
    _ = Real.exp (-r ^ 2 / (8 * A * h)) *
        (∫ x, |F x| * |G x| ∂μ) := by rw [integral_const_mul]
    _ ≤ Real.exp (-r ^ 2 / (8 * A * h)) *
        ((∫ x, |F x| ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
          (∫ x, |G x| ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hHolder'
        (Real.exp_nonneg (-r ^ 2 / (8 * A * h)) )
    _ = Real.exp (-r ^ 2 / (8 * A * h)) *
        (∫ x, |Real.exp (ρ₁ x ^ 2 / (4 * A * h)) * f x| ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
        (∫ x, |Real.exp (ρ₂ x ^ 2 / (4 * A * h)) * g x| ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
          dsimp [F, G]
          ring

end PDE.Parabolic.Cauchy.Weights
