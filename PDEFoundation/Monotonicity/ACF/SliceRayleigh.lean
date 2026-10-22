module

public import PDEFoundation.Monotonicity.ACF.SliceSmooth

/-!
# ACF-S1: the Rayleigh bound on a smooth slice

If `g` is `C¹` and the closure of its nonvanishing set on the unit sphere lies in `Ω`, then
`λ(Ω) ∫ g² ≤ ∫ |∇_θ g|²` (`sphereDirichletEigenvalue`), and for `g = f(r·)` this combines
with the slice identity into
`∫ |∇f(r·)|² ≥ ∫ (∂_r f)(r·)² + λ r⁻² ∫ f(r·)²`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE

noncomputable section

variable {d : ℕ}

theorem sphereIntegral_zero_nonneg {r : ℝ} (hr : 0 ≤ r) {f : Vec d → ℝ}
    (h : ∀ x ∈ euclideanSphere (0 : Vec d) r, 0 ≤ f x) :
    0 ≤ sphereIntegral (0 : Vec d) r f := by
  rw [sphereIntegral_zero_apply]
  exact mul_nonneg (pow_nonneg hr _)
    (integral_nonneg fun ω => h _ (sphere_smul_toVec_mem r ω))

theorem tangentialGradientNormSq_nonneg {g : Vec d → ℝ} {x : Vec d} (hx : vecNormSq x = 1) :
    0 ≤ tangentialGradientNormSq g x := by
  unfold tangentialGradientNormSq
  have := sq_vecDot_le_vecNormSq_mul_vecNormSq (classicalGradient g x) x
  rw [hx] at this
  linarith

/-- Rayleigh bound on the unit sphere for a `C¹` function whose nonvanishing set has closure
inside `Ω`. -/
theorem sphereDirichletEigenvalue_toReal_mul_le {g : Vec d → ℝ} (hg : ContDiff ℝ 1 g)
    {Ω : Set (Vec d)}
    (hΩ : closure {x | x ∈ euclideanSphere (0 : Vec d) 1 ∧ g x ≠ 0} ⊆ Ω) :
    (sphereDirichletEigenvalue d Ω).toReal * sphereIntegral (0 : Vec d) 1 (fun x => g x ^ 2) ≤
      sphereIntegral (0 : Vec d) 1 (tangentialGradientNormSq g) := by
  have hT : 0 ≤ sphereIntegral (0 : Vec d) 1 (tangentialGradientNormSq g) :=
    sphereIntegral_zero_nonneg zero_le_one fun x hx =>
      tangentialGradientNormSq_nonneg (by
        rw [mem_euclideanSphere_zero_iff] at hx
        simpa using hx)
  have hS : 0 ≤ sphereIntegral (0 : Vec d) 1 (fun x => g x ^ 2) :=
    sphereIntegral_zero_nonneg zero_le_one fun x _ => sq_nonneg _
  rcases hS.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; exact hT
  · have hle : sphereDirichletEigenvalue d Ω ≤
        ENNReal.ofReal (sphereIntegral (0 : Vec d) 1 (tangentialGradientNormSq g) /
          sphereIntegral (0 : Vec d) 1 (fun x => g x ^ 2)) :=
      iInf₂_le g ⟨hg, hΩ, hpos⟩
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rw [ENNReal.toReal_ofReal (div_nonneg hT hS)] at h1
    calc _ ≤ (sphereIntegral (0 : Vec d) 1 (tangentialGradientNormSq g) /
          sphereIntegral (0 : Vec d) 1 (fun x => g x ^ 2)) *
          sphereIntegral (0 : Vec d) 1 (fun x => g x ^ 2) := by gcongr
      _ = _ := div_mul_cancel₀ _ hpos.ne'

/-- ACF-S1: the smooth slice Rayleigh inequality
`∫ |∇f(r·)|² ≥ ∫ (∇f(r·)·ω)² + λ r⁻² ∫ f(r·)²` over the unit sphere. -/
theorem sphereIntegral_gradient_slice_ge {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f) {r : ℝ}
    (hr : r ≠ 0) {Ω : Set (Vec d)}
    (hΩ : closure {x | x ∈ euclideanSphere (0 : Vec d) 1 ∧ f (r • x) ≠ 0} ⊆ Ω) :
    sphereIntegral (0 : Vec d) 1 (fun y => vecDot (classicalGradient f (r • y)) y ^ 2) +
        (sphereDirichletEigenvalue d Ω).toReal * r⁻¹ ^ 2 *
          sphereIntegral (0 : Vec d) 1 (fun y => f (r • y) ^ 2) ≤
      sphereIntegral (0 : Vec d) 1 (fun y => vecNormSq (classicalGradient f (r • y))) := by
  have hg1 : ContDiff ℝ 1 fun y : Vec d => f (r • y) := hf.comp (contDiff_const_smul r)
  have h := sphereDirichletEigenvalue_toReal_mul_le hg1 hΩ
  rw [sphereIntegral_gradient_slice hf hr]
  have h2 : 0 ≤ r⁻¹ ^ 2 := sq_nonneg _
  nlinarith only [mul_le_mul_of_nonneg_left h h2]

end

end PDE
