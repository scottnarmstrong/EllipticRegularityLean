module

public import PDEFoundation.Sobolev.Inequalities.SobolevPoincare
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# From `w = f ^ (p/2)` to norms of `f`

Pure `ℝ≥0∞` conversion: an estimate `‖f^{p/2}‖_{q} ≤ C ‖f^{p/2}‖_{2}` gives
`‖f‖_{pq/2} ≤ C^{2/p} ‖f‖_{p}`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.DGNMOneStep

open MeasureTheory PDE

variable {α : Type*} [MeasurableSpace α]

theorem eLpNorm_le_of_rpow_half {μ₁ μ₂ : Measure α} {f : α → ℝ} {p q C : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hC : 0 ≤ C)
    (hf₁ : AEStronglyMeasurable f μ₁) (hf₂ : AEStronglyMeasurable f μ₂)
    (hpos₁ : ∀ᵐ x ∂μ₁, 0 ≤ f x) (hpos₂ : ∀ᵐ x ∂μ₂, 0 ≤ f x)
    (h : eLpNorm (fun x => f x ^ (p / 2)) (ENNReal.ofReal q) μ₁ ≤
      ENNReal.ofReal C * eLpNorm (fun x => f x ^ (p / 2)) 2 μ₂) :
    eLpNorm f (ENNReal.ofReal (p * (q / 2))) μ₁ ≤
      ENNReal.ofReal (C ^ (2 / p)) * eLpNorm f (ENNReal.ofReal p) μ₂ := by
  have he : 0 < p / 2 := by positivity
  have e1 : eLpNorm (fun x => f x ^ (p / 2)) (ENNReal.ofReal q) μ₁ =
      eLpNorm f (ENNReal.ofReal (p * (q / 2))) μ₁ ^ (p / 2) := by
    rw [eLpNorm_congr_ae (g := fun x => ‖f x‖ ^ (p / 2))
      (by filter_upwards [hpos₁] with x hx; simp [Real.norm_eq_abs, abs_of_nonneg hx])]
    rw [eLpNorm_norm_rpow f hf₁ he, ← ENNReal.ofReal_mul hq.le]
    congr 3; ring
  have e2 : eLpNorm (fun x => f x ^ (p / 2)) 2 μ₂ =
      eLpNorm f (ENNReal.ofReal p) μ₂ ^ (p / 2) := by
    rw [eLpNorm_congr_ae (g := fun x => ‖f x‖ ^ (p / 2))
      (by filter_upwards [hpos₂] with x hx; simp [Real.norm_eq_abs, abs_of_nonneg hx])]
    rw [eLpNorm_norm_rpow f hf₂ he]
    congr 2
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1; ring
  rw [e1, e2] at h
  have h2 := ENNReal.rpow_le_rpow h (show 0 ≤ 1 / (p / 2) by positivity)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    mul_one_div_cancel he.ne', ENNReal.rpow_one, ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg hC (by positivity)] at h2
  have : 1 / (p / 2) = 2 / p := by field_simp
  rw [this] at h2
  exact h2

end PDE.DGNMOneStep
