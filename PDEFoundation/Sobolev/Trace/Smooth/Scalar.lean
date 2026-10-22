module

public import PDEFoundation.Sobolev.Trace.Defs
public import PDEFoundation.Sobolev.Trace.Model.Defs

/-!
# Scalar and `L^p` bookkeeping for the smooth trace bound

`eLpNorm` as a power of a lower integral of `ofReal (|f|^p)`, the elementary inequality
`|a - b|^p ≤ 2^{p-1} (|a|^p + |b|^p)` in `[0,∞]`, and the Gagliardo integrand `gagKernel` together
with the iterated integral `gagInt` whose `1/p`-th power is `gagliardoSeminorm`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set
open scoped ENNReal NNReal

/-- `‖f‖_{L^p}` as the `1/p`-th power of the integral of `ofReal (|f|^p)`. -/
theorem eLpNorm_eq_lintegral_ofReal_rpow {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ}
    (hp : 0 < p) {f : α → ℝ} (hf : AEStronglyMeasurable f μ) :
    eLpNorm f (ENNReal.ofReal p) μ = (∫⁻ x, ENNReal.ofReal (|f x| ^ p) ∂μ) ^ (1 / p) := by
  rw [eLpNorm_eq_eLpNorm' (by simpa using hp) ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hp.le, eLpNorm']
  congr 1
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le]

/-- The integral of `ofReal (|f|^p)` is the `p`-th power of the norm. -/
theorem lintegral_ofReal_rpow_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ}
    (hp : 0 < p) {f : α → ℝ} (hf : AEStronglyMeasurable f μ) :
    ∫⁻ x, ENNReal.ofReal (|f x| ^ p) ∂μ = eLpNorm f (ENNReal.ofReal p) μ ^ p := by
  rw [eLpNorm_eq_lintegral_ofReal_rpow hp hf, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne',
    ENNReal.rpow_one]

/-- `|a - b|^p ≤ 2^{p-1} (|a|^p + |b|^p)` in `[0,∞]`. -/
theorem ofReal_abs_sub_rpow_le {p : ℝ} (hp : 1 ≤ p) (a b : ℝ) :
    ENNReal.ofReal (|a - b| ^ p) ≤
      ENNReal.ofReal (2 ^ (p - 1)) * (ENNReal.ofReal (|a| ^ p) + ENNReal.ofReal (|b| ^ p)) := by
  have hp0 : 0 ≤ p := by linarith
  have h1 : ENNReal.ofReal (|a - b| ^ p) ≤
      (ENNReal.ofReal |a| + ENNReal.ofReal |b|) ^ p := by
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _),
      ENNReal.ofReal_rpow_of_nonneg (x := |a| + |b|) (by positivity) hp0]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (abs_nonneg _)
      (by simpa [sub_eq_add_neg, abs_neg] using abs_add_le a (-b)) hp0)
  refine h1.trans ?_
  refine (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp).trans ?_
  rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0,
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0,
    show (2 : ℝ≥0∞) ^ (p - 1) = ENNReal.ofReal (2 ^ (p - 1)) by
      rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by linarith)]; simp]

/-- The (non-negative) integrand of the Gagliardo seminorm with kernel exponent `q`. -/
noncomputable def gagKernel {d : ℕ} (q p : ℝ) (f : Vec d → ℝ) (x y : Vec d) : ℝ≥0∞ :=
  ENNReal.ofReal (|f x - f y| ^ p / vecEuclideanNorm (x - y) ^ q)

/-- The `p`-th power of the Gagliardo seminorm of `f` with respect to a measure `μ`. -/
noncomputable def gagInt {d : ℕ} (μ : Measure (Vec d)) (q p : ℝ) (f : Vec d → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y, gagKernel q p f x y ∂μ ∂μ

theorem gagliardoSeminorm_eq {d : ℕ} (Ω : Set (Vec d)) (s p : ℝ) (f : Vec d → ℝ) :
    gagliardoSeminorm Ω s p f =
      gagInt (boundarySurfaceMeasure Ω) ((d : ℝ) - 1 + s * p) p f ^ (1 / p) := rfl

end PDE.TraceLane
