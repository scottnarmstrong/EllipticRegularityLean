module

public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Analysis.Normed.Operator.Mul

/-! # Sharp norm bound for the standard scalar `Lᵖ` pairing -/

@[expose] public section

namespace PDE
open MeasureTheory
open scoped ENNReal
noncomputable section
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The standard scalar integral pairing has functional norm at most
the norm of its density, with constant one. -/
theorem norm_scalarLpPairing_le
    {p q : ENNReal} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (g : Lp ℝ p μ) :
    ‖(ContinuousLinearMap.mul ℝ ℝ).lpPairing μ p q g‖ ≤ ‖g‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g)
  intro f
  have heq : (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ p q g f =
      L1.integral ((ContinuousLinearMap.mul ℝ ℝ).holder 1 g f) := by
    rw [ContinuousLinearMap.lpPairing_eq_integral, L1.integral_eq_integral]
    exact integral_congr_ae ((ContinuousLinearMap.mul ℝ ℝ).coeFn_holder g f).symm
  rw [heq]
  calc
    _ ≤ ‖((ContinuousLinearMap.mul ℝ ℝ).holder 1 g) f‖ := L1.norm_integral_le _
    _ ≤ ‖ContinuousLinearMap.mul ℝ ℝ‖ * ‖g‖ * ‖f‖ :=
      ContinuousLinearMap.norm_holder_apply_apply_le _ _ _
    _ ≤ 1 * ‖g‖ * ‖f‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_mul_le ℝ ℝ)
          (norm_nonneg g)) (norm_nonneg f)
    _ = ‖g‖ * ‖f‖ := by rw [one_mul]

end

end PDE
