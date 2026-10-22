module

public import EllipticRegularity.DeGiorgi.Holder.OscStep
public import EllipticRegularity.DeGiorgi.Holder.ScaledLinfty
public import EllipticRegularity.DeGiorgi.Holder.Iteration
public import EllipticRegularity.DeGiorgi.Holder.Representative
public import EllipticRegularity.DeGiorgi.LocalMax.Main
public import PDEFoundation.Geometry.ConvexDomain
public import PDEFoundation.Geometry.EuclideanBall.Interior
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# De Giorgi's interior Hölder estimate

Assembly of Theorem 4.8: the `L^∞` estimate (`DGNMLocalMax`), the
oscillation decay step from expansion of positivity, the dyadic iteration, and the
Hölder representative.  The expansion-of-positivity statement and the two class
stability facts are explicit hypotheses.
-/

@[expose] public section

namespace PDE.DGNMHolder

open PDE MeasureTheory

variable {d : ℕ}

/-- The scale factor in the rescaled `L²` norm is at most `2 ^ d` for `ρ ≥ 1/4`. -/
theorem scaleFactor_le {ρ : ℝ} (hρ : 1 / 4 ≤ ρ) :
    ENNReal.ofReal ((ρ ^ d)⁻¹) ^ ((1 : ℝ) / 2) ≤ ENNReal.ofReal ((2 : ℝ) ^ d) := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le (by norm_num) hρ
  have hpos : 0 < ρ ^ d := pow_pos hρ0 d
  rw [ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.2 hpos.le) (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  have h1 : (ρ ^ d)⁻¹ ≤ ((2 : ℝ) ^ d) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    have : ((1 : ℝ) / 4) ^ d ≤ ρ ^ d := pow_le_pow_left₀ (by norm_num) hρ d
    calc (ρ ^ d)⁻¹ ≤ (((1 : ℝ) / 4) ^ d)⁻¹ := inv_anti₀ (by positivity) this
      _ = ((2 : ℝ) ^ 2) ^ d := by
        rw [← inv_pow]; congr 1; norm_num
  calc ((ρ ^ d)⁻¹) ^ ((1 : ℝ) / 2) ≤ (((2 : ℝ) ^ d) ^ 2) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow (inv_nonneg.2 hpos.le) h1 (by norm_num)
    _ = (2 : ℝ) ^ d := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num

/-- Essential range bounds for the zero extension. -/
theorem range_indicator {u : Vec d → ℝ} {S : Set (Vec d)} (hS : MeasurableSet S)
    (hSB : S ⊆ euclideanBall (0 : Vec d) 1) {m M : ℝ}
    (h : EssentialRangeBoundsOn u S m M) :
    EssentialRangeBoundsOn ((euclideanBall (0 : Vec d) 1).indicator u) S m M := by
  filter_upwards [h, ae_restrict_mem hS] with x hx hxS
  rw [Set.indicator_of_mem (hSB hxS)]
  exact hx

theorem exists_alpha {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ δ ≤ α ∧ 1 - δ ≤ (2 : ℝ) ^ (-α) := by
  have h1δ : 0 < 1 - δ := by linarith
  set A : ℝ := Real.logb 2 (1 / (1 - δ)) with hA
  have hAgt : 1 < 1 / (1 - δ) := (one_lt_div h1δ).2 (by linarith)
  have hApos : 0 < A := Real.logb_pos (by norm_num) hAgt
  have hlog2 : 0 < Real.log 2 := (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have hlog2le : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hδA : δ ≤ A := by
    rw [hA, Real.logb, le_div_iff₀ hlog2, one_div, Real.log_inv]
    have := Real.log_le_sub_one_of_pos h1δ
    nlinarith
  refine ⟨min 1 A, lt_min one_pos hApos, min_le_left _ _, le_min (by linarith) hδA, ?_⟩
  have h2A : (2 : ℝ) ^ (-A) = 1 - δ := by
    rw [Real.rpow_neg (by norm_num), hA, Real.rpow_logb (by norm_num) (by norm_num)
      (by positivity)]
    field_simp
  calc 1 - δ = (2 : ℝ) ^ (-A) := h2A.symm
    _ ≤ (2 : ℝ) ^ (-(min 1 A)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [min_le_right 1 A])

end PDE.DGNMHolder
