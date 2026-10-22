module

public import PDEFoundation.Measure.NormalizedLp
public import PDEFoundation.Ambient.EuclideanNorm
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Norm bookkeeping for the interior reverse Hölder inequality

Auxiliary real-variable statements: the `L^p` seminorm as a real integral power, the
Hölder inequality on a probability space in terms of `eLpNorm`, and the final arithmetic
combining the identity with the Sobolev--Poincaré estimate.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.MeyersRH

open MeasureTheory

theorem toReal_eLpNorm_eq_integral_rpow {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {f : α → ℝ} {p : ℝ} (hp : 0 < p) (hf : MemLp f (ENNReal.ofReal p) μ) :
    (eLpNorm f (ENNReal.ofReal p) μ).toReal = (∫ a, ‖f a‖ ^ p ∂μ) ^ (1 / p) := by
  have h0 : ENNReal.ofReal p ≠ 0 := by simpa using hp
  have h1 : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  rw [hf.eLpNorm_eq_integral_rpow_norm h0 h1, ENNReal.toReal_ofReal]
  · rw [ENNReal.toReal_ofReal hp.le, one_div]
  · exact Real.rpow_nonneg (integral_nonneg fun a => Real.rpow_nonneg (norm_nonneg _) _) _

/-- Hölder's inequality on a probability space in `eLpNorm` form. -/
theorem integral_mul_le_toReal_eLpNorm_mul {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {q q' : ℝ} (hq : q'.HolderConjugate q) {P G : α → ℝ}
    (hP0 : ∀ x, 0 ≤ P x) (hG0 : ∀ x, 0 ≤ G x)
    (hP : MemLp P (ENNReal.ofReal q') μ) (hG : MemLp G (ENNReal.ofReal q) μ) :
    ∫ x, P x * G x ∂μ ≤
      (eLpNorm P (ENNReal.ofReal q') μ).toReal * (eLpNorm G (ENNReal.ofReal q) μ).toReal := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hq (Filter.Eventually.of_forall hP0)
    (Filter.Eventually.of_forall hG0) hP hG
  rw [toReal_eLpNorm_eq_integral_rpow hq.pos hP,
    toReal_eLpNorm_eq_integral_rpow hq.symm.pos hG]
  simpa only [Real.norm_of_nonneg (hP0 _), Real.norm_of_nonneg (hG0 _)] using h

/-- The constant of the interior reverse Hölder inequality. -/
noncomputable def interiorConst (d : ℕ) (S : ℝ) : ℝ :=
  1 + 384 * d * S * 2 ^ d + 128 * d * S

/-- The final arithmetic of Step 2 of Lemma 4.5. -/
theorem interior_arith {d : ℕ} {S r s Wr Fr Vol Qv I1 I2 Hη H : ℝ}
    (hS : 0 < S) (hr : 0 < r) (hs : 1 ≤ s) (hQv : 0 ≤ Qv)
    (hVol : Vol = 2 ^ d * Qv) (hH : H = Vol * Fr ^ 2)
    (hI1 : I1 ≤ 2 * |I2| + Hη) (hHη : Hη ≤ H)
    (hI2 : |I2| ≤ (32 * d / r) * Vol * (S * (2 * (2 * r)) * Wr) * (s * Wr + Fr)) :
    I1 ≤ (interiorConst d S * s) * Qv * Wr ^ 2 + interiorConst d S * H := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hVol0 : 0 ≤ Vol := by rw [hVol]; positivity
  have hH0 : 0 ≤ H := by rw [hH]; positivity
  have h1 : (32 * d / r) * Vol * (S * (2 * (2 * r)) * Wr) * (s * Wr + Fr) =
      128 * d * S * Vol * (Wr * (s * Wr + Fr)) := by
    field_simp; ring
  have h2 : Wr * (s * Wr + Fr) ≤ (3 / 2) * s * Wr ^ 2 + Fr ^ 2 / 2 := by
    linarith [sq_nonneg (Wr - Fr), mul_nonneg (sub_nonneg.2 hs) (sq_nonneg Wr)]
  have h3 : 128 * (d : ℝ) * S * Vol ≥ 0 := by positivity
  have h4 : |I2| ≤ 128 * d * S * Vol * ((3 / 2) * s * Wr ^ 2 + Fr ^ 2 / 2) := by
    rw [h1] at hI2
    exact hI2.trans (mul_le_mul_of_nonneg_left h2 h3)
  have h5 : 128 * (d : ℝ) * S * Vol * ((3 / 2) * s * Wr ^ 2 + Fr ^ 2 / 2) =
      192 * d * S * 2 ^ d * Qv * s * Wr ^ 2 + 64 * d * S * H := by
    rw [hH, hVol]; ring
  have hA : 0 ≤ (d : ℝ) * S * 2 ^ d * (s * Qv * Wr ^ 2) := by positivity
  have hB : 0 ≤ (d : ℝ) * S * H := by positivity
  have hsQW : 0 ≤ s * Qv * Wr ^ 2 := by positivity
  have h6 : I1 ≤ 384 * d * S * 2 ^ d * Qv * s * Wr ^ 2 + (128 * d * S + 1) * H := by
    linarith [abs_nonneg I2]
  have hC1 : 0 ≤ (1 + 128 * d * S) * (s * Qv * Wr ^ 2) := by positivity
  have hC2 : 0 ≤ 384 * (d : ℝ) * S * 2 ^ d * H := by positivity
  unfold interiorConst
  linarith

end PDE.MeyersRH
