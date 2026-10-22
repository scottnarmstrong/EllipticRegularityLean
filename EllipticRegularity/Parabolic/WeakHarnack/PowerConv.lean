/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.WeakHarnack.PowerCoreNeg
public import EllipticRegularity.Parabolic.WeakHarnack.MeasuresCylinders

/-! # From Lebesgue reverse Hölder steps to `eLpNorm` steps for `cylMeasure` -/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.WeakHarnack

open MeasureTheory Set PDE

variable {d : ℕ}

/-- The `L^e` norm with respect to the normalized measure. -/
theorem eLpNorm_cylMeasure {S T : Set (Vec d × ℝ)} (hT : MeasurableSet T) (hTS : T ⊆ S)
    (f : Vec d × ℝ → ℝ) (hf : AEStronglyMeasurable f ((cylMeasure S).restrict T)) {e : ℝ}
    (he : 0 < e) :
    eLpNorm f (ENNReal.ofReal e) ((cylMeasure S).restrict T) =
      ((volume S)⁻¹ * ∫⁻ z in T, ‖f z‖ₑ ^ e) ^ (1 / e) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using he) ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal he.le, cylMeasure_restrict hT hTS, lintegral_smul_measure]
  simp [smul_eq_mul]

/-- **Conversion of a Lebesgue reverse Hölder step to the normalized `eLpNorm` step.** -/
theorem eLpNorm_step_of_lintegral {S Q' Q : Set (Vec d × ℝ)} (hQ' : MeasurableSet Q')
    (hQ : MeasurableSet Q) (hQ'S : Q' ⊆ S) (hQS : Q ⊆ S) (hS0 : volume S ≠ 0)
    (hSt : volume S ≠ ⊤) (f : Vec d × ℝ → ℝ)
    (hf' : AEStronglyMeasurable f ((cylMeasure S).restrict Q'))
    (hf : AEStronglyMeasurable f ((cylMeasure S).restrict Q)) {p χ B : ℝ} (hp : 0 < p) (hχ : 1 < χ)
    (hB : 0 ≤ B)
    (h : (∫⁻ z in Q', ‖f z‖ₑ ^ (χ * p)) ^ (1 / χ) ≤
      ENNReal.ofReal B * ∫⁻ z in Q, ‖f z‖ₑ ^ p) :
    eLpNorm f (ENNReal.ofReal (χ * p)) ((cylMeasure S).restrict Q') ≤
      ENNReal.ofReal ((((volume S).toReal⁻¹) ^ (1 / χ) * B * (volume S).toReal) ^ (1 / p)) *
        eLpNorm f (ENNReal.ofReal p) ((cylMeasure S).restrict Q) := by
  have hχ0 : 0 < χ := by linarith
  have hVr : 0 < (volume S).toReal := ENNReal.toReal_pos hS0 hSt
  set Vr : ℝ := (volume S).toReal with hVrdef
  have hc : (volume S)⁻¹ = ENNReal.ofReal (Vr⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hVr, hVrdef, ENNReal.ofReal_toReal hSt]
  rw [eLpNorm_cylMeasure hQ' hQ'S f hf' (by positivity), eLpNorm_cylMeasure hQ hQS f hf hp, hc]
  set L1 := ∫⁻ z in Q', ‖f z‖ₑ ^ (χ * p) with hL1
  set L0 := ∫⁻ z in Q, ‖f z‖ₑ ^ p with hL0
  have hp1 : 0 ≤ 1 / p := by positivity
  have hχp : 0 ≤ 1 / (χ * p) := by positivity
  have hcr : 0 < Vr⁻¹ := inv_pos.2 hVr
  rw [ENNReal.mul_rpow_of_nonneg _ _ hχp, ENNReal.mul_rpow_of_nonneg _ _ hp1,
    ENNReal.ofReal_rpow_of_nonneg hcr.le hχp, ENNReal.ofReal_rpow_of_nonneg hcr.le hp1]
  have h1 : L1 ^ (1 / (χ * p)) = (L1 ^ (1 / χ)) ^ (1 / p) := by
    rw [← ENNReal.rpow_mul]; congr 1; field_simp
  have h2 : (L1 ^ (1 / χ)) ^ (1 / p) ≤ (ENNReal.ofReal B * L0) ^ (1 / p) :=
    ENNReal.rpow_le_rpow h hp1
  rw [h1]
  calc ENNReal.ofReal (Vr⁻¹ ^ (1 / (χ * p))) * (L1 ^ (1 / χ)) ^ (1 / p)
      ≤ ENNReal.ofReal (Vr⁻¹ ^ (1 / (χ * p))) * (ENNReal.ofReal B * L0) ^ (1 / p) :=
        mul_le_mul' le_rfl h2
    _ = ENNReal.ofReal ((Vr⁻¹ ^ (1 / (χ * p))) * B ^ (1 / p)) * L0 ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp1, ENNReal.ofReal_rpow_of_nonneg hB hp1,
          ENNReal.ofReal_mul (by positivity), mul_assoc]
    _ = ENNReal.ofReal (((Vr⁻¹ ^ (1 / χ) * B * Vr) ^ (1 / p)) * Vr⁻¹ ^ (1 / p)) *
          L0 ^ (1 / p) := by
        congr 2
        rw [← Real.mul_rpow (by positivity) hcr.le]
        have : Vr⁻¹ ^ (1 / (χ * p)) = (Vr⁻¹ ^ (1 / χ)) ^ (1 / p) := by
          rw [← Real.rpow_mul hcr.le]; congr 1; field_simp
        rw [this, ← Real.mul_rpow (by positivity) hB]
        congr 1
        field_simp
    _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity)]
        ring

end PDE.Parabolic.WeakHarnack
