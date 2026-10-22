module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Exponential integrability from an exponential distribution tail (layer cake)
-/

@[expose] public section

namespace PDE.DGNMLog

open MeasureTheory Set

theorem integral_exp_mul_eq (a s : ℝ) :
    ∫ t in (0 : ℝ)..s, a * Real.exp (a * t) = Real.exp (a * s) - 1 := by
  have : ∀ x ∈ Set.uIcc (0 : ℝ) s,
      HasDerivAt (fun t => Real.exp (a * t)) (a * Real.exp (a * x)) x := by
    intro x _
    have := ((hasDerivAt_id x).const_mul a).exp
    simpa [mul_comm] using this
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt this]
  · simp
  · exact (continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).intervalIntegrable _ _

/-- Layer-cake estimate of the exponential moment from an exponential tail. -/
theorem lintegral_exp_abs_le {α : Type*} [MeasurableSpace α] {ν : Measure α} {F : α → ℝ}
    (hF : AEMeasurable F ν) {CJ M a : ℝ} (hCJ : 0 < CJ) (hM : 0 < M)
    (ha : 0 < a) (haM : a ≤ 1 / (2 * CJ * M))
    (htail : ∀ t : ℝ, 0 < t → ν {z | t < |F z|} ≤
      ENNReal.ofReal (CJ * Real.exp (-(t / (CJ * M)))) * ν univ) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (a * |F z|)) ∂ν ≤
      (1 + ENNReal.ofReal CJ) * ν univ := by
  have hFabs : AEMeasurable (fun z => |F z|) ν := continuous_abs.measurable.comp_aemeasurable hF
  have hcake := lintegral_comp_eq_lintegral_meas_lt_mul ν
    (f := fun z => |F z|) (Filter.Eventually.of_forall fun z => abs_nonneg _) hFabs
    (g := fun t => a * Real.exp (a * t))
    (fun t _ => (continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).intervalIntegrable _ _)
    (Filter.Eventually.of_forall fun t => by positivity)
  have hpt : ∀ z, ENNReal.ofReal (Real.exp (a * |F z|)) =
      1 + ENNReal.ofReal (∫ t in (0 : ℝ)..|F z|, a * Real.exp (a * t)) := by
    intro z
    rw [integral_exp_mul_eq a _]
    have h1 : 1 ≤ Real.exp (a * |F z|) := Real.one_le_exp (by positivity)
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by linarith)]
    congr 1; ring
  have hmain : ∫⁻ z, ENNReal.ofReal (Real.exp (a * |F z|)) ∂ν =
      ν Set.univ + ∫⁻ t in Ioi (0 : ℝ),
        ν {z | t < |F z|} * ENNReal.ofReal (a * Real.exp (a * t)) := by
    rw [← hcake]
    simp_rw [hpt]
    rw [lintegral_add_left measurable_const]
    simp
  rw [hmain]
  set a0 : ℝ := 1 / (CJ * M) with ha0
  have ha0pos : 0 < a0 := by positivity
  have hab : 2 * a ≤ a0 := by
    have : a ≤ 1 / (2 * CJ * M) := haM
    rw [ha0]
    calc 2 * a ≤ 2 * (1 / (2 * CJ * M)) := by linarith
      _ = 1 / (CJ * M) := by field_simp
  set b : ℝ := a0 - a with hb
  have hbpos : 0 < b := by linarith
  have hab' : a ≤ b := by linarith
  have hbound : ∫⁻ t in Ioi (0 : ℝ), ν {z | t < |F z|} * ENNReal.ofReal (a * Real.exp (a * t)) ≤
      ν univ * ENNReal.ofReal CJ := by
    calc ∫⁻ t in Ioi (0 : ℝ), ν {z | t < |F z|} * ENNReal.ofReal (a * Real.exp (a * t))
        ≤ ∫⁻ t in Ioi (0 : ℝ), ν univ * ENNReal.ofReal (CJ * a * Real.exp (-b * t)) := by
          refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
          have h1 := htail t ht
          have h2 : ENNReal.ofReal (CJ * Real.exp (-(t / (CJ * M)))) * ν univ *
              ENNReal.ofReal (a * Real.exp (a * t)) =
              ν univ * ENNReal.ofReal (CJ * a * Real.exp (-b * t)) := by
            rw [mul_right_comm, ← ENNReal.ofReal_mul (by positivity), mul_comm]
            congr 2
            have : -b * t = -(t / (CJ * M)) + a * t := by rw [hb, ha0]; ring
            rw [this, Real.exp_add]
            ring
          calc ν {z | t < |F z|} * ENNReal.ofReal (a * Real.exp (a * t))
              ≤ ENNReal.ofReal (CJ * Real.exp (-(t / (CJ * M)))) * ν univ *
                  ENNReal.ofReal (a * Real.exp (a * t)) := by gcongr
            _ = _ := h2
      _ = ν univ * ENNReal.ofReal (CJ * a / b) := by
          rw [lintegral_const_mul (f := fun t : ℝ => ENNReal.ofReal (CJ * a * Real.exp (-b * t))) _
            (ENNReal.measurable_ofReal.comp (by fun_prop))]
          congr 1
          have hint : IntegrableOn (fun x : ℝ => CJ * a * Real.exp (-b * x)) (Ioi 0) volume :=
            (integrableOn_exp_mul_Ioi (neg_neg_of_pos hbpos) 0).const_mul (CJ * a)
          rw [← ofReal_integral_eq_lintegral_ofReal hint
            (Filter.Eventually.of_forall fun x => by positivity)]
          congr 1
          rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hbpos)]
          field_simp
          simp
      _ ≤ ν univ * ENNReal.ofReal CJ := by
          gcongr
          rw [div_le_iff₀ hbpos]
          nlinarith
  calc ν univ + _ ≤ ν univ + ν univ * ENNReal.ofReal CJ := by gcongr
    _ = (1 + ENNReal.ofReal CJ) * ν univ := by ring

end PDE.DGNMLog
