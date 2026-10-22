module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Layercake


/-!
# A layer-cake estimate for functions with Gaussian tails

If `μ {|W| > t} ≤ K e^{-b t²}` for every `t > 0`, then
`∫ (|W| - t₀)₊ dμ ≤ K e^{-b t₀²} √(π/b)/2`.
-/

@[expose] public section

open MeasureTheory Set Real

namespace PDE.PoincareAdjustMean

theorem integral_posPart_le_of_gaussian_tail {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (W : α → ℝ) (hW : Integrable W μ) {t0 b K : ℝ} (ht0 : 0 ≤ t0)
    (hb : 0 < b) (hK : 0 ≤ K)
    (hdist : ∀ t : ℝ, 0 < t → μ.real {z | t < |W z|} ≤ K * exp (-b * t ^ 2)) :
    ∫ z, max (|W z| - t0) 0 ∂μ ≤ K * exp (-b * t0 ^ 2) * (√(π / b) / 2) := by
  have hf_int : Integrable (fun z => max (|W z| - t0) 0) μ :=
    (hW.abs.sub (integrable_const t0)).pos_part
  have hf_nn : 0 ≤ᵐ[μ] fun z => max (|W z| - t0) 0 :=
    Filter.Eventually.of_forall fun z => le_max_right _ _
  rw [hf_int.integral_eq_integral_meas_lt hf_nn]
  have hg_int : Integrable (fun t : ℝ => K * exp (-b * t0 ^ 2) * exp (-b * t ^ 2))
      (volume.restrict (Ioi 0)) :=
    ((integrable_exp_neg_mul_sq hb).integrableOn).const_mul _
  calc ∫ t in Ioi 0, μ.real {a | t < max (|W a| - t0) 0}
      ≤ ∫ t in Ioi 0, K * exp (-b * t0 ^ 2) * exp (-b * t ^ 2) := by
        refine integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun t => ENNReal.toReal_nonneg) hg_int ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht' : 0 < t := ht
        have hset : {a | t < max (|W a| - t0) 0} = {a | t0 + t < |W a|} := by
          ext a
          simp only [Set.mem_ofPred_eq, lt_max_iff]
          constructor
          · rintro (h | h)
            · linarith
            · linarith
          · intro h; left; linarith
        rw [hset]
        refine (hdist (t0 + t) (by linarith)).trans ?_
        have hexp : exp (-b * (t0 + t) ^ 2) ≤ exp (-b * t0 ^ 2) * exp (-b * t ^ 2) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.2
          nlinarith [mul_pos hb (mul_pos ht' (by linarith : (0:ℝ) < t0 + t)), mul_nonneg hb.le
            (mul_nonneg ht0 ht'.le)]
        calc K * exp (-b * (t0 + t) ^ 2) ≤ K * (exp (-b * t0 ^ 2) * exp (-b * t ^ 2)) :=
              mul_le_mul_of_nonneg_left hexp hK
          _ = _ := by ring
    _ = K * exp (-b * t0 ^ 2) * (√(π / b) / 2) := by
        rw [integral_const_mul, integral_gaussian_Ioi]

end PDE.PoincareAdjustMean
