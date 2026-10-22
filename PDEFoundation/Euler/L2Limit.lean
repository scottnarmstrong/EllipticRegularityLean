module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Two `L²` facts used for the weak gradient of `v₂`

* `exists_tendsto_eLpNorm_two_of_bound`: a sequence in `L²` that is Cauchy in the quantitative form
  `‖fₘ - fₙ‖₂ ≤ aₘ + aₙ`, `aₙ → 0`, has a strong `L²` limit (Mathlib has no sequential weak compactness,
  so strong convergence of the mollified gradients is what we use);
* `abs_integral_mul_le_eLpNorm_two`: Cauchy-Schwarz `|∫ f g| ≤ ‖f‖₂ ‖g‖₂`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace PDE

section

variable {α E : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E] [CompleteSpace E]

theorem exists_tendsto_eLpNorm_two_of_bound {f : ℕ → α → E} (hf : ∀ n, MemLp (f n) 2 μ)
    {a : ℕ → ℝ≥0∞} (ha : Tendsto a atTop (𝓝 0))
    (h : ∀ m n, eLpNorm (f m - f n) 2 μ ≤ a m + a n) :
    ∃ g : α → E, MemLp g 2 μ ∧ Tendsto (fun n => eLpNorm (f n - g) 2 μ) atTop (𝓝 0) := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have hc : CauchySeq (fun n => (hf n).toLp (f n)) := by
    rw [Lp.cauchySeq_Lp_iff_cauchySeq_eLpNorm]
    have h0 : Tendsto (fun n : ℕ × ℕ => a n.1 + a n.2) atTop (𝓝 0) := by
      have := (ha.comp tendsto_fst).add (ha.comp tendsto_snd)
      rwa [Filter.prod_atTop_atTop_eq, add_zero] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ => bot_le)
      (fun n => ?_)
    refine le_trans (le_of_eq ?_) (h n.1 n.2)
    refine eLpNorm_congr_ae ?_
    filter_upwards [(hf n.1).coeFn_toLp, (hf n.2).coeFn_toLp] with x h2 h3
    simp only [Pi.sub_apply, h2, h3]
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨L, Lp.memLp L, ?_⟩
  have := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ L).1 hL
  refine this.congr (fun n => ?_)
  refine eLpNorm_congr_ae ?_
  filter_upwards [(hf n).coeFn_toLp] with x h2
  simp only [Pi.sub_apply, h2]

end

/-- Cauchy-Schwarz on a measure space: `|∫ f g| ≤ ‖f‖₂ ‖g‖₂`. -/
theorem abs_integral_mul_le_eLpNorm_two {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    abs (∫ x, f x * g x ∂μ) ≤ (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  have hp : (2 : ℝ).HolderConjugate 2 := by
    constructor <;> norm_num
  have hf' : MemLp (fun x => |f x|) (ENNReal.ofReal 2) μ := by
    simpa using (memLp_norm_iff hf.aestronglyMeasurable).2 hf
  have hg' : MemLp (fun x => |g x|) (ENNReal.ofReal 2) μ := by
    simpa using (memLp_norm_iff hg.aestronglyMeasurable).2 hg
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hp (Filter.Eventually.of_forall fun x => abs_nonneg (f x))
    (Filter.Eventually.of_forall fun x => abs_nonneg (g x)) hf' hg'
  have e1 : (eLpNorm f 2 μ).toReal = (∫ x, |f x| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    have := hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
    rw [this, ENNReal.toReal_ofReal (by positivity)]
    simp only [Real.norm_eq_abs, ENNReal.toReal_ofNat, one_div]
  have e2 : (eLpNorm g 2 μ).toReal = (∫ x, |g x| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    have := hg.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
    rw [this, ENNReal.toReal_ofReal (by positivity)]
    simp only [Real.norm_eq_abs, ENNReal.toReal_ofNat, one_div]
  rw [e1, e2]
  refine le_trans ?_ h
  refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
  simp only [abs_mul]

end PDE
