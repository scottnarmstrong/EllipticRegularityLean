module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# ACF-S2: `L²` convergence implies `L¹` convergence of squares

Elementary (no Hölder) estimate: if `pₙ → p` in `L²(μ)` then `pₙ² → p²` in `L¹(μ)`.
-/

@[expose] public section

open MeasureTheory Filter

namespace PDE

noncomputable section

theorem tendsto_integral_abs_sq_sub {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {pn : ℕ → α → ℝ} {p : α → ℝ}
    (hp : Integrable (fun x => p x ^ 2) μ)
    (he : ∀ n, Integrable (fun x => (pn n x - p x) ^ 2) μ)
    (h : Tendsto (fun n => ∫ x, (pn n x - p x) ^ 2 ∂μ) atTop (nhds 0)) :
    Tendsto (fun n => ∫ x, |pn n x ^ 2 - p x ^ 2| ∂μ) atTop (nhds 0) := by
  set c : ℝ := ∫ x, p x ^ 2 ∂μ with hc
  have hc0 : 0 ≤ c := integral_nonneg fun _ => sq_nonneg _
  have key : ∀ t : ℝ, 0 < t → ∀ n, ∫ x, |pn n x ^ 2 - p x ^ 2| ∂μ ≤
      (1 + t) * ∫ x, (pn n x - p x) ^ 2 ∂μ + c / t := by
    intro t ht n
    have hpt : ∀ x, |pn n x ^ 2 - p x ^ 2| ≤
        (1 + t) * (pn n x - p x) ^ 2 + t⁻¹ * p x ^ 2 := by
      intro x
      set e := pn n x - p x
      have h1 : pn n x ^ 2 - p x ^ 2 = e * (e + 2 * p x) := by simp only [e]; ring
      rw [h1, abs_le]
      have h2 : 0 ≤ t * (e + t⁻¹ * p x) ^ 2 := by positivity
      have h3 : 0 ≤ t * (e - t⁻¹ * p x) ^ 2 := by positivity
      have h4 : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
      have h5 : t * (e + t⁻¹ * p x) ^ 2 = t * e ^ 2 + 2 * e * p x * (t * t⁻¹) +
          (t * t⁻¹) * t⁻¹ * p x ^ 2 := by ring
      have h6 : t * (e - t⁻¹ * p x) ^ 2 = t * e ^ 2 - 2 * e * p x * (t * t⁻¹) +
          (t * t⁻¹) * t⁻¹ * p x ^ 2 := by ring
      rw [h4] at h5 h6
      constructor <;> nlinarith only [h2, h3, h5, h6]
    calc ∫ x, |pn n x ^ 2 - p x ^ 2| ∂μ
        ≤ ∫ x, ((1 + t) * (pn n x - p x) ^ 2 + t⁻¹ * p x ^ 2) ∂μ :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
            (((he n).const_mul _).add (hp.const_mul _)) (Eventually.of_forall hpt)
      _ = _ := by
          rw [integral_add ((he n).const_mul _) (hp.const_mul _), integral_const_mul,
            integral_const_mul, div_eq_inv_mul]
  rw [Metric.tendsto_atTop]
  intro ε hε
  set t : ℝ := 2 * (c + 1) / ε with ht
  have htpos : 0 < t := by positivity
  have hct : c / t < ε / 2 := by
    rw [div_lt_iff₀ htpos, ht, mul_div_assoc', div_mul_eq_mul_div, lt_div_iff₀ hε]
    nlinarith
  have hev : ∀ᶠ n in atTop, (1 + t) * ∫ x, (pn n x - p x) ^ 2 ∂μ < ε / 2 := by
    have := (h.const_mul (1 + t))
    rw [mul_zero] at this
    exact this.eventually (gt_mem_nhds (by positivity))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
  have := key t htpos n
  have := hN n hn
  linarith

end

end PDE
