module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.Order.Floor
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A derivative-free Gronwall lemma

A continuous nonnegative function with `f t ≤ L ∫_s^t f` on `[s, t₀]` vanishes there. Proved by
iterating the inequality, so no differentiability is used.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace PDE

/-- Iterated bound: `f t ≤ M (L (t - s))^n / n!`. -/
theorem gronwall_iterate {f : ℝ → ℝ} {s t₀ L M : ℝ} (hL : 0 ≤ L)
    (hf : ContinuousOn f (Icc s t₀))
    (hM : ∀ t ∈ Icc s t₀, f t ≤ M)
    (hineq : ∀ t ∈ Icc s t₀, f t ≤ L * ∫ τ in s..t, f τ) (n : ℕ) :
    ∀ t ∈ Icc s t₀, f t ≤ M * (L * (t - s)) ^ n / (n.factorial : ℝ) := by
  induction n with
  | zero => intro t ht; simpa using hM t ht
  | succ n ih =>
    intro t ht
    have hst : s ≤ t := ht.1
    have hsub : Icc s t ⊆ Icc s t₀ := Icc_subset_Icc_right ht.2
    have hfi : IntervalIntegrable f volume s t :=
      (hf.mono hsub).intervalIntegrable_of_Icc hst
    have hgi : IntervalIntegrable (fun τ => M * (L * (τ - s)) ^ n / (n.factorial : ℝ)) volume s t :=
      (Continuous.intervalIntegrable (by fun_prop) _ _)
    have hmono : ∫ τ in s..t, f τ ≤ ∫ τ in s..t, M * (L * (τ - s)) ^ n / (n.factorial : ℝ) := by
      refine intervalIntegral.integral_mono_on hst hfi hgi ?_
      intro τ hτ
      exact ih τ ⟨hτ.1, hτ.2.trans ht.2⟩
    have hcalc : ∫ τ in s..t, M * (L * (τ - s)) ^ n / (n.factorial : ℝ)
        = M * L ^ n * (t - s) ^ (n + 1) / ((n + 1 : ℝ) * (n.factorial : ℝ)) := by
      have h1 : ∫ τ in s..t, (τ - s) ^ n = (t - s) ^ (n + 1) / (n + 1) := by
        rw [intervalIntegral.integral_comp_sub_right (fun x => x ^ n) s, integral_pow]
        simp
      have h2 : (fun τ : ℝ => M * (L * (τ - s)) ^ n / (n.factorial : ℝ))
          = fun τ => (M * L ^ n / (n.factorial : ℝ)) * (τ - s) ^ n := by
        funext τ; rw [mul_pow]; ring
      rw [h2, intervalIntegral.integral_const_mul, h1]
      field_simp
    calc f t ≤ L * ∫ τ in s..t, f τ := hineq t ht
      _ ≤ L * ∫ τ in s..t, M * (L * (τ - s)) ^ n / (n.factorial : ℝ) :=
          mul_le_mul_of_nonneg_left hmono hL
      _ = M * (L * (t - s)) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
          rw [hcalc, Nat.factorial_succ, mul_pow]; push_cast; field_simp; ring

/-- Derivative-free Gronwall: `f ≤ L ∫_s^t f` with `f` continuous and nonnegative forces `f = 0`. -/
theorem gronwall_eq_zero {f : ℝ → ℝ} {s t₀ L : ℝ} (hL : 0 ≤ L)
    (hf : ContinuousOn f (Icc s t₀)) (hf0 : ∀ t ∈ Icc s t₀, 0 ≤ f t)
    (hineq : ∀ t ∈ Icc s t₀, f t ≤ L * ∫ τ in s..t, f τ) :
    ∀ t ∈ Icc s t₀, f t = 0 := by
  intro t ht
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := s) (b := t₀)).exists_bound_of_continuousOn hf
  have hM' : ∀ t ∈ Icc s t₀, f t ≤ |M| := fun t ht =>
    (le_abs_self _).trans (by simpa using (hM t ht).trans (le_abs_self M))
  have hb := gronwall_iterate hL hf hM' hineq
  have hlim : Tendsto (fun n : ℕ => |M| * ((L * (t - s)) ^ n / (n.factorial : ℝ))) atTop (𝓝 0) := by
    simpa using (FloorSemiring.tendsto_pow_div_factorial_atTop (L * (t - s))).const_mul |M|
  refine le_antisymm ?_ (hf0 t ht)
  refine le_of_tendsto_of_tendsto' tendsto_const_nhds hlim (fun n => ?_)
  have := hb n t ht
  rwa [mul_div_assoc] at this

end PDE
