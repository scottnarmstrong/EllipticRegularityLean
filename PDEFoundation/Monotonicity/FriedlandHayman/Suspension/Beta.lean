module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Friedland--Hayman: a Beta-type reduction identity

For real `p > -1` and `N ≥ 1`, `∫_0^{π/2} sin^{N-1} cos^{p+2} = ((p+1)/(p+N+1)) ∫_0^{π/2} sin^{N-1} cos^p`,
together with integrability and positivity of these integrals.
-/

@[expose] public section

open MeasureTheory

namespace PDE.FHLane

noncomputable section

namespace Susp

theorem cos_nonneg_of_mem {θ : ℝ} (h : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) : 0 ≤ Real.cos θ :=
  Real.cos_nonneg_of_mem_Icc ⟨by linarith [h.1, Real.pi_pos], h.2⟩

theorem intervalIntegrable_cos_rpow {p : ℝ} (hp : -1 < p) :
    IntervalIntegrable (fun θ => Real.cos θ ^ p) MeasureTheory.volume 0 (Real.pi / 2) := by
  rcases le_or_gt 0 p with h0 | h0
  · exact (Continuous.rpow_const Real.continuous_cos fun _ => Or.inr h0).intervalIntegrable _ _
  · have hint : IntervalIntegrable (fun θ : ℝ => (2 / Real.pi * (Real.pi / 2 - θ)) ^ p)
        MeasureTheory.volume 0 (Real.pi / 2) := by
      have h1 := ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := Real.pi / 2) hp
        ).comp_sub_left (Real.pi / 2)).symm
      simp only [sub_zero, sub_self] at h1
      have h2 := h1.const_mul ((2 / Real.pi) ^ p)
      refine h2.congr fun θ hθ => ?_
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hθ
      have : 0 ≤ Real.pi / 2 - θ := by linarith [hθ.2]
      rw [Real.mul_rpow (by positivity) this]
    refine hint.mono_fun' (Real.continuous_cos.measurable.pow_const p).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_uIoc).2 (Filter.Eventually.of_forall fun θ hθ => ?_)
    rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hθ
    have hc : 0 ≤ Real.cos θ := cos_nonneg_of_mem ⟨hθ.1.le, hθ.2⟩
    beta_reduce
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hc _)]
    rcases eq_or_lt_of_le hθ.2 with h | h
    · rw [h, Real.cos_pi_div_two, sub_self, mul_zero, Real.zero_rpow h0.ne]
    · have hs : 2 / Real.pi * (Real.pi / 2 - θ) ≤ Real.cos θ := by
        rw [← Real.sin_pi_div_two_sub]
        exact Real.mul_le_sin (by linarith) (by linarith [hθ.1])
      have hpos : 0 < 2 / Real.pi * (Real.pi / 2 - θ) :=
        mul_pos (by positivity) (by linarith)
      exact Real.rpow_le_rpow_of_nonpos hpos hs h0.le

theorem intervalIntegrable_sin_pow_mul_cos_rpow (m : ℕ) {p : ℝ} (hp : -1 < p) :
    IntervalIntegrable (fun θ => Real.sin θ ^ m * Real.cos θ ^ p) MeasureTheory.volume 0
      (Real.pi / 2) := by
  have h := (intervalIntegrable_cos_rpow hp).mul_continuousOn
    (g := fun θ => Real.sin θ ^ m) (by fun_prop)
  exact h.congr fun θ _ => by simp [mul_comm]

/-- The Beta-type integral `∫_0^{π/2} sin^{N-1} cos^p`. -/
def sinCos (N : ℕ) (p : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.sin θ ^ (N - 1) * Real.cos θ ^ p

theorem sinCos_pos (N : ℕ) {p : ℝ} (hp : -1 < p) : 0 < sinCos N p := by
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (intervalIntegrable_sin_pow_mul_cos_rpow _ hp) (fun θ hθ => ?_) (by linarith [Real.pi_pos])
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  positivity

theorem rpow_add_two {c : ℝ} (hc : 0 ≤ c) (p : ℝ) (hp : p + 2 ≠ 0) :
    c ^ (p + 2) = c ^ 2 * c ^ p := by
  rw [Real.rpow_add' hc hp, mul_comm, Real.rpow_two]

theorem sinCos_add_two {N : ℕ} (hN : 1 ≤ N) {p : ℝ} (hp : -1 < p) :
    (p + N + 1) * sinCos N (p + 2) = (p + 1) * sinCos N p := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have hp2 : -1 < p + 2 := by linarith
  have hp1 : 0 < p + 1 := by linarith
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  set f' : ℝ → ℝ := fun θ => ((m : ℝ) + 1) * (Real.sin θ ^ m * Real.cos θ ^ (p + 2)) -
    (p + 1) * (Real.sin θ ^ (m + 2) * Real.cos θ ^ p) with hf'
  have hint1 := intervalIntegrable_sin_pow_mul_cos_rpow m hp2
  have hint2 := intervalIntegrable_sin_pow_mul_cos_rpow (m + 2) hp
  have hint3 := intervalIntegrable_sin_pow_mul_cos_rpow m hp
  have hderiv : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivWithinAt
      (fun θ => Real.sin θ ^ (m + 1) * Real.cos θ ^ (p + 1)) (f' θ) (Set.Ioi θ) θ := by
    intro θ hθ
    have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have h1 : HasDerivAt (fun x => Real.sin x ^ (m + 1))
        (((m + 1 : ℕ) : ℝ) * Real.sin θ ^ (m + 1 - 1) * Real.cos θ) θ :=
      (Real.hasDerivAt_sin θ).pow (m + 1)
    have h2 := (Real.hasDerivAt_cos θ).rpow_const (p := p + 1) (Or.inl hc.ne')
    refine ((h1.mul h2).congr_deriv ?_).hasDerivWithinAt
    have e1 : Real.cos θ ^ (p + 2) = Real.cos θ * Real.cos θ ^ (p + 1) := by
      rw [show p + 2 = 1 + (p + 1) by ring, Real.rpow_add hc, Real.rpow_one]
    have e2 : Real.cos θ ^ (p + 1 - 1) = Real.cos θ ^ p := by rw [add_sub_cancel_right]
    simp only [hf', e1, e2, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    ring
  have hcont : ContinuousOn (fun θ => Real.sin θ ^ (m + 1) * Real.cos θ ^ (p + 1))
      (Set.Icc 0 (Real.pi / 2)) :=
    ((Real.continuous_sin.pow _).mul
      (Continuous.rpow_const Real.continuous_cos fun _ => Or.inr hp1.le)).continuousOn
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hle hcont hderiv
    ((hint1.const_mul _).sub (hint2.const_mul _))
  have hz : Real.cos (Real.pi / 2) ^ (p + 1) = 0 := by
    rw [Real.cos_pi_div_two]; exact Real.zero_rpow hp1.ne'
  simp only [Real.sin_pi_div_two, Real.sin_zero, one_pow, one_mul, hz,
    zero_pow (Nat.succ_ne_zero m), zero_mul, sub_zero] at hFTC
  rw [intervalIntegral.integral_sub (hint1.const_mul _) (hint2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hFTC
  have hrel : ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.sin θ ^ (m + 2) * Real.cos θ ^ p =
      sinCos (m + 1) p - sinCos (m + 1) (p + 2) := by
    unfold sinCos
    simp only [Nat.add_sub_cancel]
    rw [← intervalIntegral.integral_sub hint3 hint1]
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    rw [Set.uIcc_of_le hle] at hθ
    have hc := cos_nonneg_of_mem hθ
    rw [rpow_add_two hc p (by linarith), pow_add, Real.sin_sq]
    ring
  rw [hrel] at hFTC
  unfold sinCos at hFTC ⊢
  simp only [Nat.add_sub_cancel] at hFTC ⊢
  push_cast
  linarith

end Susp

end

end PDE.FHLane
