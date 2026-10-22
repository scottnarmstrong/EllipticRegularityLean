module

public import PDEFoundation.Monotonicity.Defs
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Gaussian integrability on `Vec d`

Integrability of `(1 + |x|²)^k exp(-c |x|²)` over `Vec d` and the locally uniform Gaussian
domination bundle for the heat kernel used in Poon's monotonicity formula.
-/

@[expose] public section

open MeasureTheory

namespace PDE

noncomputable section

/-- `exp(-c |x|²)` is integrable on `Vec d` for `c > 0`. -/
theorem integrable_exp_neg_mul_vecNormSq {d : ℕ} {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : Vec d => Real.exp (-c * vecNormSq x)) (volume : Measure (Vec d)) := by
  have h : Integrable (fun x : Vec d => ∏ i, Real.exp (-c * x i ^ 2))
      (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) :=
    Integrable.fintype_prod (fun _ => integrable_exp_neg_mul_sq hc)
  have hv : (volume : Measure (Vec d)) = Measure.pi fun _ : Fin d => (volume : Measure ℝ) := rfl
  rw [hv]
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [vecNormSq_eq_sum_sq, Finset.mul_sum, neg_mul]
  rw [← Real.exp_sum]

/-- Elementary polynomial-to-exponential bound. -/
theorem pow_one_add_le_mul_exp {ε : ℝ} (hε : 0 < ε) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (1 + t) ^ k ≤ (k.factorial : ℝ) * ε⁻¹ ^ k * Real.exp ε * Real.exp (ε * t) := by
  have h0 : 0 ≤ ε * (1 + t) := by positivity
  have h1 := Real.pow_div_factorial_le_exp (ε * (1 + t)) h0 k
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have h2 : (ε * (1 + t)) ^ k ≤ k.factorial * Real.exp (ε * (1 + t)) := by
    rw [div_le_iff₀ hf] at h1
    exact h1.trans_eq (mul_comm _ _)
  have h3 : (1 + t) ^ k = ε⁻¹ ^ k * (ε * (1 + t)) ^ k := by
    rw [mul_pow, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hε.ne', one_pow, one_mul]
  have h4 : Real.exp (ε * (1 + t)) = Real.exp ε * Real.exp (ε * t) := by
    rw [mul_add, mul_one, Real.exp_add]
  rw [h3]
  calc ε⁻¹ ^ k * (ε * (1 + t)) ^ k ≤ ε⁻¹ ^ k * (k.factorial * Real.exp (ε * (1 + t))) := by
        gcongr
    _ = _ := by rw [h4]; ring

/-- Polynomially weighted Gaussians are integrable on `Vec d`. -/
theorem integrable_pow_one_add_vecNormSq_mul_exp {d : ℕ} {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Integrable (fun x : Vec d => (1 + vecNormSq x) ^ k * Real.exp (-c * vecNormSq x))
      (volume : Measure (Vec d)) := by
  have hε : 0 < c / 2 := by positivity
  set C : ℝ := (k.factorial : ℝ) * (c / 2)⁻¹ ^ k * Real.exp (c / 2) with hC
  have hint := (integrable_exp_neg_mul_vecNormSq (d := d) hε).const_mul C
  refine Integrable.mono' hint ?_ (Filter.Eventually.of_forall fun x => ?_)
  · have : Measurable (vecNormSq : Vec d → ℝ) := by
      have e : (vecNormSq : Vec d → ℝ) = fun x => ∑ i, x i ^ 2 := funext vecNormSq_eq_sum_sq
      rw [e]; fun_prop
    exact (by fun_prop : Measurable fun x : Vec d => (1 + vecNormSq x) ^ k *
      Real.exp (-c * vecNormSq x)).aestronglyMeasurable
  · have hq := vecNormSq_nonneg x
    rw [Real.norm_of_nonneg (by positivity)]
    have h := pow_one_add_le_mul_exp hε k hq
    calc (1 + vecNormSq x) ^ k * Real.exp (-c * vecNormSq x)
        ≤ (C * Real.exp (c / 2 * vecNormSq x)) * Real.exp (-c * vecNormSq x) := by
          gcongr
      _ = C * Real.exp (-(c / 2) * vecNormSq x) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- The heat kernel is positive for `s > 0`. -/
theorem heatKernel_pos (d : ℕ) {s : ℝ} (hs : 0 < s) (x : Vec d) : 0 < heatKernel d s x := by
  unfold heatKernel
  have : 0 < 4 * Real.pi * s := by positivity
  positivity

/-- Pointwise Gaussian bound for the heat kernel on `s ∈ [a, b]`, with the exponential weight
`exp (2 A' |x|²)` absorbed. -/
theorem exp_mul_heatKernel_le {d : ℕ} {a b A' : ℝ} (ha : 0 < a)
    {s : ℝ} (hs : s ∈ Set.Icc a b) (x : Vec d) :
    Real.exp (2 * A' * vecNormSq x) * heatKernel d s x ≤
      (4 * Real.pi * a) ^ (-(d : ℝ) / 2) * Real.exp (-(1 / (4 * b) - 2 * A') * vecNormSq x) := by
  obtain ⟨has, hsb⟩ := hs
  have hs0 : 0 < s := ha.trans_le has
  have hb0 : 0 < b := hs0.trans_le hsb
  have hq := vecNormSq_nonneg x
  unfold heatKernel
  have h1 : (4 * Real.pi * s) ^ (-(d : ℝ) / 2) ≤ (4 * Real.pi * a) ^ (-(d : ℝ) / 2) := by
    apply Real.rpow_le_rpow_of_nonpos (by positivity) (by gcongr)
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have h2 : Real.exp (-vecNormSq x / (4 * s)) ≤ Real.exp (-vecNormSq x / (4 * b)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left hq (by positivity) (by gcongr)
  have h3 : 0 ≤ (4 * Real.pi * s) ^ (-(d : ℝ) / 2) := by positivity
  calc Real.exp (2 * A' * vecNormSq x) *
        ((4 * Real.pi * s) ^ (-(d : ℝ) / 2) * Real.exp (-vecNormSq x / (4 * s)))
      ≤ Real.exp (2 * A' * vecNormSq x) *
        ((4 * Real.pi * a) ^ (-(d : ℝ) / 2) * Real.exp (-vecNormSq x / (4 * b))) := by
        gcongr
    _ = _ := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        field_simp
        ring

/-- Locally uniform Gaussian domination for the heat kernel (plan §4.1, step 1). For `A : ℝ`
(any sign) and `0 < a ≤ b` with `8 A b < 1` there is `A' > A` with `8 A' b < 1` such that, for
every polynomial degree `k`, `(1 + |x|²)^k exp (2 A' |x|²) Φ(s,x) ≤ M exp (-c |x|²)` uniformly
for `s ∈ [a, b]`. -/
theorem heatKernel_gaussian_domination (d : ℕ) (A : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hAb : 8 * A * b < 1) :
    ∃ A' : ℝ, A < A' ∧ 8 * A' * b < 1 ∧ ∀ k : ℕ, ∃ c M : ℝ, 0 < c ∧ 0 ≤ M ∧
      ∀ s ∈ Set.Icc a b, ∀ x : Vec d,
        (1 + vecNormSq x) ^ k * (Real.exp (2 * A' * vecNormSq x) * heatKernel d s x) ≤
          M * Real.exp (-c * vecNormSq x) := by
  have hb0 : 0 < b := ha.trans_le hab
  refine ⟨(A + 1 / (8 * b)) / 2, ?_, ?_, fun k => ?_⟩
  · have : A < 1 / (8 * b) := by rw [lt_div_iff₀ (by positivity)]; linarith
    linarith
  · have h : A < 1 / (8 * b) := by rw [lt_div_iff₀ (by positivity)]; linarith
    have e : 8 * ((A + 1 / (8 * b)) / 2) * b = 4 * A * b + 1 / 2 := by field_simp; ring
    rw [e]; linarith
  · set A' := (A + 1 / (8 * b)) / 2 with hA'
    have hc0 : 0 < 1 / (4 * b) - 2 * A' := by
      have h : A < 1 / (8 * b) := by rw [lt_div_iff₀ (by positivity)]; linarith
      have e : 1 / (4 * b) - 2 * A' = 1 / (8 * b) - A := by rw [hA']; field_simp; ring
      rw [e]; linarith
    set c0 := 1 / (4 * b) - 2 * A' with hc0def
    have hε : 0 < c0 / 2 := by positivity
    set P := (4 * Real.pi * a) ^ (-(d : ℝ) / 2) with hP
    set C : ℝ := (k.factorial : ℝ) * (c0 / 2)⁻¹ ^ k * Real.exp (c0 / 2) with hC
    refine ⟨c0 / 2, P * C, hε, by positivity, fun s hs x => ?_⟩
    have hq := vecNormSq_nonneg x
    have h1 := exp_mul_heatKernel_le (d := d) ha (b := b) (A' := A') hs x
    have h2 := pow_one_add_le_mul_exp hε k hq
    calc (1 + vecNormSq x) ^ k * (Real.exp (2 * A' * vecNormSq x) * heatKernel d s x)
        ≤ (C * Real.exp (c0 / 2 * vecNormSq x)) *
          (P * Real.exp (-c0 * vecNormSq x)) := by
          have hΦ := heatKernel_pos d (ha.trans_le hs.1) x
          gcongr
      _ = P * C * Real.exp (-(c0 / 2) * vecNormSq x) := by
          have : Real.exp (c0 / 2 * vecNormSq x) * Real.exp (-c0 * vecNormSq x)
              = Real.exp (-(c0 / 2) * vecNormSq x) := by
            rw [← Real.exp_add]; congr 1; ring
          calc _ = P * C * (Real.exp (c0 / 2 * vecNormSq x) * Real.exp (-c0 * vecNormSq x)) := by
                ring
            _ = _ := by rw [this]

end

end PDE
