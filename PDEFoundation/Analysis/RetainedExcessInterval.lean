module

public import PDEFoundation.Analysis.CoupledOscillationIteration
public import Mathlib.Analysis.SpecificLimits.Normed
public import PDEFoundation.Analysis.FiniteForcedIteration

/-! # Radius iteration retaining the outer excess coefficient -/

@[expose] public section

namespace PDE

/-- Iterate comparisons with successive radius ratios at least `θ`. The last
comparison may have a larger ratio, and its coefficient remains exact. Only
comparisons with both radii in the actual interval `[r,R]` are used. -/
theorem retainedExcessIteration_on_Icc
    (E : ℝ → ℝ) {R r θ A : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hrR : r ≤ R)
    (hθ : 0 < θ) (hθone : θ < 1) (hA : 0 ≤ A)
    (hstep : ∀ {a b : ℝ}, r ≤ a → a ≤ b → b ≤ R → θ * b ≤ a →
      E a ≤ (a / b) * E b + A) :
    E r ≤ (r / R) * E R + A / (1 - θ) := by
  obtain ⟨n, hnlow, hnhigh⟩ := exists_nat_pow_near_of_lt_one
    (div_pos hr hR) ((div_le_one hR).2 hrR) hθ hθone
  have hnpos : 0 < θ ^ n := pow_pos hθ n
  let s := r / θ ^ n
  have hs : 0 < s := div_pos hr hnpos
  have hsR : s ≤ R := by
    apply (div_le_iff₀ hnpos).2
    have hh := (div_le_iff₀ hR).1 hnhigh
    simpa only [mul_comm] using hh
  have hθRs : θ * R ≤ s := by
    apply (le_div_iff₀ hnpos).2
    have hh := (lt_div_iff₀ hR).1 hnlow
    rw [pow_succ] at hh
    linarith only [show θ * R * θ ^ n < r by simpa only [mul_assoc, mul_comm,
      mul_left_comm] using hh]
  have hrs : r ≤ s := by
    exact le_div_self hr.le hnpos (pow_le_one₀ hθ.le hθone.le)
  have hbase : E s ≤ (s / R) * E R + A := hstep hrs hsR le_rfl hθRs
  have hscale (k : ℕ) : 0 < θ ^ k * s := mul_pos (pow_pos hθ k) hs
  have hscaleR (k : ℕ) : θ ^ k * s ≤ R :=
    (mul_le_of_le_one_left hs.le (pow_le_one₀ hθ.le hθone.le)).trans hsR
  have hend : θ ^ n * s = r := mul_div_cancel₀ r hnpos.ne'
  have hrec : ∀ k : ℕ, k < n → E (θ ^ (k + 1) * s) ≤ θ * E (θ ^ k * s) + A := by
    intro k hk
    have heq : θ ^ (k + 1) * s = θ * (θ ^ k * s) := by rw [pow_succ']; ring
    have hle : θ ^ (k + 1) * s ≤ θ ^ k * s := by
      rw [heq]
      exact mul_le_of_le_one_left (hscale k).le hθone.le
    have hra : r ≤ θ ^ (k + 1) * s := by
      rw [← hend]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one hθ.le hθone.le (Nat.succ_le_of_lt hk)) hs.le
    have hh := hstep hra hle (hscaleR k) (by rw [heq])
    rw [heq, mul_div_cancel_right₀ θ (hscale k).ne'] at hh
    simpa only [heq] using hh
  have hfinite := forcedIteration_finiteBound_of_lt (X := fun k => E (θ ^ k * s)) hθ.le hrec
  have hcoeff : θ ^ n * (s / R) = r / R := by rw [← mul_div_assoc, hend]
  calc
    E r ≤ θ ^ n * E s + A * ∑ j ∈ Finset.range n, θ ^ j := by
      simpa only [hend, pow_zero, one_mul] using hfinite
    _ ≤ θ ^ n * ((s / R) * E R + A) + A * ∑ j ∈ Finset.range n, θ ^ j :=
      add_le_add (mul_le_mul_of_nonneg_left hbase hnpos.le) le_rfl
    _ = (r / R) * E R + A * ∑ j ∈ Finset.range (n + 1), θ ^ j := by
      rw [Finset.sum_range_succ]
      rw [mul_add, ← mul_assoc, hcoeff]
      ring
    _ ≤ (r / R) * E R + A * (1 - θ)⁻¹ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (geometric_sum_le_inv_one_sub hθ.le hθone (n + 1)) hA)
    _ = (r / R) * E R + A / (1 - θ) := by simp only [div_eq_mul_inv]

end PDE
