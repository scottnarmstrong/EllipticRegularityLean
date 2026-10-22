module

public import PDEFoundation.Analysis.ForcedIteration

/-!
# Finite iteration of oscillations and averages

The oscillation recurrence feeds back through the size of the averages. The
proof controls every finite stage by induction; it does not assume that an
infinite supremum is finite before absorbing a small coefficient.
-/

@[expose] public section

namespace PDE

/-- A finite geometric sum is bounded by its infinite geometric majorant. -/
theorem geometric_sum_le_inv_one_sub {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (n : ℕ) :
    (∑ j ∈ Finset.range n, t ^ j) ≤ (1 - t)⁻¹ := by
  have hden : 0 < 1 - t := sub_pos.mpr ht1
  rw [← one_div]
  apply (le_div_iff₀ hden).mpr
  rw [geom_sum_mul_of_le_one ht1.le]
  linarith only [pow_nonneg ht0 n]

/-- Control coupled oscillation and mean recurrences at every finite scale.
Here `E` is the weighted oscillation, `m` is the size of the mean, and `M`
is the full mean-square size. The feedback condition is a scalar inequality
on a proposed bound, rather than an assumption about an infinite supremum. -/
theorem coupledOscillationIteration_bound
    {E m M : ℕ → ℝ} {q t a b D L : ℝ}
    (hq : 0 ≤ q) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (ha : 0 ≤ a) (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hE0 : E 0 ≤ L)
    (hE : ∀ n, E (n + 1) ≤ q * E n + a * M n + b)
    (hm : ∀ n, m (n + 1) ≤ m n + D * t ^ n * E n)
    (hM : ∀ n, M n ≤ m n + t ^ n * E n)
    (hfeedback : q * L + a * (m 0 + (1 + D / (1 - t)) * L) + b ≤ L) :
    ∀ n, E n ≤ L ∧
      m n ≤ m 0 + D * L * ∑ j ∈ Finset.range n, t ^ j ∧
      M n ≤ m 0 + (1 + D / (1 - t)) * L := by
  have hM_of_bounds (n : ℕ) (he : E n ≤ L)
      (hmn : m n ≤ m 0 + D * L * ∑ j ∈ Finset.range n, t ^ j) :
      M n ≤ m 0 + (1 + D / (1 - t)) * L := by
    have ht : t ^ n ≤ 1 := pow_le_one₀ ht0 ht1.le
    have hsum := geometric_sum_le_inv_one_sub ht0 ht1 n
    calc
      M n ≤ m n + t ^ n * E n := hM n
      _ ≤ (m 0 + D * L * ∑ j ∈ Finset.range n, t ^ j) + t ^ n * L :=
        add_le_add hmn (mul_le_mul_of_nonneg_left he (pow_nonneg ht0 n))
      _ ≤ (m 0 + D * L * (1 - t)⁻¹) + L := by
        apply add_le_add
        · exact add_le_add le_rfl
            (mul_le_mul_of_nonneg_left hsum (mul_nonneg hD hL))
        · simpa only [one_mul] using mul_le_mul_of_nonneg_right ht hL
      _ = m 0 + (1 + D / (1 - t)) * L := by
        rw [div_eq_mul_inv]
        ring
  intro n
  induction n with
  | zero =>
      have hm0 : m 0 ≤ m 0 + D * L * ∑ j ∈ Finset.range 0, t ^ j := by
        simp only [Finset.sum_range_zero, mul_zero, add_zero, le_refl]
      exact ⟨hE0, hm0, hM_of_bounds 0 hE0 hm0⟩
  | succ n ih =>
      have he : E (n + 1) ≤ L := by
        calc
          E (n + 1) ≤ q * E n + a * M n + b := hE n
          _ ≤ q * L + a * (m 0 + (1 + D / (1 - t)) * L) + b :=
            add_le_add
              (add_le_add (mul_le_mul_of_nonneg_left ih.1 hq)
                (mul_le_mul_of_nonneg_left ih.2.2 ha)) le_rfl
          _ ≤ L := hfeedback
      have hmn : m (n + 1) ≤
          m 0 + D * L * ∑ j ∈ Finset.range (n + 1), t ^ j := by
        calc
          m (n + 1) ≤ m n + D * t ^ n * E n := hm n
          _ ≤ (m 0 + D * L * ∑ j ∈ Finset.range n, t ^ j) + D * t ^ n * L :=
            add_le_add ih.2.1 (mul_le_mul_of_nonneg_left ih.1
              (mul_nonneg hD (pow_nonneg ht0 n)))
          _ = m 0 + D * L * ∑ j ∈ Finset.range (n + 1), t ^ j := by
            rw [Finset.sum_range_succ]
            ring
      exact ⟨he, hmn, hM_of_bounds (n + 1) he hmn⟩

/-- Small feedback gives explicit uniform bounds, obtained from finite
induction. Its smallness is the product of the contraction gap and the gap
in the geometric series for successive means. -/
theorem coupledOscillationIteration_small_feedback
    {E m M : ℕ → ℝ} {q t a b D : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hD : 0 ≤ D)
    (hE0 : 0 ≤ E 0) (hm0 : 0 ≤ m 0)
    (hE : ∀ n, E (n + 1) ≤ q * E n + a * M n + b)
    (hm : ∀ n, m (n + 1) ≤ m n + D * t ^ n * E n)
    (hM : ∀ n, M n ≤ m n + t ^ n * E n)
    (hsmall : a * (1 + D / (1 - t)) ≤ (1 - q) / 2) :
    ∀ n,
      E n ≤ 2 * (E 0 + (a * m 0 + b) / (1 - q)) ∧
      M n ≤ m 0 + (1 + D / (1 - t)) *
        (2 * (E 0 + (a * m 0 + b) / (1 - q))) := by
  let L := 2 * (E 0 + (a * m 0 + b) / (1 - q))
  have hg : 0 < 1 - q := sub_pos.mpr hq1
  have hforcing : 0 ≤ a * m 0 + b := add_nonneg (mul_nonneg ha hm0) hb
  have hforcingDiv : 0 ≤ (a * m 0 + b) / (1 - q) := div_nonneg hforcing hg.le
  have hL : 0 ≤ L := mul_nonneg (by norm_num) (add_nonneg hE0 hforcingDiv)
  have hinitial : E 0 ≤ L := by
    dsimp only [L]
    linarith only [hE0, hforcingDiv]
  have hmajorant : a * m 0 + b ≤ (1 - q) / 2 * L := by
    have hidentity : (1 - q) / 2 * L = (1 - q) * E 0 + (a * m 0 + b) := by
      dsimp only [L]
      field_simp [hg.ne']
    rw [hidentity]
    exact le_add_of_nonneg_left (mul_nonneg hg.le hE0)
  have hfeedback : q * L + a * (m 0 + (1 + D / (1 - t)) * L) + b ≤ L := by
    calc
      q * L + a * (m 0 + (1 + D / (1 - t)) * L) + b =
          q * L + (a * (1 + D / (1 - t))) * L + (a * m 0 + b) := by ring
      _ ≤ q * L + ((1 - q) / 2) * L + ((1 - q) / 2) * L :=
        add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hsmall hL)) hmajorant
      _ = L := by ring
  have hbound := coupledOscillationIteration_bound hq0 ht0 ht1 ha hD hL
    hinitial hE hm hM hfeedback
  intro n
  exact ⟨(hbound n).1, (hbound n).2.2⟩

end PDE
