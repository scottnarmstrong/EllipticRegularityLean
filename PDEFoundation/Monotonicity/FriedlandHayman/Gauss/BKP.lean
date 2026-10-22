module

public import PDEFoundation.Monotonicity.FriedlandHayman.Gauss.Mean

/-!
# Friedland--Hayman: continuity of `β` and the Beckner--Kenig--Pipher inequality

Summing the shift bounds over a grid, using the monotonicity of the mean, gives
`β(t) + β(-t) ≥ 2 - t² / (2k)` for every `k ≥ 1`, hence `2 ≤ β(t) + β(-t)`.
-/

@[expose] public section

open Set MeasureTheory Filter Topology

namespace PDE.FHLane

noncomputable section

theorem continuous_gaussBeta : Continuous gaussBeta := by
  refine continuous_iff_continuousAt.2 fun τ₀ => ?_
  set M := gaussMean τ₀ with hM
  have hbound : ∀ τ, |gaussBeta τ - gaussBeta τ₀| ≤ |τ - τ₀| * |M| / 2 + (τ - τ₀) ^ 2 / 4 := by
    intro τ
    rcases le_total τ τ₀ with h | h
    · have h1 := gaussBeta_shift_upper h
      have h2 := gaussMean_mono h
      have h3 : gaussBeta τ ≤ gaussBeta τ₀ := gaussBeta_mono h
      have h4 : (τ₀ - τ) * gaussMean τ ≤ (τ₀ - τ) * M :=
        mul_le_mul_of_nonneg_left h2 (sub_nonneg.2 h)
      have h5 : (τ₀ - τ) * M ≤ (τ₀ - τ) * |M| :=
        mul_le_mul_of_nonneg_left (le_abs_self M) (sub_nonneg.2 h)
      rw [abs_of_nonpos (sub_nonpos.2 h3), abs_of_nonpos (sub_nonpos.2 h)]
      nlinarith
    · have h1 := gaussBeta_shift_upper h
      have h3 : gaussBeta τ₀ ≤ gaussBeta τ := gaussBeta_mono h
      have h5 : (τ - τ₀) * M ≤ (τ - τ₀) * |M| :=
        mul_le_mul_of_nonneg_left (le_abs_self M) (sub_nonneg.2 h)
      rw [abs_of_nonneg (sub_nonneg.2 h3), abs_of_nonneg (sub_nonneg.2 h)]
      nlinarith
  have hlim : Tendsto (fun τ => |τ - τ₀| * |M| / 2 + (τ - τ₀) ^ 2 / 4) (𝓝 τ₀) (𝓝 0) := by
    have hc : Continuous fun τ : ℝ => |τ - τ₀| * |M| / 2 + (τ - τ₀) ^ 2 / 4 := by fun_prop
    simpa using hc.tendsto τ₀
  have : Tendsto (fun τ => gaussBeta τ - gaussBeta τ₀) (𝓝 τ₀) (𝓝 0) :=
    squeeze_zero_norm (fun τ => by rw [Real.norm_eq_abs]; exact hbound τ) hlim
  have := (tendsto_sub_nhds_zero_iff).1 this
  exact this

theorem gaussBeta_grid_pos (h : ℝ) (hh : 0 ≤ h) (n : ℕ) :
    gaussBeta 0 + n * h * gaussMean 0 / 2 - n * h ^ 2 / 4 ≤ gaussBeta (n * h) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := gaussBeta_shift_lower (τ₁ := n * h) (τ₂ := (n + 1) * h)
      (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
    have hm : gaussMean 0 ≤ gaussMean ((n + 1) * h) :=
      gaussMean_mono (mul_nonneg (by positivity) hh)
    have h2 : h * gaussMean 0 ≤ h * gaussMean ((n + 1) * h) := mul_le_mul_of_nonneg_left hm hh
    push_cast
    rw [show ((n : ℝ) + 1) * h - n * h = h by ring] at h1
    nlinarith

theorem gaussBeta_grid_neg (h : ℝ) (hh : 0 ≤ h) (n : ℕ) :
    gaussBeta 0 - n * h * gaussMean 0 / 2 - n * h ^ 2 / 4 ≤ gaussBeta (-(n * h)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := gaussBeta_shift_upper (τ₁ := -((n + 1) * h)) (τ₂ := -(n * h))
      (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
    have hm : gaussMean (-((n + 1) * h)) ≤ gaussMean 0 :=
      gaussMean_mono (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
    have h2 : h * gaussMean (-((n + 1) * h)) ≤ h * gaussMean 0 :=
      mul_le_mul_of_nonneg_left hm hh
    push_cast
    rw [show -(n * h) - -(((n : ℝ) + 1) * h) = h by ring] at h1
    nlinarith

theorem gaussBeta_add_neg_of_nonneg {t : ℝ} (ht : 0 ≤ t) : 2 ≤ gaussBeta t + gaussBeta (-t) := by
  have key : ∀ k : ℕ, 2 - t ^ 2 / 2 * (1 / ((k : ℝ) + 1)) ≤ gaussBeta t + gaussBeta (-t) := by
    intro k
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hh : 0 ≤ t / ((k : ℝ) + 1) := div_nonneg ht hk.le
    have h1 := gaussBeta_grid_pos _ hh (k + 1)
    have h2 := gaussBeta_grid_neg _ hh (k + 1)
    have e : (((k + 1 : ℕ) : ℝ)) * (t / ((k : ℝ) + 1)) = t := by
      push_cast
      field_simp
    have e2 : (((k + 1 : ℕ) : ℝ)) * (t / ((k : ℝ) + 1)) ^ 2 = t ^ 2 * (1 / ((k : ℝ) + 1)) := by
      push_cast
      field_simp
    rw [e, e2] at h1 h2
    rw [gaussBeta_zero] at h1 h2
    linarith
  have hlim : Tendsto (fun k : ℕ => 2 - t ^ 2 / 2 * (1 / ((k : ℝ) + 1))) atTop (𝓝 2) := by
    have := (tendsto_const_nhds (x := (2 : ℝ))).sub
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (t ^ 2 / 2))
    simpa using this
  exact le_of_tendsto' hlim key

/-- Beckner–Kenig–Pipher. -/
theorem gaussBeta_add_neg (t : ℝ) : 2 ≤ gaussBeta t + gaussBeta (-t) := by
  rcases le_total 0 t with ht | ht
  · exact gaussBeta_add_neg_of_nonneg ht
  · have := gaussBeta_add_neg_of_nonneg (neg_nonneg.2 ht)
    rw [neg_neg] at this
    linarith

end

end PDE.FHLane
