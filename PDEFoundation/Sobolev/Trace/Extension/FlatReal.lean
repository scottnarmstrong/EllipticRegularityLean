module

public import PDEFoundation.Sobolev.Trace.Extension.FlatBasic

/-!
# The real-variable inequality for pairs inside the chart ball

For `x', y'` in the chart ball, with `X = Ψ₀ x'`, `Y = Ψ₀ y'`, `w = ζ g ∘ Ψ₀`:
`|w x' - w y'|^p / |x' - y'|^q` is bounded by a multiple of `|g X - g Y|^p / |X - Y|^q` plus a
multiple of `(|g X|^p + |g Y|^p) · min(a, b |x' - y'|)^p / |x' - y'|^q`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set
open scoped ENNReal NNReal

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

/-- Convexity of `t ↦ t^p`, in the form `(u + v)^p ≤ 2^(p-1) (u^p + v^p)`. -/
theorem real_add_rpow_le {u v p : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hp : 1 ≤ p) :
    (u + v) ^ p ≤ 2 ^ (p - 1) * (u ^ p + v ^ p) := by
  have h := NNReal.rpow_add_le_mul_rpow_add_rpow u.toNNReal v.toNNReal hp
  have h' := (NNReal.coe_le_coe.2 h)
  simpa [Real.coe_toNNReal _ hu, Real.coe_toNNReal _ hv, NNReal.coe_rpow, NNReal.coe_add,
    NNReal.coe_mul] using h'

/-- Comparison of the flat and the ambient distance. -/
theorem div_rpow_le_of_le_mul {A s d s0 q : ℝ} (hA : 0 ≤ A) (hq : 0 < q) (hs : 0 ≤ s)
    (hsd : s ≤ d) (hd : d ≤ s0 * s) : A / s ^ q ≤ s0 ^ q * (A / d ^ q) := by
  have hd0 : 0 ≤ d := hs.trans hsd
  rcases hs.eq_or_lt with rfl | hspos
  · have hd' : d = 0 := le_antisymm (by simpa using hd) hd0
    subst hd'
    simp [Real.zero_rpow hq.ne']
  · have hdpos : 0 < d := hspos.trans_le hsd
    have hs0 : 0 ≤ s0 := by
      by_contra h
      have h' := lt_of_not_ge h
      nlinarith
    have hsq : 0 < s ^ q := Real.rpow_pos_of_pos hspos q
    have hdq : 0 < d ^ q := Real.rpow_pos_of_pos hdpos q
    rw [div_le_iff₀ hsq]
    have h1 : d ^ q ≤ (s0 * s) ^ q := Real.rpow_le_rpow hd0 hd hq.le
    rw [Real.mul_rpow hs0 hspos.le] at h1
    have h2 : A ≤ (s0 ^ q * s ^ q) * (A / d ^ q) := by
      calc A = d ^ q * (A / d ^ q) := by field_simp
        _ ≤ (s0 ^ q * s ^ q) * (A / d ^ q) :=
          mul_le_mul_of_nonneg_right h1 (div_nonneg hA hdq.le)
    calc A ≤ (s0 ^ q * s ^ q) * (A / d ^ q) := h2
      _ = s0 ^ q * (A / d ^ q) * s ^ q := by ring

namespace GraphChart

/-- The real-variable inequality for a pair of points of the chart ball. -/
theorem flat_real_ineq (φ : GraphChart Ω) {ζ : Vec (n + 1) → ℝ} {M Lz δ p : ℝ} (hp : 1 < p)
    (hM0 : 0 ≤ M) (hM : ∀ X, |ζ X| ≤ M) (hLz0 : 0 ≤ Lz)
    (hLz : ∀ X Y, |ζ X - ζ Y| ≤ Lz * vecEuclideanNorm (X - Y)) (hδ : 0 < δ)
    (g : Vec (n + 1) → ℝ) (x' y' : Vec n) :
    |flatPullback φ ζ g x' - flatPullback φ ζ g y'| ^ p /
        vecEuclideanNorm (x' - y') ^ ((n : ℝ) + p - 1) ≤
      2 ^ (p - 1) * M ^ p * Real.sqrt (1 + φ.L ^ 2) ^ ((n : ℝ) + p - 1) *
          (|g (φ.map (x', 0)) - g (φ.map (y', 0))| ^ p /
            vecEuclideanNorm (φ.map (x', 0) - φ.map (y', 0)) ^ ((n : ℝ) + p - 1)) +
        (2 ^ (p - 1) + M ^ p) * ((|g (φ.map (x', 0))| ^ p + |g (φ.map (y', 0))| ^ p) *
          (min (2 * M + 1) ((Lz * Real.sqrt (1 + φ.L ^ 2) + 1 / δ) * vecEuclideanNorm (x' - y')) ^ p /
            vecEuclideanNorm (x' - y') ^ ((n : ℝ) + p - 1))) := by
  set q : ℝ := (n : ℝ) + p - 1 with hqdef
  set s0 : ℝ := Real.sqrt (1 + φ.L ^ 2) with hs0def
  set X := φ.map (x', 0) with hX
  set Y := φ.map (y', 0) with hY
  set s := vecEuclideanNorm (x' - y') with hsdef
  set d := vecEuclideanNorm (X - Y) with hddef
  set m := min (2 * M + 1) ((Lz * s0 + 1 / δ) * s) with hm
  have hp0 : 0 < p := by linarith
  have hq : 0 < q := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hs : 0 ≤ s := vecEuclideanNorm_nonneg _
  have hs0 : 0 ≤ s0 := Real.sqrt_nonneg _
  have hdle : d ≤ s0 * s := vecEuclideanNorm_graphMap_zero_sub_le φ.γ_lip x' y'
  have hsd : s ≤ d := vecEuclideanNorm_sub_le_graphMap (i := φ.i) (γ := φ.γ) (sgn := φ.sgn)
    (x', 0) (y', 0)
  have hsq : 0 ≤ s ^ q := Real.rpow_nonneg hs q
  have hmnn : 0 ≤ m := le_min (by linarith) (by
    have : 0 ≤ 1 / δ := by positivity
    positivity)
  have hζ1 : |ζ X - ζ Y| ≤ 2 * M := by
    calc |ζ X - ζ Y| ≤ |ζ X| + |ζ Y| := abs_sub _ _
      _ ≤ M + M := add_le_add (hM X) (hM Y)
      _ = 2 * M := by ring
  have hζ2 : |ζ X - ζ Y| ≤ Lz * s0 * s := by
    calc |ζ X - ζ Y| ≤ Lz * d := hLz X Y
      _ ≤ Lz * (s0 * s) := mul_le_mul_of_nonneg_left hdle hLz0
      _ = Lz * s0 * s := by ring
  have hζ : |ζ X - ζ Y| ≤ m := by
    have hδ' : 0 ≤ 1 / δ := by positivity
    refine le_min (hζ1.trans (by linarith)) (hζ2.trans (by nlinarith))
  have h1 : |flatPullback φ ζ g x' - flatPullback φ ζ g y'| ≤
      M * |g X - g Y| + m * |g Y| := by
    have : flatPullback φ ζ g x' - flatPullback φ ζ g y' =
        ζ X * (g X - g Y) + (ζ X - ζ Y) * g Y := by
      simp only [flatPullback, hX, hY]; ring
    rw [this]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hM X) (abs_nonneg _)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_right hζ (abs_nonneg _)
  have h2 : |flatPullback φ ζ g x' - flatPullback φ ζ g y'| ^ p ≤
      2 ^ (p - 1) * (M ^ p * |g X - g Y| ^ p + m ^ p * |g Y| ^ p) := by
    refine (Real.rpow_le_rpow (abs_nonneg _) h1 hp0.le).trans ?_
    refine (real_add_rpow_le (mul_nonneg hM0 (abs_nonneg _)) (mul_nonneg hmnn (abs_nonneg _))
      hp.le).trans_eq ?_
    rw [Real.mul_rpow hM0 (abs_nonneg _), Real.mul_rpow hmnn (abs_nonneg _)]
  have h3 := div_le_div_of_nonneg_right h2 hsq
  have hA : |g X - g Y| ^ p / s ^ q ≤ s0 ^ q * (|g X - g Y| ^ p / d ^ q) :=
    div_rpow_le_of_le_mul (Real.rpow_nonneg (abs_nonneg _) _) hq hs hsd hdle
  have hR : 0 ≤ m ^ p / s ^ q := div_nonneg (Real.rpow_nonneg hmnn _) hsq
  have h2p : 0 ≤ (2 : ℝ) ^ (p - 1) := Real.rpow_nonneg (by norm_num) _
  have hMp : 0 ≤ M ^ p := Real.rpow_nonneg hM0 _
  have e0 : 2 ^ (p - 1) * (M ^ p * |g X - g Y| ^ p + m ^ p * |g Y| ^ p) / s ^ q =
      2 ^ (p - 1) * (M ^ p * (|g X - g Y| ^ p / s ^ q) + |g Y| ^ p * (m ^ p / s ^ q)) := by
    ring
  have e1 : 2 ^ (p - 1) * (M ^ p * (|g X - g Y| ^ p / s ^ q)) ≤
      2 ^ (p - 1) * M ^ p * s0 ^ q * (|g X - g Y| ^ p / d ^ q) := by
    calc 2 ^ (p - 1) * (M ^ p * (|g X - g Y| ^ p / s ^ q))
        ≤ 2 ^ (p - 1) * (M ^ p * (s0 ^ q * (|g X - g Y| ^ p / d ^ q))) := by gcongr
      _ = _ := by ring
  have hgY : 0 ≤ |g Y| ^ p := Real.rpow_nonneg (abs_nonneg _) _
  have hgX : 0 ≤ |g X| ^ p := Real.rpow_nonneg (abs_nonneg _) _
  have e2 : 2 ^ (p - 1) * (|g Y| ^ p * (m ^ p / s ^ q)) ≤
      (2 ^ (p - 1) + M ^ p) * ((|g X| ^ p + |g Y| ^ p) * (m ^ p / s ^ q)) := by
    calc 2 ^ (p - 1) * (|g Y| ^ p * (m ^ p / s ^ q))
        ≤ (2 ^ (p - 1) + M ^ p) * (|g Y| ^ p * (m ^ p / s ^ q)) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hMp) (mul_nonneg hgY hR)
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left hgX) hR) (add_nonneg h2p hMp)
  rw [e0] at h3
  have e3 : 2 ^ (p - 1) * (M ^ p * (|g X - g Y| ^ p / s ^ q) + |g Y| ^ p * (m ^ p / s ^ q)) =
      2 ^ (p - 1) * (M ^ p * (|g X - g Y| ^ p / s ^ q)) +
        2 ^ (p - 1) * (|g Y| ^ p * (m ^ p / s ^ q)) := by ring
  rw [e3] at h3
  linarith

end GraphChart

end PDE.TraceLane
