module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Field.GeomSum

/-!
# The real iteration in the Bombieri-Giusti lemma

If `h ≥ 0` is bounded on `[δ, 1]` and satisfies `h σ' ≤ ϑ h σ + K (σ - σ')⁻ᵝ` with `ϑ < 1`,
then `h δ` is bounded by an explicit constant depending on `δ, K, ϑ, β` only.
-/

@[expose] public section

namespace PDE.Bombieri

open Finset Filter

/-- The `k`-fold iteration along the radii `σ i = 1 - (1 - δ) τ ^ i`. -/
theorem iteration_partial (h : ℝ → ℝ) (δ K ϑ β τ : ℝ) (hδ : δ < 1) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hϑ : 0 ≤ ϑ) (_hβ : 0 < β)
    (hrec : ∀ σ' σ : ℝ, δ ≤ σ' → σ' < σ → σ ≤ 1 → h σ' ≤ ϑ * h σ + K / (σ - σ') ^ β)
    (_hK : 0 ≤ K) (_hh : ∀ σ, δ ≤ σ → σ ≤ 1 → 0 ≤ h σ) (k : ℕ) :
    h δ ≤ ϑ ^ k * h (1 - (1 - δ) * τ ^ k) +
      K / ((1 - δ) * (1 - τ)) ^ β * ∑ i ∈ range k, (ϑ / τ ^ β) ^ i := by
  have hd : 0 < 1 - δ := by linarith
  have hτ' : 0 < 1 - τ := by linarith
  have hσ : ∀ i : ℕ, δ ≤ 1 - (1 - δ) * τ ^ i ∧ 1 - (1 - δ) * τ ^ i ≤ 1 := by
    intro i
    have h1 : τ ^ i ≤ 1 := pow_le_one₀ hτ0.le hτ1.le
    have h2 : 0 < τ ^ i := pow_pos hτ0 i
    constructor <;> nlinarith
  have hgap : ∀ i : ℕ, (1 - (1 - δ) * τ ^ (i + 1)) - (1 - (1 - δ) * τ ^ i) =
      (1 - δ) * (1 - τ) * τ ^ i := by
    intro i; rw [pow_succ]; ring
  induction k with
  | zero => simp
  | succ k ih =>
    have hpos : 0 < (1 - δ) * (1 - τ) * τ ^ k := by positivity
    have hlt : 1 - (1 - δ) * τ ^ k < 1 - (1 - δ) * τ ^ (k + 1) := by
      have := hgap k; linarith
    have hstep := hrec _ _ (hσ k).1 hlt (hσ (k + 1)).2
    rw [hgap k] at hstep
    have hpow : ((1 - δ) * (1 - τ) * τ ^ k) ^ β =
        ((1 - δ) * (1 - τ)) ^ β * (τ ^ β) ^ k := by
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
        ← Real.rpow_natCast (τ ^ β), ← Real.rpow_mul hτ0.le, ← Real.rpow_mul hτ0.le]
      ring_nf
    rw [hpow] at hstep
    have hterm : K / (((1 - δ) * (1 - τ)) ^ β * (τ ^ β) ^ k) =
        K / ((1 - δ) * (1 - τ)) ^ β * (1 / τ ^ β) ^ k := by
      rw [one_div, inv_pow, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
      ring
    rw [hterm] at hstep
    have hsum : ∑ i ∈ range (k + 1), (ϑ / τ ^ β) ^ i =
        ∑ i ∈ range k, (ϑ / τ ^ β) ^ i + (ϑ / τ ^ β) ^ k := Finset.sum_range_succ _ _
    have hpk : 0 ≤ ϑ ^ k := pow_nonneg hϑ k
    have hmul : ϑ ^ k * (K / ((1 - δ) * (1 - τ)) ^ β * (1 / τ ^ β) ^ k) =
        K / ((1 - δ) * (1 - τ)) ^ β * (ϑ / τ ^ β) ^ k := by
      rw [div_pow ϑ, one_div, inv_pow]; ring
    calc h δ ≤ ϑ ^ k * h (1 - (1 - δ) * τ ^ k) +
          K / ((1 - δ) * (1 - τ)) ^ β * ∑ i ∈ range k, (ϑ / τ ^ β) ^ i := ih
      _ ≤ ϑ ^ k * (ϑ * h (1 - (1 - δ) * τ ^ (k + 1)) +
            K / ((1 - δ) * (1 - τ)) ^ β * (1 / τ ^ β) ^ k) +
          K / ((1 - δ) * (1 - τ)) ^ β * ∑ i ∈ range k, (ϑ / τ ^ β) ^ i := by
        gcongr
      _ = ϑ ^ (k + 1) * h (1 - (1 - δ) * τ ^ (k + 1)) +
          K / ((1 - δ) * (1 - τ)) ^ β * ∑ i ∈ range (k + 1), (ϑ / τ ^ β) ^ i := by
        rw [hsum, mul_add, mul_add, hmul, pow_succ]; ring

/-- The limiting iteration bound. -/
theorem iteration_bound (h : ℝ → ℝ) (δ K ϑ β τ H : ℝ) (hδ : δ < 1) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hϑ0 : 0 ≤ ϑ) (hϑ1 : ϑ < 1) (hβ : 0 < β) (hrτ : ϑ < τ ^ β)
    (hrec : ∀ σ' σ : ℝ, δ ≤ σ' → σ' < σ → σ ≤ 1 → h σ' ≤ ϑ * h σ + K / (σ - σ') ^ β)
    (hK : 0 ≤ K) (hh : ∀ σ, δ ≤ σ → σ ≤ 1 → 0 ≤ h σ)
    (hH : ∀ σ, δ ≤ σ → σ ≤ 1 → h σ ≤ H) :
    h δ ≤ K / ((1 - δ) * (1 - τ)) ^ β / (1 - ϑ / τ ^ β) := by
  have hτβ : 0 < τ ^ β := Real.rpow_pos_of_pos hτ0 β
  have hr1 : ϑ / τ ^ β < 1 := (div_lt_one hτβ).mpr hrτ
  have hr0 : 0 ≤ ϑ / τ ^ β := div_nonneg hϑ0 hτβ.le
  have hd : 0 < 1 - δ := by linarith
  have hτ' : 0 < 1 - τ := by linarith
  set B := K / ((1 - δ) * (1 - τ)) ^ β / (1 - ϑ / τ ^ β) with hB
  have hbound : ∀ k : ℕ, h δ ≤ ϑ ^ k * H + B := by
    intro k
    have hp := iteration_partial h δ K ϑ β τ hδ hτ0 hτ1 hϑ0 hβ hrec hK hh k
    have hg : ∑ i ∈ range k, (ϑ / τ ^ β) ^ i ≤ 1 / (1 - ϑ / τ ^ β) := by
      have hpos : 0 < 1 - ϑ / τ ^ β := by linarith
      rw [le_div_iff₀ hpos, mul_comm, mul_neg_geom_sum]
      have : 0 ≤ (ϑ / τ ^ β) ^ k := pow_nonneg hr0 k
      linarith
    have hσ1 : h (1 - (1 - δ) * τ ^ k) ≤ H := by
      have h1 : τ ^ k ≤ 1 := pow_le_one₀ hτ0.le hτ1.le
      have h2 : 0 < τ ^ k := pow_pos hτ0 k
      exact hH _ (by nlinarith) (by nlinarith)
    have hC : 0 ≤ K / ((1 - δ) * (1 - τ)) ^ β :=
      div_nonneg hK (Real.rpow_nonneg (by positivity) _)
    calc h δ ≤ _ := hp
      _ ≤ ϑ ^ k * H + K / ((1 - δ) * (1 - τ)) ^ β * (1 / (1 - ϑ / τ ^ β)) := by
        gcongr
      _ = ϑ ^ k * H + B := by rw [hB]; ring
  have hlim : Tendsto (fun k : ℕ => ϑ ^ k * H + B) atTop (nhds (0 * H + B)) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hϑ0 hϑ1).mul_const H).add_const B
  have := ge_of_tendsto hlim (Eventually.of_forall hbound)
  simpa using this

end PDE.Bombieri
