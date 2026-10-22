module

public import PDEFoundation.Monotonicity.FriedlandHayman.Basic

/-!
# Friedland--Hayman: limit of the degrees `deg_D((D-2)β)`

If `deg_{n+N}((n+N-2) β) ≤ α` for all `N ≥ 1`, then `β ≤ α`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.FHLane

noncomputable section

theorem ofReal_le_of_degree_bound {β : ℝ} (hβ : 0 ≤ β) {α : ENNReal} {n : ℕ}
    (h : ∀ N : ℕ, 1 ≤ N →
      eigenvalueDegree (n + N) (ENNReal.ofReal ((((n + N : ℕ) : ℝ) - 2) * β)) ≤ α) :
    ENNReal.ofReal β ≤ α := by
  rcases eq_or_ne α ⊤ with rfl | hα
  · exact le_top
  set a := α.toReal with ha_def
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have hαa : α = ENNReal.ofReal a := (ENNReal.ofReal_toReal hα).symm
  rw [hαa] at h ⊢
  rw [ENNReal.ofReal_le_ofReal_iff ha0]
  by_contra hlt
  push Not at hlt
  have hba : 0 < β - a := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (a ^ 2 / (β - a) + 3)
  have hq : 0 ≤ a ^ 2 / (β - a) := div_nonneg (sq_nonneg a) hba.le
  have hN3 : (3 : ℝ) < N := by linarith
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) < N := by linarith
    exact_mod_cast this.le
  set κ : ℝ := ((n + N : ℕ) : ℝ) - 2 with hκ
  have hκN : (N : ℝ) - 2 ≤ κ := by
    rw [hκ]; push_cast; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hκpos : a ^ 2 / (β - a) + 1 < κ := by linarith
  have hκ0 : 0 < κ := by linarith
  have hD : 2 ≤ n + N := by
    have : (2 : ℝ) < ((n + N : ℕ) : ℝ) := by linarith
    exact_mod_cast this.le
  have hcast : (((n + N) - 2 : ℕ) : ℝ) = κ := by
    rw [hκ, Nat.cast_sub hD]; norm_num
  have hl : ENNReal.ofReal (κ * β) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hle := h N hN1
  rw [eigenvalueDegree_eq _ hl, hcast, ENNReal.toReal_ofReal (by positivity)] at hle
  rw [ENNReal.ofReal_le_ofReal_iff ha0] at hle
  have h1 : Real.sqrt ((κ / 2) ^ 2 + κ * β) ≤ a + κ / 2 := by linarith
  rw [Real.sqrt_le_iff] at h1
  obtain ⟨-, h2⟩ := h1
  have h3 : κ * β ≤ a ^ 2 + a * κ := by nlinarith
  have h4 : a ^ 2 < κ * (β - a) := by
    have := (div_lt_iff₀ hba).1 (by linarith : a ^ 2 / (β - a) < κ)
    exact this
  nlinarith

end

end PDE.FHLane
