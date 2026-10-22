module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Chaining local Hölder bounds on convex sets

A finite subdivision of a segment extends a local Hölder estimate to a
global estimate on a set with uniformly bounded diameter.
-/

@[expose] public section

namespace PDE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A local Hölder estimate on a convex set extends to every pair of points
when the set has diameter at most `N * ρ`. -/
theorem abs_sub_le_of_localHolder_on_convex
    {S : Set E} {f : E → ℝ} {D ρ α K : ℝ} {N : ℕ}
    (hconv : Convex ℝ S)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ D)
    (hα0 : 0 < α) (hK : 0 ≤ K)
    (hN : 0 < N) (hD : D ≤ (N : ℝ) * ρ)
    (hlocal : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ ρ →
      |f x - f y| ≤ K * ‖x - y‖ ^ α) :
    ∀ x ∈ S, ∀ y ∈ S,
      |f x - f y| ≤ (N : ℝ) * K * ‖x - y‖ ^ α := by
  intro x hx y hy
  let t (j : ℕ) : ℝ := (j : ℝ) / (N : ℝ)
  let p (j : ℕ) : E := x + t j • (y - x)
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hNge1 : 1 ≤ (N : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hN)
  have hp0 : p 0 = x := by
    simp [p, t]
  have hpN : p N = y := by
    dsimp [p, t]
    rw [div_self hNreal.ne']
    simp
  have hpoint_mem {j : ℕ} (hj : j ≤ N) : p j ∈ S := by
    apply hconv.add_smul_sub_mem hx hy
    dsimp [t]
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) hNreal.le
    · apply (div_le_iff₀ hNreal).2
      simpa using (Nat.cast_le.mpr hj : (j : ℝ) ≤ (N : ℝ))
  have hstep_coeff (j : ℕ) : t (j + 1) - t j = 1 / (N : ℝ) := by
    dsimp [t]
    rw [Nat.cast_add, Nat.cast_one]
    field_simp [hNreal.ne']
    ring
  have hstep_vector (j : ℕ) :
      p j - p (j + 1) = (t j - t (j + 1)) • (y - x) := by
    dsimp [p]
    simp [sub_smul, add_sub_add_left_eq_sub]
  have hstep_norm (j : ℕ) :
      ‖p j - p (j + 1)‖ = ‖x - y‖ / (N : ℝ) := by
    calc
      ‖p j - p (j + 1)‖ =
          ‖(t j - t (j + 1)) • (y - x)‖ := by rw [hstep_vector]
      _ = ‖t j - t (j + 1)‖ * ‖y - x‖ := norm_smul _ _
      _ = (1 / (N : ℝ)) * ‖x - y‖ := by
        rw [show t j - t (j + 1) = -(1 / (N : ℝ)) by linarith [hstep_coeff j],
          Real.norm_eq_abs, abs_neg, abs_of_pos (one_div_pos.mpr hNreal),
          norm_sub_rev]
      _ = ‖x - y‖ / (N : ℝ) := by ring
  have hstep_small {j : ℕ} (hj : j < N) :
      ‖p j - p (j + 1)‖ ≤ ρ := by
    rw [hstep_norm]
    apply (div_le_iff₀ hNreal).2
    calc
      ‖x - y‖ ≤ D := hdiam x hx y hy
      _ ≤ (N : ℝ) * ρ := hD
      _ = ρ * (N : ℝ) := by ring
  have hstep_le_total (j : ℕ) :
      ‖p j - p (j + 1)‖ ≤ ‖x - y‖ := by
    rw [hstep_norm]
    apply (div_le_iff₀ hNreal).2
    calc
      ‖x - y‖ = ‖x - y‖ * 1 := by ring
      _ ≤ ‖x - y‖ * (N : ℝ) :=
        mul_le_mul_of_nonneg_left hNge1 (norm_nonneg _)
  have hterm {j : ℕ} (hj : j < N) :
      dist (f (p j)) (f (p (j + 1))) ≤ K * ‖x - y‖ ^ α := by
    have hjle : j ≤ N := Nat.le_of_lt hj
    have hj1le : j + 1 ≤ N := Nat.succ_le_of_lt hj
    have hloc := hlocal (p j) (hpoint_mem hjle)
      (p (j + 1)) (hpoint_mem hj1le) (hstep_small hj)
    have hpower :
        ‖p j - p (j + 1)‖ ^ α ≤ ‖x - y‖ ^ α :=
      Real.rpow_le_rpow (norm_nonneg _) (hstep_le_total j) hα0.le
    calc
      dist (f (p j)) (f (p (j + 1))) =
          |f (p j) - f (p (j + 1))| := Real.dist_eq _ _
      _ ≤ K * ‖p j - p (j + 1)‖ ^ α := hloc
      _ ≤ K * ‖x - y‖ ^ α := mul_le_mul_of_nonneg_left hpower hK
  have hsum :
      (∑ j ∈ Finset.range N, dist (f (p j)) (f (p (j + 1)))) ≤
        (N : ℝ) * (K * ‖x - y‖ ^ α) := by
    calc
      (∑ j ∈ Finset.range N, dist (f (p j)) (f (p (j + 1)))) ≤
          ∑ j ∈ Finset.range N, K * ‖x - y‖ ^ α :=
        Finset.sum_le_sum fun j hj => hterm (Finset.mem_range.mp hj)
      _ = (N : ℝ) * (K * ‖x - y‖ ^ α) := by simp
  calc
    |f x - f y| = dist (f x) (f y) := by rw [Real.dist_eq]
    _ = dist (f (p 0)) (f (p N)) := by rw [hp0, hpN]
    _ ≤ ∑ j ∈ Finset.range N, dist (f (p j)) (f (p (j + 1))) :=
      dist_le_range_sum_dist (fun j => f (p j)) N
    _ ≤ (N : ℝ) * (K * ‖x - y‖ ^ α) := hsum
    _ = (N : ℝ) * K * ‖x - y‖ ^ α := by ring

end PDE
