module

public import PDEFoundation

/-!
# Abstract Harnack chain (Nash-Aronson lower bound)

A purely order-theoretic iteration: if consecutive slice estimates
`essSup_{B(p_k,r)} w(τ_k) ≤ H · essInf_{B(p_{k+1},r)} w(τ_{k+1})` hold for `k < N`, a lower bound
on the first `essSup` propagates with the factor `H⁻¹` per step.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Parabolic.NashLower

/-- Restricted volume on a Euclidean ball of positive radius is nonzero. -/
theorem neZero_restrict_euclideanBall {d : ℕ} (z : Vec d) {r : ℝ} (hr : 0 < r) :
    NeZero ((volume : Measure (Vec d)).restrict (euclideanBall z r)) := by
  refine ⟨fun h => ?_⟩
  have h1 := volume_euclideanBall_pos z hr
  have h2 : ((volume : Measure (Vec d)).restrict (euclideanBall z r)) univ = 0 := by rw [h]; rfl
  rw [Measure.restrict_apply_univ] at h2
  exact h1.ne' h2

/-- On a nonzero measure the essential infimum is at most the essential supremum. -/
theorem essInf_le_essSup_of_neZero {α : Type*} [MeasurableSpace α] {μ : Measure α} [NeZero μ]
    (f : α → ℝ≥0∞) : essInf f μ ≤ essSup f μ := by
  have h1 : ∀ᵐ y ∂μ, essInf f μ ≤ f y := ae_essInf_le
  have h2 : ∀ᵐ y ∂μ, f y ≤ essSup f μ := ae_le_essSup
  obtain ⟨y, hy1, hy2⟩ := (h1.and h2).exists
  exact hy1.trans hy2

theorem ofReal_div_le_of_ofReal_le_mul {H : ℝ} (hH : 0 < H) {c : ℝ} {I : ℝ≥0∞}
    (h : ENNReal.ofReal c ≤ ENNReal.ofReal H * I) : ENNReal.ofReal (c / H) ≤ I := by
  rw [ENNReal.ofReal_div_of_pos hH]
  refine ENNReal.div_le_of_le_mul ?_
  rwa [mul_comm]

/-- The Harnack chain: a lower bound for `essSup` at step `0` gives `K / H^(k+1)` lower bounds
for `essInf` at steps `k + 1 ≤ N`. -/
theorem chain_lower {d : ℕ} (w : Vec d × ℝ → ℝ) {H : ℝ} (hH : 0 < H) (N : ℕ) (τ : ℕ → ℝ)
    (p : ℕ → Vec d) {r : ℝ} (hr : 0 < r) (K : ℝ)
    (hstep : ∀ k, k < N →
      essSup (fun x => ENNReal.ofReal (w (x, τ k))) (volume.restrict (euclideanBall (p k) r)) ≤
        ENNReal.ofReal H *
          essInf (fun x => ENNReal.ofReal (w (x, τ (k + 1))))
            (volume.restrict (euclideanBall (p (k + 1)) r)))
    (h0 : ENNReal.ofReal K ≤
      essSup (fun x => ENNReal.ofReal (w (x, τ 0))) (volume.restrict (euclideanBall (p 0) r))) :
    ∀ k, k < N → ENNReal.ofReal (K / H ^ (k + 1)) ≤
      essInf (fun x => ENNReal.ofReal (w (x, τ (k + 1))))
        (volume.restrict (euclideanBall (p (k + 1)) r)) := by
  have hsup : ∀ k, k < N → ENNReal.ofReal (K / H ^ k) ≤
      essSup (fun x => ENNReal.ofReal (w (x, τ k))) (volume.restrict (euclideanBall (p k) r)) := by
    intro k
    induction k with
    | zero => intro _; simpa using h0
    | succ k ih =>
      intro hk
      have hk' : k < N := Nat.lt_of_succ_lt hk
      have := neZero_restrict_euclideanBall (p (k + 1)) hr
      have h1 := (ih hk').trans (hstep k hk')
      have h2 := ofReal_div_le_of_ofReal_le_mul hH h1
      have h3 : K / H ^ k / H = K / H ^ (k + 1) := by rw [div_div, pow_succ]
      rw [h3] at h2
      exact h2.trans (essInf_le_essSup_of_neZero _)
  intro k hk
  have h1 := (hsup k hk).trans (hstep k hk)
  have h2 := ofReal_div_le_of_ofReal_le_mul hH h1
  have h3 : K / H ^ k / H = K / H ^ (k + 1) := by rw [div_div, pow_succ]
  rwa [h3] at h2

end PDE.Parabolic.NashLower
