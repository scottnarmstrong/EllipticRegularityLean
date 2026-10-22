module

public import PDEFoundation.Geometry.EuclideanBall.Basic
public import PDEFoundation.Sobolev.ClassicalGradient
public import PDEFoundation.Sobolev.ClassicalLaplacian
import PDEFoundation.Monotonicity.Poon.BernsteinBound
import PDEFoundation.Monotonicity.Poon.BernsteinBridge
import PDEFoundation.Monotonicity.Poon.MaxPrinciple

/-!
# Bernstein gradient estimate for the heat equation

For `w` caloric and `C^∞` near the cylinder `[t₀, t₀ + ρ²] × B̄_ρ(x₀)`,
`|∇w(t₀ + ρ², x₀)| ≤ (5 + d) ρ⁻¹ sup |w|`.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace PDE

noncomputable section

variable {d : ℕ}

/-- **Bernstein gradient estimate.** -/
theorem bernstein_gradient_estimate (w : ℝ → Vec d → ℝ) {Ω : Set (ℝ × Vec d)} (hΩ : IsOpen Ω)
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec d => w p.1 p.2) Ω)
    (hheat : ∀ t : ℝ, ∀ x : Vec d, (t, x) ∈ Ω →
      deriv (fun τ : ℝ => w τ x) t = euclideanCoordLaplacian (w t) x)
    {x₀ : Vec d} {ρ t₀ : ℝ} (hρ : 0 < ρ)
    (hcyl : Icc t₀ (t₀ + ρ ^ 2) ×ˢ euclideanClosedBall x₀ ρ ⊆ Ω) {M : ℝ}
    (hM : ∀ s ∈ Icc t₀ (t₀ + ρ ^ 2), ∀ y ∈ euclideanClosedBall x₀ ρ, |w s y| ≤ M) :
    vecEuclideanNorm (classicalGradient (w (t₀ + ρ ^ 2)) x₀) ≤ (5 + (d : ℝ)) / ρ * M := by
  classical
  set F : ℝ × Vec d → ℝ := fun p => w p.1 p.2 with hF
  have hFs : JSm Ω F := hw
  have hρ2 : 0 < ρ ^ 2 := pow_pos hρ 2
  set t₁ : ℝ := t₀ + ρ ^ 2 with ht₁
  have ht01 : t₀ ≤ t₁ := by linarith
  have hheatJ : EqOn (jEt F) (jLap F) Ω := by
    rintro ⟨t, x⟩ hp
    have h1 : jEt F (t, x) = deriv (fun τ : ℝ => F (τ, x)) t :=
      (deriv_slice_time (hFs.differentiableAt hΩ hp)).symm
    have h2 : jLap F (t, x) = euclideanCoordLaplacian (fun y : Vec d => F (t, y)) x :=
      (euclideanCoordLaplacian_slice hΩ hFs hp).symm
    rw [h1, h2]
    exact hheat t x hp
  set G : ℝ × Vec d → ℝ := jBernstein F x₀ t₀ ρ with hG
  have hGs : JSm Ω G := hFs.jBernstein hΩ x₀ t₀ ρ
  have hdist : ∀ x : Vec d, jDistSq x₀ (0, x) = euclideanSqDist x x₀ := by
    intro x
    unfold jDistSq euclideanSqDist
    rw [vecNormSq_eq_sum_sq]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [sq]
  have hdist' : ∀ p : ℝ × Vec d, jDistSq x₀ p = euclideanSqDist p.2 x₀ := by
    intro p
    have : jDistSq x₀ p = jDistSq x₀ (0, p.2) := rfl
    rw [this, hdist]
  obtain ⟨t', ht', x', hx', hbd, hmax⟩ := parabolic_weak_max_principle
    (fun t x => G (t, x)) hΩ (hGs.of_le (WithTop.coe_le_coe.2 (show (2 : ℕ∞) ≤ ⊤ from le_top))) ht01 hcyl (fun t ht x hx => by
      have hp : (t, x) ∈ Ω := hcyl ⟨ht, hx⟩
      have h1 := deriv_slice_time (g := G) (hGs.differentiableAt hΩ hp)
      have h2 := euclideanCoordLaplacian_slice hΩ hGs hp
      change deriv (fun τ : ℝ => G (τ, x)) t -
        euclideanCoordLaplacian (fun y : Vec d => G (t, y)) x ≤ 0
      rw [h2, h1]
      exact jBernstein_sub_nonpos hΩ hFs hheatJ hρ hp ht.1 (by linarith [ht.2])
        (by rw [hdist']; exact hx))
  -- bound at the maximum point
  have hFsq : ∀ s ∈ Icc t₀ t₁, ∀ y ∈ euclideanClosedBall x₀ ρ, F (s, y) * F (s, y) ≤ M * M := by
    intro s hs y hy
    have h := hM s hs y hy
    have h0 : 0 ≤ M := (abs_nonneg _).trans h
    calc F (s, y) * F (s, y) = |F (s, y)| * |F (s, y)| := (abs_mul_abs_self _).symm
      _ ≤ M * M := mul_le_mul h h (abs_nonneg _) h0
  have hlam : 0 ≤ (25 + 4 * (d : ℝ)) / 2 := by positivity
  have hGmax : G (t', x') ≤ (25 + 4 * (d : ℝ)) / 2 * (M * M) := by
    have hzero : jCutA x₀ t₀ (ρ ^ 2)⁻¹ (t', x') = 0 := by
      rcases hbd with h | h
      · simp [jCutA, h]
      · have hs : euclideanSqDist x' x₀ = ρ ^ 2 := h
        have hD : jDistSq x₀ (t', x') = ρ ^ 2 := by rw [hdist']; exact hs
        have hZ : jCutZ x₀ (ρ ^ 2)⁻¹ (t', x') = 0 := by
          simp only [jCutZ, hD]
          rw [inv_mul_cancel₀ hρ2.ne']; ring
        simp [jCutA, hZ]
    have : G (t', x') = (25 + 4 * (d : ℝ)) / 2 * (F (t', x') * F (t', x')) := by
      simp [hG, jBernstein, hzero]
    rw [this]
    exact mul_le_mul_of_nonneg_left (hFsq t' ht' x' hx') hlam
  have hx₀mem : x₀ ∈ euclideanClosedBall x₀ ρ := by
    simp [euclideanClosedBall]; positivity
  have ht₁mem : t₁ ∈ Icc t₀ t₁ := ⟨ht01, le_rfl⟩
  have htop := hmax t₁ ht₁mem x₀ hx₀mem
  have hGtop : ρ ^ 2 * jGradSq F (t₁, x₀) ≤ G (t₁, x₀) := by
    have hZ : jCutZ x₀ (ρ ^ 2)⁻¹ (t₁, x₀) = 1 := by
      have : jDistSq x₀ (t₁, x₀) = 0 := by
        rw [hdist']; simp
      simp [jCutZ, this]
    have hA : jCutA x₀ t₀ (ρ ^ 2)⁻¹ (t₁, x₀) = ρ ^ 2 := by
      simp only [jCutA, hZ]
      rw [ht₁]; ring
    have : G (t₁, x₀) = ρ ^ 2 * jGradSq F (t₁, x₀) +
        (25 + 4 * (d : ℝ)) / 2 * (F (t₁, x₀) * F (t₁, x₀)) := by
      simp only [hG, jBernstein, hA]
    rw [this]
    have : 0 ≤ (25 + 4 * (d : ℝ)) / 2 * (F (t₁, x₀) * F (t₁, x₀)) :=
      mul_nonneg hlam (mul_self_nonneg _)
    linarith
  have hP : ρ ^ 2 * jGradSq F (t₁, x₀) ≤ (25 + 4 * (d : ℝ)) / 2 * (M * M) :=
    hGtop.trans (htop.trans hGmax)
  -- identify the gradient
  have hgrad : vecNormSq (classicalGradient (w t₁) x₀) = jGradSq F (t₁, x₀) := by
    have hp : (t₁, x₀) ∈ Ω := hcyl ⟨ht₁mem, hx₀mem⟩
    rw [vecNormSq_eq_sum_sq]
    unfold jGradSq
    refine Finset.sum_congr rfl fun i _ => ?_
    have := fderiv_slice_apply (g := F) (hFs.differentiableAt hΩ hp) (basisVec i)
    simp only [classicalGradient_apply, sq]
    change fderiv ℝ (fun y : Vec d => F (t₁, y)) x₀ (basisVec i) *
      fderiv ℝ (fun y : Vec d => F (t₁, y)) x₀ (basisVec i) = _
    rw [this]
    rfl
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM t₀ ⟨le_rfl, ht01⟩ x₀ hx₀mem)
  unfold vecEuclideanNorm
  rw [hgrad, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have hlam2 : (25 + 4 * (d : ℝ)) / 2 ≤ (5 + (d : ℝ)) ^ 2 := by
    nlinarith [sq_nonneg (d : ℝ), (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have h1 : ρ ^ 2 * jGradSq F (t₁, x₀) ≤ ρ ^ 2 * ((5 + (d : ℝ)) / ρ * M) ^ 2 := by
    have : ρ ^ 2 * ((5 + (d : ℝ)) / ρ * M) ^ 2 = (5 + (d : ℝ)) ^ 2 * (M * M) := by
      field_simp
    rw [this]
    exact hP.trans (mul_le_mul_of_nonneg_right hlam2 (mul_self_nonneg M))
  exact le_of_mul_le_mul_left h1 hρ2

end

end PDE
