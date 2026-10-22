module

public import PDEFoundation.Monotonicity.Poon.DifferentiateSetup

/-!
# Differentiability of Poon's `H`

For `s` with `0 < s < T`, `8 A s < 1`, the function `poonH u` is differentiable at `s`, with
derivative the integral of `∂ₛ (u(-s,x)² Φ(s,x))`, written with `∂ₛ u(-s,x) = -Δu(-s,x)`
(heat equation) and `∂ₛ Φ = (-d/(2s) + |x|²/(4s²)) Φ`.
-/

@[expose] public section

open Set Filter MeasureTheory

namespace PDE

noncomputable section

variable {d : ℕ} {u : ℝ → Vec d → ℝ} {T : ℝ}

theorem sq_const_mul_exp (C' A' q : ℝ) :
    (C' * Real.exp (A' * q)) ^ 2 = C' ^ 2 * Real.exp (2 * A' * q) := by
  rw [mul_pow, ← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

theorem hasDerivAt_slice_neg
    (heat : ∀ t ∈ Ioo (-T) 0, ∀ x : Vec d,
      HasDerivAt (fun τ : ℝ => u τ x) (euclideanCoordLaplacian (u t) x) t)
    {r : ℝ} (hr : -r ∈ Ioo (-T) 0) (x : Vec d) :
    HasDerivAt (fun ρ : ℝ => u (-ρ) x) (-(euclideanCoordLaplacian (u (-r)) x)) r := by
  have h := (heat (-r) hr x).scomp r (hasDerivAt_neg r)
  convert h using 1
  · rfl
  · simp

/-- **`H` is differentiable on the admissible interval**, with explicit derivative integrand. -/
theorem poonH_hasDerivAt
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (jointOf u) (Ioo (-T) 0 ×ˢ (univ : Set (Vec d))))
    (heat : ∀ t ∈ Ioo (-T) 0, ∀ x : Vec d,
      HasDerivAt (fun τ : ℝ => u τ x) (euclideanCoordLaplacian (u t) x) t)
    {A C : ℝ}
    (hbound : ∀ t ∈ Ioo (-T) 0, ∀ x : Vec d, |u t x| ≤ C * Real.exp (A * vecNormSq x))
    {s : ℝ} (hs0 : 0 < s) (hsT : s < T) (hAs : 8 * A * s < 1) :
    Integrable (fun x : Vec d => u (-s) x ^ 2 * heatKernel d s x) volume ∧
    Integrable (fun x : Vec d =>
      (2 * u (-s) x * (-(euclideanCoordLaplacian (u (-s)) x)) +
        u (-s) x ^ 2 * (-(d : ℝ) / (2 * s) + vecNormSq x / (4 * s ^ 2))) * heatKernel d s x)
      volume ∧
    HasDerivAt (poonH u)
      (∫ x : Vec d,
        (2 * u (-s) x * (-(euclideanCoordLaplacian (u (-s)) x)) +
          u (-s) x ^ 2 * (-(d : ℝ) / (2 * s) + vecNormSq x / (4 * s ^ 2))) * heatKernel d s x) s := by
  obtain ⟨a, b, A', C', ha, has, hsb, hbT, hG, hC', hB⟩ :=
    exists_poon_domination hsmooth heat hbound hs0 hsT hAs
  have hmem : ∀ r ∈ Ioo a b, -r ∈ Ioo (-T) 0 := fun r hr =>
    ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have hmem' : ∀ r ∈ Icc a b, -r ∈ Ioo (-T) 0 := fun r hr =>
    ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have key := hasDerivAt_integral_heatKernel_param (d := d)
    (P := fun r x => u (-r) x ^ 2)
    (P' := fun r x => 2 * u (-r) x * (-(euclideanCoordLaplacian (u (-r)) x)))
    (a := a) (b := b) (s := s) (A' := A') ha ⟨has, hsb⟩ hG
    (fun r hr => (continuous_slice_of_smooth hsmooth (hmem r hr)).pow 2)
    (by
      have hs' : -s ∈ Ioo (-T) 0 := hmem s ⟨has, hsb⟩
      exact (continuous_slice_of_smooth hsmooth hs').const_mul 2 |>.mul
        (continuous_laplacian_slice hsmooth hs').neg)
    (fun r hr x => by
      have h1 := hasDerivAt_slice_neg heat (hmem r hr) x
      have h2 := h1.pow 2
      convert h2 using 1
      simp)
    ⟨2 * C' ^ 2, by positivity, fun r hr x => by
      obtain ⟨b1, -, b3, -⟩ := hB r hr x
      have hE : 0 ≤ C' * Real.exp (A' * vecNormSq x) := by positivity
      have e := sq_const_mul_exp C' A' (vecNormSq x)
      have b1' : |u (-r) x| ≤ C' * Real.exp (A' * vecNormSq x) := b1
      constructor
      · rw [abs_of_nonneg (sq_nonneg _)]
        have : u (-r) x ^ 2 ≤ (C' * Real.exp (A' * vecNormSq x)) ^ 2 := by
          calc u (-r) x ^ 2 = |u (-r) x| ^ 2 := (sq_abs _).symm
            _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) b1' 2
        rw [e] at this
        nlinarith [Real.exp_pos (2 * A' * vecNormSq x), sq_nonneg C']
      · rw [abs_mul, abs_mul, abs_neg]
        have : |u (-r) x| * |euclideanCoordLaplacian (u (-r)) x| ≤
            (C' * Real.exp (A' * vecNormSq x)) ^ 2 := by
          rw [sq]; exact mul_le_mul b1' b3 (abs_nonneg _) hE
        rw [e] at this
        have h2 : |(2 : ℝ)| = 2 := abs_of_pos two_pos
        rw [h2]
        nlinarith⟩
  exact key
