module

public import PDEFoundation.Monotonicity.Poon.DifferentiateH

/-!
# Differentiability of Poon's `D`

For `s` with `0 < s < T`, `8 A s < 1`, the function `poonD u` is differentiable at `s`, with
derivative the integral of `∂ₛ (|∇u(-s,x)|² Φ(s,x))`, written with
`∂ₛ ∇u(-s,x) = -∇Δu(-s,x)` (heat equation, `∇ ∂ₜ u = ∇ Δ u`) and the `∂ₛ Φ` formula.
-/

@[expose] public section

open Set Filter MeasureTheory

namespace PDE

noncomputable section

variable {d : ℕ} {u : ℝ → Vec d → ℝ} {T : ℝ}

theorem hasDerivAt_gradient_slice_neg
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (jointOf u) (Ioo (-T) 0 ×ˢ (univ : Set (Vec d))))
    (heat : ∀ t ∈ Ioo (-T) 0, ∀ x : Vec d,
      HasDerivAt (fun τ : ℝ => u τ x) (euclideanCoordLaplacian (u t) x) t)
    {r : ℝ} (hr : -r ∈ Ioo (-T) 0) (x : Vec d) (i : Fin d) :
    HasDerivAt (fun ρ : ℝ => classicalGradient (u (-ρ)) x i)
      (-(classicalGradient (euclideanCoordLaplacian (u (-r))) x i)) r := by
  have hΩ := isOpen_slab (d := d) (-T) 0
  have hsm : JSm (slab d (-T) 0) (jointOf u) := hsmooth
  have hp : (-r, x) ∈ slab d (-T) 0 := ⟨hr, mem_univ x⟩
  have h0 : HasDerivAt (fun τ : ℝ => jEx i (jointOf u) (τ, x))
      (jEt (jEx i (jointOf u)) (-r, x)) (-r) :=
    hasDerivAt_slice_time ((hsm.jEx hΩ i).differentiableAt hΩ hp)
  have h1 := h0.scomp r (hasDerivAt_neg r)
  have h2 : HasDerivAt (fun ρ : ℝ => jEx i (jointOf u) (-ρ, x))
      (-(classicalGradient (euclideanCoordLaplacian (u (-r))) x i)) r := by
    rw [← jEt_jEx_slice hsmooth heat hr x i]
    convert h1 using 1
    · rfl
    · simp
  refine h2.congr_of_eventuallyEq ?_
  have hopen : IsOpen {ρ : ℝ | -ρ ∈ Ioo (-T) 0} := isOpen_Ioo.preimage continuous_neg
  filter_upwards [hopen.mem_nhds hr] with ρ hρ
  rw [← euclideanCoordDeriv_eq_classicalGradient_apply,
    coordDeriv_slice_eq hsm hρ i]

/-- **`D` is differentiable on the admissible interval**, with explicit derivative integrand. -/
theorem poonD_hasDerivAt
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (jointOf u) (Ioo (-T) 0 ×ˢ (univ : Set (Vec d))))
    (heat : ∀ t ∈ Ioo (-T) 0, ∀ x : Vec d,
      HasDerivAt (fun τ : ℝ => u τ x) (euclideanCoordLaplacian (u t) x) t)
    {A C : ℝ}
    (hbound : ∀ t ∈ Ioo (-T) 0, ∀ x : Vec d, |u t x| ≤ C * Real.exp (A * vecNormSq x))
    {s : ℝ} (hs0 : 0 < s) (hsT : s < T) (hAs : 8 * A * s < 1) :
    Integrable (fun x : Vec d => vecNormSq (classicalGradient (u (-s)) x) * heatKernel d s x)
      volume ∧
    Integrable (fun x : Vec d =>
      (-2 * vecDot (classicalGradient (u (-s)) x)
          (classicalGradient (euclideanCoordLaplacian (u (-s))) x) +
        vecNormSq (classicalGradient (u (-s)) x) *
          (-(d : ℝ) / (2 * s) + vecNormSq x / (4 * s ^ 2))) * heatKernel d s x) volume ∧
    HasDerivAt (poonD u)
      (∫ x : Vec d,
        (-2 * vecDot (classicalGradient (u (-s)) x)
            (classicalGradient (euclideanCoordLaplacian (u (-s))) x) +
          vecNormSq (classicalGradient (u (-s)) x) *
            (-(d : ℝ) / (2 * s) + vecNormSq x / (4 * s ^ 2))) * heatKernel d s x) s := by
  obtain ⟨a, b, A', C', ha, has, hsb, hbT, hG, hC', hB⟩ :=
    exists_poon_domination hsmooth heat hbound hs0 hsT hAs
  have hmem : ∀ r ∈ Ioo a b, -r ∈ Ioo (-T) 0 := fun r hr =>
    ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have hsm : JSm (slab d (-T) 0) (jointOf u) := hsmooth
  have hcg : ∀ t ∈ Ioo (-T) 0, ∀ i : Fin d, Continuous (fun y => classicalGradient (u t) y i) :=
    fun t ht i => by
      have : (fun y => classicalGradient (u t) y i) = fun y => jEx i (jointOf u) (t, y) :=
        funext fun y => by
          rw [← euclideanCoordDeriv_eq_classicalGradient_apply, coordDeriv_slice_eq hsm ht i]
      rw [this]
      exact continuous_jEx_slice hsm ht i
  have hcL : ∀ t ∈ Ioo (-T) 0, ∀ i : Fin d,
      Continuous (fun y => classicalGradient (euclideanCoordLaplacian (u t)) y i) :=
    fun t ht i => by
      have hdeq : (fun y : Vec d => jEt (jointOf u) (t, y)) = euclideanCoordLaplacian (u t) := by
        rw [← deriv_slice_eq_laplacian heat ht, ← deriv_slice_eq hsm ht]
      have : (fun y => classicalGradient (euclideanCoordLaplacian (u t)) y i) =
          fun y => jEx i (jEt (jointOf u)) (t, y) :=
        funext fun y => by
          rw [← euclideanCoordDeriv_eq_classicalGradient_apply, ← hdeq,
            euclideanCoordDeriv_slice (isOpen_slab (d := d) (-T) 0) (JSm.jEt (isOpen_slab (d := d) (-T) 0) hsm) i
              (⟨ht, mem_univ y⟩ : (t, y) ∈ slab d (-T) 0)]
      rw [this]
      exact continuous_jEx_slice (JSm.jEt (isOpen_slab (d := d) (-T) 0) hsm) ht i
  have hcv : Continuous (fun x : Vec d => vecNormSq x) := contDiff_vecNormSq.continuous
  have key := hasDerivAt_integral_heatKernel_param (d := d)
    (P := fun r x => vecNormSq (classicalGradient (u (-r)) x))
    (P' := fun r x => -2 * vecDot (classicalGradient (u (-r)) x)
      (classicalGradient (euclideanCoordLaplacian (u (-r))) x))
    (a := a) (b := b) (s := s) (A' := A') ha ⟨has, hsb⟩ hG
    (fun r hr => by
      simp only [vecNormSq_eq_sum_sq]
      exact continuous_finsetSum _ fun i _ => (hcg _ (hmem r hr) i).pow 2)
    (by
      have hs' : -s ∈ Ioo (-T) 0 := hmem s ⟨has, hsb⟩
      simp only [vecDot]
      exact continuous_const.mul (continuous_finsetSum _ fun i _ =>
        (hcg _ hs' i).mul (hcL _ hs' i)))
    (fun r hr x => by
      have hi := fun i => hasDerivAt_gradient_slice_neg hsmooth heat (hmem r hr) x i
      have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin d)))
        (fun i _ => (hi i).pow 2)
      simp only [vecNormSq_eq_sum_sq]
      convert hsum using 1
      simp only [vecDot, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Nat.cast_ofNat]
      ring)
    ⟨2 * d * C' ^ 2 + C' ^ 2, by positivity, fun r hr x => by
      obtain ⟨b1, b2, b3, b4⟩ := hB r hr x
      have hE : 0 ≤ C' * Real.exp (A' * vecNormSq x) := by positivity
      have e := sq_const_mul_exp C' A' (vecNormSq x)
      have hex := Real.exp_pos (2 * A' * vecNormSq x)
      have hq : 0 ≤ vecNormSq (classicalGradient (u (-r)) x) := by
        rw [vecNormSq_eq_sum_sq]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
      constructor
      · rw [abs_of_nonneg hq, ← vecEuclideanNorm_sq]
        have : vecEuclideanNorm (classicalGradient (u (-r)) x) ^ 2 ≤
            (C' * Real.exp (A' * vecNormSq x)) ^ 2 :=
          pow_le_pow_left₀ (vecEuclideanNorm_nonneg _) b2 2
        rw [e] at this
        nlinarith [sq_nonneg C']
      · have hcomp : ∀ i : Fin d, |classicalGradient (u (-r)) x i| ≤
            C' * Real.exp (A' * vecNormSq x) := fun i =>
          (Real.abs_le_sqrt (sq_apply_le_vecNormSq _ i)).trans b2
        have hcomp' : ∀ i : Fin d, |classicalGradient (euclideanCoordLaplacian (u (-r))) x i| ≤
            C' * Real.exp (A' * vecNormSq x) := fun i =>
          (Real.abs_le_sqrt (sq_apply_le_vecNormSq _ i)).trans b4
        have hdot : |vecDot (classicalGradient (u (-r)) x)
            (classicalGradient (euclideanCoordLaplacian (u (-r))) x)| ≤
            d * (C' * Real.exp (A' * vecNormSq x)) ^ 2 := by
          unfold vecDot
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          calc ∑ i, |classicalGradient (u (-r)) x i *
                classicalGradient (euclideanCoordLaplacian (u (-r))) x i|
              ≤ ∑ _i : Fin d, (C' * Real.exp (A' * vecNormSq x)) ^ 2 := by
                refine Finset.sum_le_sum fun i _ => ?_
                rw [abs_mul, sq]
                exact mul_le_mul (hcomp i) (hcomp' i) (abs_nonneg _) hE
            _ = d * (C' * Real.exp (A' * vecNormSq x)) ^ 2 := by simp
        rw [e] at hdot
        rw [abs_mul]
        have h2 : |(-2 : ℝ)| = 2 := by norm_num
        rw [h2]
        nlinarith [sq_nonneg C', (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]⟩
  exact key
