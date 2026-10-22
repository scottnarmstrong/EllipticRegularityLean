module

public import PDEFoundation.Monotonicity.Poon.AssemblySetup

/-!
# Derivatives of `H`, `D` and the frequency on the admissible interval

With `v = u(-s, ·)`, `w = x·∇v - 2sΔv`:

* `H' = 2 D`,
* `D' = (1/(2s²)) ∫ w² Φ - D/s`,
* `∫ v w Φ = 2 s D`,

and the Cauchy–Schwarz inequality `(∫ v w Φ)² ≤ H ∫ w² Φ` where `H > 0`, which gives
`N' ≥ 0` for `N = s D / H`.
-/

@[expose] public section

open Set MeasureTheory

namespace PDE

noncomputable section

variable {d : ℕ} {u : ℝ → Vec d → ℝ} {T : ℝ}

theorem poonH_eq_lam (u : ℝ → Vec d → ℝ) (s : ℝ) :
    poonH u s = Lam d s (fun x => u (-s) x * u (-s) x) := by
  unfold poonH Lam
  simp only [sq]

theorem poonD_eq_lam (u : ℝ → Vec d → ℝ) (s : ℝ) :
    poonD u s = Lam d s (pQ2 (u (-s))) := rfl

theorem poonH_nonneg {s : ℝ} (hs : 0 < s) : 0 ≤ poonH u s := by
  unfold poonH
  exact integral_nonneg fun x => mul_nonneg (sq_nonneg _) (heatKernel_pos d hs x).le

theorem poonD_nonneg {s : ℝ} (hs : 0 < s) : 0 ≤ poonD u s := by
  unfold poonD
  exact integral_nonneg fun x => mul_nonneg (vecNormSq_nonneg _) (heatKernel_pos d hs x).le

section Admissible

variable
  (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (jointOf u) (Ioo (-T) 0 ×ˢ (univ : Set (Vec d))))
  (heat : ∀ t ∈ Ioo (-T) 0, ∀ x : Vec d,
    HasDerivAt (fun τ : ℝ => u τ x) (euclideanCoordLaplacian (u t) x) t)
  {A C : ℝ}
  (hbound : ∀ t ∈ Ioo (-T) 0, ∀ x : Vec d, |u t x| ≤ C * Real.exp (A * vecNormSq x))
  {s : ℝ} (hs0 : 0 < s) (hsT : s < T) (hAs : 8 * A * s < 1)
include hsmooth heat hbound hs0 hsT hAs

/-- `H' = 2 D`. -/
theorem poonH_hasDerivAt_two_mul :
    HasDerivAt (poonH u) (2 * poonD u s) s := by
  obtain ⟨-, -, hder⟩ := poonH_hasDerivAt hsmooth heat hbound hs0 hsT hAs
  obtain ⟨A', hP⟩ := exists_poonSetup hsmooth heat hbound hs0 hsT hAs
  have := hP.lam_H_identity
  rw [poonD_eq_lam]
  exact this ▸ hder

/-- `D' = (1/(2s²)) ∫ w² Φ - D/s`. -/
theorem poonD_hasDerivAt_clean :
    ∃ A' : ℝ, PoonSetup (u (-s)) s A' ∧
    HasDerivAt (poonD u)
      (1 / (2 * s ^ 2) * Lam d s (fun x => (pP (u (-s)) x - 2 * s * euclideanCoordLaplacian (u (-s)) x) *
        (pP (u (-s)) x - 2 * s * euclideanCoordLaplacian (u (-s)) x)) - 1 / s * poonD u s) s := by
  obtain ⟨-, -, hder⟩ := poonD_hasDerivAt hsmooth heat hbound hs0 hsT hAs
  obtain ⟨A', hP⟩ := exists_poonSetup hsmooth heat hbound hs0 hsT hAs
  refine ⟨A', hP, ?_⟩
  have := hP.lam_D_identity
  rw [poonD_eq_lam]
  exact this ▸ hder

end Admissible

/-- Cauchy–Schwarz in `L²(Φ dx)` via the discriminant. -/
theorem lam_cs_of_pos {s : ℝ} (hs : 0 < s) {A' : ℝ} (hw : WeightInt d s A') {f g : Vec d → ℝ}
    (hf : PDom A' f) (hg : PDom A' g)
    (hH : 0 < Lam d s (fun x => f x * f x)) :
    Lam d s (fun x => f x * g x) ^ 2 ≤
      Lam d s (fun x => f x * f x) * Lam d s (fun x => g x * g x) := by
  set I := Lam d s (fun x => f x * g x) with hI
  set Hf := Lam d s (fun x => f x * f x) with hHf
  set W := Lam d s (fun x => g x * g x) with hW
  have hnn : 0 ≤ Lam d s (fun x => (g x - (I / Hf) * f x) * (g x - (I / Hf) * f x)) := by
    unfold Lam
    exact integral_nonneg fun x => mul_nonneg (mul_self_nonneg _) (heatKernel_pos d hs x).le
  have hff := hf.mul hf
  have hgg := hg.mul hg
  have hfg := hf.mul hg
  have e : Lam d s (fun x => (g x - (I / Hf) * f x) * (g x - (I / Hf) * f x)) =
      W + (-(2 * (I / Hf))) * I + (I / Hf) ^ 2 * Hf := by
    rw [show (fun x => (g x - (I / Hf) * f x) * (g x - (I / Hf) * f x)) =
        fun x => g x * g x + (-(2 * (I / Hf))) * (f x * g x) +
          (I / Hf) ^ 2 * (f x * f x) from funext fun x => by ring,
      Lam_add hs hw (hgg.add (hfg.const_mul _)) (hff.const_mul _),
      Lam_add hs hw hgg (hfg.const_mul _), Lam_const_mul, Lam_const_mul]
  rw [e] at hnn
  have hH0 : Hf ≠ 0 := hH.ne'
  have : W - I ^ 2 / Hf ≥ 0 := by
    have h2 : W + (-(2 * (I / Hf))) * I + (I / Hf) ^ 2 * Hf = W - I ^ 2 / Hf := by
      field_simp; ring
    linarith
  have h3 : I ^ 2 / Hf ≤ W := by linarith
  rw [div_le_iff₀ hH] at h3
  linarith

/-- On the admissible interval where `H > 0`, the frequency is differentiable with nonnegative
derivative. -/
theorem poonFrequency_deriv_nonneg
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (jointOf u) (Ioo (-T) 0 ×ˢ (univ : Set (Vec d))))
    (heat : ∀ t ∈ Ioo (-T) 0, ∀ x : Vec d,
      HasDerivAt (fun τ : ℝ => u τ x) (euclideanCoordLaplacian (u t) x) t)
    {A C : ℝ}
    (hbound : ∀ t ∈ Ioo (-T) 0, ∀ x : Vec d, |u t x| ≤ C * Real.exp (A * vecNormSq x))
    {s : ℝ} (hs0 : 0 < s) (hsT : s < T) (hAs : 8 * A * s < 1) (hH : 0 < poonH u s) :
    ∃ N' : ℝ, HasDerivAt (poonFrequency u) N' s ∧ 0 ≤ N' := by
  have hHd := poonH_hasDerivAt_two_mul hsmooth heat hbound hs0 hsT hAs
  obtain ⟨A', hP, hDd⟩ := poonD_hasDerivAt_clean hsmooth heat hbound hs0 hsT hAs
  have hw := hP.weight
  set v := u (-s) with hv
  set W := Lam d s (fun x => (pP v x - 2 * s * euclideanCoordLaplacian v x) *
    (pP v x - 2 * s * euclideanCoordLaplacian v x)) with hW
  set I := Lam d s (fun x => v x * (pP v x - 2 * s * euclideanCoordLaplacian v x)) with hI
  have hwd : PDom A' (fun x => pP v x - 2 * s * euclideanCoordLaplacian v x) :=
    hP.dom_P.sub (hP.dom_L.const_mul _)
  have hHeq : poonH u s = Lam d s (fun x => v x * v x) := poonH_eq_lam u s
  have hI2 : I = 2 * s * poonD u s := hP.lam_vw_identity
  have hcs := lam_cs_of_pos hs0 hw hP.dom_v hwd (hHeq ▸ hH)
  rw [← hI, ← hHeq, ← hW] at hcs
  have hmul : HasDerivAt (fun r => r * poonD u r) (1 * poonD u s + s * (1 / (2 * s ^ 2) * W -
      1 / s * poonD u s)) s := (hasDerivAt_id s).mul hDd
  have hdiv := hmul.div hHd hH.ne'
  refine ⟨_, hdiv, ?_⟩
  apply div_nonneg _ (sq_nonneg _)
  have hs0' : s ≠ 0 := hs0.ne'
  rw [hI2] at hcs
  have key : (1 * poonD u s + s * (1 / (2 * s ^ 2) * W - 1 / s * poonD u s)) * poonH u s -
      s * poonD u s * (2 * poonD u s) = (poonH u s * W - (2 * s * poonD u s) ^ 2 ) / (2 * s) := by
    field_simp
    ring
  have : 0 ≤ (poonH u s * W - (2 * s * poonD u s) ^ 2) / (2 * s) := by
    apply div_nonneg _ (by positivity)
    linarith
  linarith

end

end PDE
