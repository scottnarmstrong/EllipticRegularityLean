module

public import PDEFoundation

/-!
# Calculus of the Meyers-type profiles `s^γ x_k`

`s(x) = ∑ w_j x_j²` for a `0/1` weight vector `w`.  With `w ≡ 1` this is `|x|²` (Meyers' example in
`ℝᵈ`), and with `w = 1` on the first two coordinates it is `r²` (the planar-type example of
Proposition 4.7).  This file computes the classical gradient of `s^γ x_k`
and of the flux components off the singular set `{s = 0}`.
-/

@[expose] public section

namespace PDE.Ch4Meyers

open MeasureTheory Set

variable {d : ℕ}

/-- The weighted quadratic form `s(x) = ∑ w_j x_j²`. -/
noncomputable def axisSq (w : Fin d → ℝ) (x : Vec d) : ℝ := ∑ j, w j * x j ^ 2

variable {w : Fin d → ℝ}

theorem axisSq_nonneg (hw : ∀ i, w i = 0 ∨ w i = 1) (x : Vec d) : 0 ≤ axisSq w x := by
  refine Finset.sum_nonneg fun j _ => ?_
  rcases hw j with h | h <;> simp [h, sq_nonneg]

theorem sq_le_axisSq (hw : ∀ i, w i = 0 ∨ w i = 1) (x : Vec d) {i : Fin d} (hi : w i = 1) :
    x i ^ 2 ≤ axisSq w x := by
  have h := Finset.single_le_sum (f := fun j => w j * x j ^ 2)
    (fun j _ => by rcases hw j with h | h <;> simp [h, sq_nonneg]) (Finset.mem_univ i)
  unfold axisSq
  simpa [hi] using h

theorem wx_sq (hw : ∀ i, w i = 0 ∨ w i = 1) (x : Vec d) (i : Fin d) :
    (w i * x i) ^ 2 = w i * x i ^ 2 := by
  rcases hw i with h | h <;> simp [h]

theorem sum_wx_sq (hw : ∀ i, w i = 0 ∨ w i = 1) (x : Vec d) :
    ∑ i, (w i * x i) ^ 2 = axisSq w x := by
  simp only [axisSq]
  exact Finset.sum_congr rfl fun i _ => wx_sq hw x i

theorem wx_sq_le (hw : ∀ i, w i = 0 ∨ w i = 1) (x : Vec d) (i : Fin d) :
    (w i * x i) ^ 2 ≤ axisSq w x := by
  rw [wx_sq hw]
  rcases hw i with h | h
  · simpa [h] using axisSq_nonneg hw x
  · simpa [h] using sq_le_axisSq hw x h

theorem abs_wx_le_sqrt (hw : ∀ i, w i = 0 ∨ w i = 1) (x : Vec d) (i : Fin d) :
    |w i * x i| ≤ Real.sqrt (axisSq w x) := by
  apply Real.abs_le_sqrt
  exact wx_sq_le hw x i

theorem contDiff_axisSq (w : Fin d → ℝ) : ContDiff ℝ (⊤ : ℕ∞) (axisSq w) := by
  unfold axisSq
  refine ContDiff.sum fun j _ => ?_
  exact contDiff_const.mul ((contDiff_apply ℝ ℝ j).pow 2)

theorem hasFDerivAt_axisSq (w : Fin d → ℝ) (x : Vec d) :
    HasFDerivAt (axisSq w)
      (∑ j : Fin d, (2 * w j * x j) • ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin d => ℝ) j) x := by
  unfold axisSq
  have := HasFDerivAt.fun_sum (u := Finset.univ) (A := fun j (y : Vec d) => w j * y j ^ 2)
    (A' := fun j => (2 * w j * x j) • ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin d => ℝ) j) (x := x)
    (fun j _ => by
      have h1 : HasFDerivAt (fun y : Vec d => y j)
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j) x :=
        hasFDerivAt_apply j x
      have h2 := (h1.pow 2).const_mul (w j)
      convert h2 using 1
      ext v
      simp only [smul_eq_mul, smul_apply, ContinuousLinearMap.proj_apply]
      ring_nf)
  exact this

theorem fderiv_axisSq_basisVec (w : Fin d → ℝ) (x : Vec d) (i : Fin d) :
    fderiv ℝ (axisSq w) x (basisVec i) = 2 * w i * x i := by
  rw [(hasFDerivAt_axisSq w x).fderiv]
  simp [basisVec, Pi.single_apply]

/-- Partial derivative of `s^p * x_a * x_b` in the direction of the `i`th basis vector,
off the singular set. -/
theorem hasFDerivAt_rpow_mul_coord (hw : ∀ i, w i = 0 ∨ w i = 1) {x : Vec d}
    (hs : 0 < axisSq w x) (p : ℝ) (P : Vec d → ℝ) {P' : Vec d →L[ℝ] ℝ}
    (hP : HasFDerivAt P P' x) :
    HasFDerivAt (fun y => axisSq w y ^ p * P y)
      ((axisSq w x ^ p) • P' + P x • ((p * axisSq w x ^ (p - 1)) •
        ∑ j : Fin d, (2 * w j * x j) • ContinuousLinearMap.proj (R := ℝ)
          (φ := fun _ : Fin d => ℝ) j)) x := by
  have _ := hw
  have h1 := (hasFDerivAt_axisSq w x).rpow_const (p := p) (Or.inl hs.ne')
  have h2 := h1.mul hP
  convert h2 using 1

theorem fderiv_rpow_mul_basisVec (hw : ∀ i, w i = 0 ∨ w i = 1) {x : Vec d}
    (hs : 0 < axisSq w x) (p : ℝ) {P : Vec d → ℝ} {P' : Vec d →L[ℝ] ℝ}
    (hP : HasFDerivAt P P' x) (i : Fin d) :
    fderiv ℝ (fun y => axisSq w y ^ p * P y) x (basisVec i) =
      axisSq w x ^ p * P' (basisVec i) +
        P x * (p * axisSq w x ^ (p - 1) * (2 * w i * x i)) := by
  rw [(hasFDerivAt_rpow_mul_coord hw hs p P hP).fderiv]
  simp [basisVec, Pi.single_apply]

theorem hasFDerivAt_coord (x : Vec d) (k : Fin d) :
    HasFDerivAt (fun y : Vec d => y k)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) k) x :=
  hasFDerivAt_apply k x

end PDE.Ch4Meyers
