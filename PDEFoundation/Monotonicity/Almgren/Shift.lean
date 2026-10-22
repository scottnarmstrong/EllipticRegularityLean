module

public import PDEFoundation.Monotonicity.Core.HarmonicFacade

/-!
# Almgren equality case: the shifted Euler field

For `u` smooth on an open set `U`, the function `x ↦ x · ∇u - α u` is smooth, and harmonic
when `u` is.
-/

@[expose] public section

namespace PDE

noncomputable section

variable {d : ℕ}

/-- Laplacian of `f - a g` at a point of an open set, for smooth `f, g`. -/
theorem euclideanCoordLaplacian_sub_const_mul {U : Set (Vec d)} (hU : IsOpen U)
    {f g : Vec d → ℝ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U)
    (a : ℝ) {x : Vec d} (hx : x ∈ U) :
    euclideanCoordLaplacian (fun z => f z - a * g z) x =
      euclideanCoordLaplacian f x - a * euclideanCoordLaplacian g x := by
  have hfirst : ∀ j : Fin d, ∀ y ∈ U,
      euclideanCoordDeriv j (fun z => f z - a * g z) y =
        euclideanCoordDeriv j f y - a * euclideanCoordDeriv j g y := by
    intro j y hy
    have h := ((differentiableAt_of_contDiffOn_top hU hf hy).hasFDerivAt).sub
      ((differentiableAt_of_contDiffOn_top hU hg hy).hasFDerivAt.const_mul a)
    unfold euclideanCoordDeriv
    have h' : HasFDerivAt (fun z => f z - a * g z)
        (fderiv ℝ f y - a • fderiv ℝ g y) y := h
    rw [h'.fderiv]
    simp
  have hsecond : ∀ j : Fin d,
      euclideanCoordSecondDeriv j j (fun z => f z - a * g z) x =
        euclideanCoordSecondDeriv j j f x - a * euclideanCoordSecondDeriv j j g x := by
    intro j
    have hev : euclideanCoordDeriv j (fun z => f z - a * g z) =ᶠ[nhds x]
        fun z => euclideanCoordDeriv j f z - a * euclideanCoordDeriv j g z := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hfirst j y hy
    unfold euclideanCoordSecondDeriv
    rw [hev.fderiv_eq]
    have h := ((differentiableAt_of_contDiffOn_top hU
        (contDiffOn_top_euclideanCoordDeriv hU hf j) hx).hasFDerivAt).sub
      ((differentiableAt_of_contDiffOn_top hU
        (contDiffOn_top_euclideanCoordDeriv hU hg j) hx).hasFDerivAt.const_mul a)
    have h' : HasFDerivAt (fun z => euclideanCoordDeriv j f z - a * euclideanCoordDeriv j g z)
        (fderiv ℝ (euclideanCoordDeriv j f) x - a • fderiv ℝ (euclideanCoordDeriv j g) x) x := h
    rw [h'.fderiv]
    simp
  unfold euclideanCoordLaplacian
  simp_rw [hsecond]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]

/-- The shifted Euler field `x ↦ x · ∇u - α u` of a `C²` harmonic function is smooth and
harmonic on the ball. -/
theorem shiftedEuler_harmonic (hd : 0 < d) {R : ℝ} {u : Vec d → ℝ}
    (hu : ContDiffOn ℝ 2 u (euclideanBall (0 : Vec d) R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0) (α : ℝ) :
    ContDiffOn ℝ 2 (fun y => vecDot y (classicalGradient u y) - α * u y)
        (euclideanBall (0 : Vec d) R) ∧
      ∀ x ∈ euclideanBall (0 : Vec d) R,
        euclideanCoordLaplacian (fun y => vecDot y (classicalGradient u y) - α * u y) x = 0 := by
  have hutop := contDiffOn_top_of_harmonicOn hd hu hharm
  refine ⟨?_, fun x hx => ?_⟩
  · have h : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => vecDot y (classicalGradient u y) - α * u y)
        (euclideanBall (0 : Vec d) R) :=
      (contDiffOn_euler_of_harmonicOn hd hu hharm).sub (contDiffOn_const.mul hutop)
    exact h.of_le (by simp)
  · rw [euclideanCoordLaplacian_sub_const_mul (isOpen_euclideanBall 0 R)
      (contDiffOn_euler_of_harmonicOn hd hu hharm) hutop α hx,
      euclideanCoordLaplacian_euler_of_harmonicOn hd hu hharm x hx, hharm x hx]
    ring

end

end PDE
