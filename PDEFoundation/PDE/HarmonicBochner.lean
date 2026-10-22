module

public import PDEFoundation.Sobolev.ClassicalLaplacian

/-!
# Native Bochner calculation for smooth harmonic functions

Mixed coordinate derivatives commute, so derivatives of a smooth harmonic
function are harmonic. Squaring gives a nonnegative coordinate Laplacian.
These are exact algebraic identities on the native vector carrier.
-/

@[expose] public section

namespace PDE

noncomputable section

variable {d : ℕ}

private theorem euclideanCoordDeriv_eq_zero_of_eventuallyEq
    {f : Vec d → ℝ} {c : ℝ} {x : Vec d}
    (h : f =ᶠ[nhds x] fun _ : Vec d ↦ c) (i : Fin d) :
    euclideanCoordDeriv i f x = 0 := by
  rw [euclideanCoordDeriv, h.fderiv_eq]
  simp

/-- A coordinate derivative of a smooth coordinate-harmonic function is
coordinate-harmonic. -/
theorem euclideanCoordLaplacian_euclideanCoordDeriv_eq_zero
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {U : Set (Vec d)} (hU : IsOpen U)
    (hharm : ∀ y ∈ U, euclideanCoordLaplacian u y = 0)
    {x : Vec d} (hx : x ∈ U) (i : Fin d) :
    euclideanCoordLaplacian (euclideanCoordDeriv i u) x = 0 := by
  have hstep : ∀ j : Fin d,
      euclideanCoordSecondDeriv j j (euclideanCoordDeriv i u) x =
        euclideanCoordDeriv i (euclideanCoordSecondDeriv j j u) x := fun j ↦
    euclideanCoordThirdDeriv_diag_right_comm hu i j x
  have hg : ∀ j : Fin d, HasFDerivAt (euclideanCoordSecondDeriv j j u)
      (fderiv ℝ (euclideanCoordSecondDeriv j j u) x) x := fun j ↦
    ((contDiff_euclideanCoordSecondDeriv hu j j).differentiable (by simp) x).hasFDerivAt
  have hL : HasFDerivAt (fun y : Vec d ↦ ∑ j : Fin d, euclideanCoordSecondDeriv j j u y)
      (∑ j : Fin d, fderiv ℝ (euclideanCoordSecondDeriv j j u) x) x := by
    have hres := HasFDerivAt.sum fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) ↦ hg j
    have hfun : (∑ j : Fin d, euclideanCoordSecondDeriv j j u) =
        fun y : Vec d ↦ ∑ j : Fin d, euclideanCoordSecondDeriv j j u y := by
      funext y
      simp [Finset.sum_apply]
    rw [hfun] at hres
    exact hres
  have hzero : euclideanCoordDeriv i (euclideanCoordLaplacian u) x = 0 :=
    euclideanCoordDeriv_eq_zero_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) hharm) i
  have hsplit : euclideanCoordDeriv i (euclideanCoordLaplacian u) x =
      ∑ j : Fin d, euclideanCoordDeriv i (euclideanCoordSecondDeriv j j u) x := by
    rw [euclideanCoordDeriv,
      show euclideanCoordLaplacian u =
        fun y : Vec d ↦ ∑ j : Fin d, euclideanCoordSecondDeriv j j u y from rfl,
      hL.fderiv]
    simp [euclideanCoordDeriv]
  rw [euclideanCoordLaplacian]
  rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) ↦ hstep j, ← hsplit, hzero]

/-- The coordinate Laplacian of a square is twice the squared coordinate
gradient plus twice the function times its Laplacian. -/
theorem euclideanCoordLaplacian_sq
    {g : Vec d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x : Vec d) :
    euclideanCoordLaplacian (fun y ↦ g y ^ 2) x =
      2 * ∑ j : Fin d, (euclideanCoordDeriv j g x) ^ 2 +
        2 * g x * euclideanCoordLaplacian g x := by
  classical
  have hD : ∀ j : Fin d, ContDiff ℝ (⊤ : ℕ∞) (euclideanCoordDeriv j g) :=
    fun j ↦ contDiff_euclideanCoordDeriv hg j
  have hsecond : ∀ j : Fin d,
      euclideanCoordSecondDeriv j j (fun y ↦ g y ^ 2) x =
        2 * (euclideanCoordDeriv j g x) ^ 2 +
          2 * g x * euclideanCoordSecondDeriv j j g x := by
    intro j
    rw [euclideanCoordSecondDeriv]
    have hfirst : euclideanCoordDeriv j (fun y ↦ g y ^ 2) =
        fun y ↦ 2 * g y * euclideanCoordDeriv j g y := by
      funext y
      exact euclideanCoordDeriv_sq hg j y
    rw [hfirst]
    unfold euclideanCoordDeriv
    have hgdiff : DifferentiableAt ℝ g x := (hg.differentiable (by simp)) x
    have hDdiff : DifferentiableAt ℝ (euclideanCoordDeriv j g) x :=
      ((hD j).differentiable (by simp)) x
    have h2gdiff : DifferentiableAt ℝ (fun y ↦ (2 : ℝ) * g y) x :=
      differentiableAt_const (c := (2 : ℝ)).mul hgdiff
    change (fderiv ℝ ((fun y ↦ (2 : ℝ) * g y) * euclideanCoordDeriv j g) x)
        (basisVec j) = _
    rw [fderiv_mul h2gdiff hDdiff]
    simp only [add_apply, smul_apply]
    rw [fderiv_const_mul hgdiff]
    simp only [smul_apply, smul_eq_mul]
    simp only [euclideanCoordSecondDeriv, euclideanCoordDeriv]
    ring
  rw [euclideanCoordLaplacian, Finset.sum_congr rfl
    (fun j (_ : j ∈ Finset.univ) ↦ hsecond j), Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [euclideanCoordLaplacian]

/-- The squared coordinate derivative of a smooth harmonic function is
subharmonic. -/
theorem euclideanCoordLaplacian_sq_euclideanCoordDeriv_nonneg
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {U : Set (Vec d)} (hU : IsOpen U)
    (hharm : ∀ y ∈ U, euclideanCoordLaplacian u y = 0)
    {x : Vec d} (hx : x ∈ U) (i : Fin d) :
    0 ≤ euclideanCoordLaplacian (fun y ↦ (euclideanCoordDeriv i u y) ^ 2) x := by
  rw [euclideanCoordLaplacian_sq (contDiff_euclideanCoordDeriv hu i),
    euclideanCoordLaplacian_euclideanCoordDeriv_eq_zero hu hU hharm hx i, mul_zero, add_zero]
  positivity

end

end PDE
