module

public import EllipticRegularity.Ch4.Spagnolo.Setup
public import PDEFoundation.Sobolev.H1.ZeroBoundaryCutoff
public import PDEFoundation.Geometry.EuclideanBall.Topology

/-!
# Radial tests of the equation: the flux identities

Manuscript Theorem 4.24, Step 2. For a smooth profile `X : ℝ → ℝ` vanishing on
`[s₀, ∞)` with `s₀ < 1`, the function `ψ(x) = X(|x|²)` is a smooth test
function compactly supported in the unit disc, with `∇ψ = 2 X'(|x|²) x`.
Testing the equation `-∇·a∇u = 0` with `ψ` and with `ψ u` (an `H¹₀` test) gives
* `∫_{B₁} X'(|x|²) σ · x = 0`, and
* `∫_{B₁} X(|x|²) ∇u · a∇u + 2 ∫_{B₁} X'(|x|²) u σ · x = 0`,
where `σ = a ∇u`. These are the integrated forms of `F = 0` and `G = φ`.
-/

@[expose] public section

namespace PDE.Ch4Spagnolo

open MeasureTheory Set

theorem hasFDerivAt_vecNormSq (x : Vec 2) :
    HasFDerivAt (fun y : Vec 2 => vecNormSq y)
      ((x 0 • ContinuousLinearMap.proj 0 + x 0 • ContinuousLinearMap.proj 0) +
        (x 1 • ContinuousLinearMap.proj 1 + x 1 • ContinuousLinearMap.proj 1) :
          Vec 2 →L[ℝ] ℝ) x := by
  have h : (fun x : Vec 2 => vecNormSq x) = fun x => x 0 * x 0 + x 1 * x 1 := by
    funext x; simp [vecNormSq, vecDot, Fin.sum_univ_two]
  rw [h]
  exact ((hasFDerivAt_apply 0 x).mul (hasFDerivAt_apply 0 x)).add
    ((hasFDerivAt_apply 1 x).mul (hasFDerivAt_apply 1 x))

/-- The classical gradient of the radial function `x ↦ X(|x|²)` is
`2 X'(|x|²) x`. -/
theorem classicalGradient_radial {X : ℝ → ℝ} (hX : Differentiable ℝ X) (x : Vec 2) :
    classicalGradient (fun y : Vec 2 => X (vecNormSq y)) x =
      (2 * deriv X (vecNormSq x)) • x := by
  have h : HasFDerivAt (fun y : Vec 2 => X (vecNormSq y)) _ x :=
    (hX (vecNormSq x)).hasDerivAt.comp_hasFDerivAt x (hasFDerivAt_vecNormSq x)
  ext i
  rw [classicalGradient_apply, h.fderiv]
  fin_cases i <;> simp [basisVec] <;> ring

theorem tsupport_radial_subset {X : ℝ → ℝ} {s0 : ℝ} (hXs : ∀ t, s0 ≤ t → X t = 0) :
    tsupport (fun x : Vec 2 => X (vecNormSq x)) ⊆ {x | vecNormSq x ≤ s0} := by
  refine closure_minimal ?_ (isClosed_le continuous_vecNormSq continuous_const)
  intro y hx
  by_contra hcon
  exact hx (hXs _ (le_of_lt (not_le.1 hcon)))

theorem tsupport_radial_subset_ball {X : ℝ → ℝ} {s0 : ℝ} (hs0 : s0 < 1)
    (hXs : ∀ t, s0 ≤ t → X t = 0) :
    tsupport (fun x : Vec 2 => X (vecNormSq x)) ⊆ euclideanBall (0 : Vec 2) 1 :=
  fun _ hx => mem_ball_one_iff.2 (lt_of_le_of_lt (tsupport_radial_subset hXs hx) hs0)

theorem hasCompactSupport_radial {X : ℝ → ℝ} {s0 : ℝ} (hs0 : s0 < 1)
    (hXs : ∀ t, s0 ≤ t → X t = 0) :
    HasCompactSupport (fun x : Vec 2 => X (vecNormSq x)) := by
  refine (isCompact_closedBall (0 : Vec 2) 1).of_isClosed_subset (isClosed_tsupport _) ?_
  exact (tsupport_radial_subset_ball hs0 hXs).trans
    ((euclideanBall_subset_supBall (by norm_num)).trans Metric.ball_subset_closedBall)

section Solution

variable {Λ : ℝ} {a : CoeffField 2}

/-- **Radial flux identity** (`F = 0` in integrated form):
`∫_{B₁} X'(|x|²) σ · x = 0`. -/
theorem integral_deriv_radial_mul_flux_dot_eq_zero
    (hmeas : ∀ i j : Fin 2, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec 2) 1)))
    (hell : ∀ x ∈ euclideanBall (0 : Vec 2) 1, IsEllipticMatrix 1 Λ (a x))
    (u : H1Function (euclideanBall (0 : Vec 2) 1))
    (hsol : IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec 2) 1) u
      (0 : Vec 2 → ℝ) 0)
    {X : ℝ → ℝ} (hX : ContDiff ℝ (⊤ : ℕ∞) X) {s0 : ℝ} (hs0 : s0 < 1)
    (hXs : ∀ t, s0 ≤ t → X t = 0) :
    ∫ x in euclideanBall (0 : Vec 2) 1,
      deriv X (vecNormSq x) * vecDot (matVecMul (a x) (u.grad x)) x = 0 := by
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => X (vecNormSq x)) :=
    hX.comp contDiff_vecNormSq
  let φ : H10Function (euclideanBall (0 : Vec 2) 1) :=
    H10Function.ofContDiff (isOpen_euclideanBall _ _) hψ (hasCompactSupport_radial hs0 hXs)
      (tsupport_radial_subset_ball hs0 hXs)
  have htest := (DGNM.solution_test (isOpenBoundedConvexDomain_euclideanBall _ one_pos)
    hmeas hell hsol φ).2
  have hgrad : ∀ x, φ.toH1Function.grad x = (2 * deriv X (vecNormSq x)) • x := by
    intro x
    rw [← classicalGradient_radial (hX.differentiable (by simp)) x]
    rfl
  simp only [hgrad, DGNM.vecDot_smul_right] at htest
  have h2 : ∫ x in euclideanBall (0 : Vec 2) 1,
      2 * (deriv X (vecNormSq x) * vecDot (matVecMul (a x) (u.grad x)) x) = 0 := by
    rw [← htest]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring
  rw [integral_const_mul] at h2
  linarith

/-- **Radial energy identity** (`G = φ` in integrated form):
`∫_{B₁} X(|x|²) ∇u·a∇u + 2 ∫_{B₁} X'(|x|²) u σ · x = 0`. -/
theorem integral_radial_mul_energy_add_eq_zero
    (hmeas : ∀ i j : Fin 2, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec 2) 1)))
    (hell : ∀ x ∈ euclideanBall (0 : Vec 2) 1, IsEllipticMatrix 1 Λ (a x))
    (u : H1Function (euclideanBall (0 : Vec 2) 1))
    (hsol : IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec 2) 1) u
      (0 : Vec 2 → ℝ) 0)
    {X : ℝ → ℝ} (hX : ContDiff ℝ (⊤ : ℕ∞) X) {s0 : ℝ} (hs0 : s0 < 1)
    (hXs : ∀ t, s0 ≤ t → X t = 0) :
    (∫ x in euclideanBall (0 : Vec 2) 1,
        X (vecNormSq x) * vecDot (u.grad x) (matVecMul (a x) (u.grad x))) +
      2 * ∫ x in euclideanBall (0 : Vec 2) 1,
        deriv X (vecNormSq x) * (u x * vecDot (matVecMul (a x) (u.grad x)) x) = 0 := by
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => X (vecNormSq x)) :=
    hX.comp contDiff_vecNormSq
  let φ : H10Function (euclideanBall (0 : Vec 2) 1) :=
    u.mulContDiffHasCompactSupportToH10 (isOpenBoundedConvexDomain_euclideanBall _ one_pos)
      hψ (hasCompactSupport_radial hs0 hXs) (tsupport_radial_subset_ball hs0 hXs)
  have htest := (DGNM.solution_test (isOpenBoundedConvexDomain_euclideanBall _ one_pos)
    hmeas hell hsol φ).2
  have hgrad : ∀ x, φ.toH1Function.grad x =
      X (vecNormSq x) • u.grad x + u x • ((2 * deriv X (vecNormSq x)) • x) := by
    intro x
    rw [← classicalGradient_radial (hX.differentiable (by simp)) x]
    simp only [φ, H1Function.mulContDiffHasCompactSupportToH10_grad]
  simp only [hgrad, DGNM.vecDot_add_right, DGNM.vecDot_smul_right] at htest
  have hcontX : Continuous (fun x : Vec 2 => X (vecNormSq x)) :=
    hX.continuous.comp continuous_vecNormSq
  have hcontX' : Continuous (fun x : Vec 2 => deriv X (vecNormSq x)) :=
    (hX.continuous_deriv (by simp)).comp continuous_vecNormSq
  have hI1 := integrableOn_continuous_mul hcontX (integrableOn_energy hmeas hell u)
  have hI2 := (integrableOn_continuous_mul hcontX'
    (integrableOn_mul_flux_dot hmeas hell u)).const_mul 2
  rw [← integral_const_mul, ← integral_add hI1 hI2, ← htest]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [vecDot_comm (matVecMul (a x) (u.grad x)) (u.grad x)]
  ring

end Solution

end PDE.Ch4Spagnolo
