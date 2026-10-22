module

public import PDEFoundation.Monotonicity.Core.HarmonicFacadeSmooth
public import PDEFoundation.Monotonicity.Core.HarmonicFacadeEuler
public import PDEFoundation.PDE.HarmonicPointwiseAssembly
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Analytic.Polynomial
public import PDEFoundation.Monotonicity.Core.Homogeneous

/-!
# Chapter 2 harmonic facade

For `u` of class `C²` and classically harmonic on a round ball `euclideanBall 0 R`:

* `PDE.contDiffOn_top_of_harmonicOn` : `u` is `C^∞` (Weyl), with the corollary `contDiffOn_three`;
* `PDE.analyticOnNhd_of_harmonicOn_C2` : `u` is real analytic on the ball;
* unique continuation from a smaller concentric ball (against another harmonic function or a
  polynomial);
* the Euler field `x · ∇u` and every coordinate derivative of `u` are harmonic (see
  `HarmonicFacadeEuler`).
-/

@[expose] public section

open Filter
open scoped Topology

namespace PDE

noncomputable section

variable {d : ℕ}

theorem euclideanBall_eq_abs (x : Vec d) (R : ℝ) :
    euclideanBall x R = euclideanBall x |R| := by
  ext y
  change euclideanSqDist y x < R ^ 2 ↔ euclideanSqDist y x < |R| ^ 2
  rw [sq_abs]

theorem euclideanBall_eq_empty_zero (x : Vec d) : euclideanBall x (0 : ℝ) = ∅ := by
  ext y
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hy
  have hy' : euclideanSqDist y x < (0 : ℝ) ^ 2 := hy
  have : 0 ≤ euclideanSqDist y x := euclideanSqDist_nonneg _ _
  norm_num at hy'
  linarith

/-- **Weyl regularity.** A `C²` classically harmonic function on a round ball is `C^∞` there. -/
theorem contDiffOn_top_of_harmonicOn (hd : 0 < d) {R : ℝ} {u : Vec d → ℝ}
    (hu : ContDiffOn ℝ 2 u (euclideanBall (0 : Vec d) R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) u (euclideanBall (0 : Vec d) R) := by
  rcases eq_or_ne R 0 with rfl | hR0
  · rw [euclideanBall_eq_empty_zero]; exact contDiffOn_empty
  rw [euclideanBall_eq_abs] at hu hharm ⊢
  have hR : 0 < |R| := abs_pos.2 hR0
  generalize |R| = R at hR hu hharm ⊢
  intro x hx
  have hxn : vecEuclideanNorm (x - 0) < R := (mem_euclideanBall_iff_vecEuclideanNorm_lt hR).1 hx
  set ρ := (vecEuclideanNorm (x - 0) + R) / 2 with hρdef
  have hρ : 0 < ρ := by
    have := vecEuclideanNorm_nonneg (x - 0)
    rw [hρdef]; linarith
  have hρR : ρ < R := by rw [hρdef]; linarith
  have hxρ : x ∈ euclideanBall (0 : Vec d) ρ := by
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hρ]; rw [hρdef]; linarith
  have h := contDiffOn_top_of_harmonicOn_aux hd hρ hρR hu hharm
  exact (h.contDiffAt ((isOpen_euclideanBall 0 ρ).mem_nhds hxρ)).contDiffWithinAt

/-- Corollary of Weyl regularity: harmonic `C²` functions on a ball are `C³`. -/
theorem contDiffOn_three_of_harmonicOn (hd : 0 < d) {R : ℝ} {u : Vec d → ℝ}
    (hu : ContDiffOn ℝ 2 u (euclideanBall (0 : Vec d) R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0) :
    ContDiffOn ℝ 3 u (euclideanBall (0 : Vec d) R) := by
  have h := contDiffOn_top_of_harmonicOn hd hu hharm
  exact_mod_cast contDiffOn_infty.1 h 3

/-- Corollary of Weyl regularity: harmonic `C²` functions on a ball are `C^n` for every `n`. -/
theorem contDiffOn_nat_of_harmonicOn (hd : 0 < d) {R : ℝ} {u : Vec d → ℝ}
    (hu : ContDiffOn ℝ 2 u (euclideanBall (0 : Vec d) R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0) (n : ℕ) :
    ContDiffOn ℝ n u (euclideanBall (0 : Vec d) R) :=
  contDiffOn_infty.1 (contDiffOn_top_of_harmonicOn hd hu hharm) n

/-- A `C²` classically harmonic function on a round ball is real analytic there. -/
theorem analyticOnNhd_of_harmonicOn_C2 (hd : 0 < d) {R : ℝ} {u : Vec d → ℝ}
    (hu : ContDiffOn ℝ 2 u (euclideanBall (0 : Vec d) R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0) :
    AnalyticOnNhd ℝ u (euclideanBall (0 : Vec d) R) := by
  have hsmooth := contDiffOn_top_of_harmonicOn hd hu hharm
  rcases eq_or_ne R 0 with rfl | hR0
  · rw [euclideanBall_eq_empty_zero]; intro x hx; exact hx.elim
  rw [euclideanBall_eq_abs] at hsmooth hharm ⊢
  have hR : 0 < |R| := abs_pos.2 hR0
  generalize |R| = R at hR hsmooth hharm ⊢
  intro x hx
  exact analyticAt_of_harmonicOn hd hR hsmooth hharm hx

/-- Unique continuation for analytic functions on a ball from a smaller concentric ball. -/
theorem eqOn_euclideanBall_of_analyticOnNhd {R ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R)
    {u v : Vec d → ℝ} (hu : AnalyticOnNhd ℝ u (euclideanBall (0 : Vec d) R))
    (hv : AnalyticOnNhd ℝ v (euclideanBall (0 : Vec d) R))
    (huv : Set.EqOn u v (euclideanBall (0 : Vec d) ρ)) :
    Set.EqOn u v (euclideanBall (0 : Vec d) R) := by
  have hR : 0 < R := hρ.trans_le hρR
  have h0ρ : (0 : Vec d) ∈ euclideanBall (0 : Vec d) ρ := by
    exact center_mem_euclideanBall 0 hρ
  have h0R : (0 : Vec d) ∈ euclideanBall (0 : Vec d) R := by
    exact center_mem_euclideanBall 0 hR
  have hev : u =ᶠ[𝓝 (0 : Vec d)] v := by
    filter_upwards [(isOpen_euclideanBall 0 ρ).mem_nhds h0ρ] with y hy using huv hy
  exact hu.eqOn_of_preconnected_of_eventuallyEq hv
    (convex_euclideanBall (0 : Vec d) R).isPreconnected h0R hev

/-- Unique continuation between two `C²` harmonic functions. -/
theorem eqOn_euclideanBall_of_harmonic_eqOn_inner (hd : 0 < d) {R ρ : ℝ} (hρ : 0 < ρ)
    (hρR : ρ ≤ R) {u v : Vec d → ℝ}
    (hu : ContDiffOn ℝ 2 u (euclideanBall (0 : Vec d) R))
    (huh : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0)
    (hv : ContDiffOn ℝ 2 v (euclideanBall (0 : Vec d) R))
    (hvh : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian v x = 0)
    (huv : Set.EqOn u v (euclideanBall (0 : Vec d) ρ)) :
    Set.EqOn u v (euclideanBall (0 : Vec d) R) :=
  eqOn_euclideanBall_of_analyticOnNhd hρ hρR (analyticOnNhd_of_harmonicOn_C2 hd hu huh)
    (analyticOnNhd_of_harmonicOn_C2 hd hv hvh) huv

/-- Unique continuation of a `C²` harmonic function against a polynomial. -/
theorem eqOn_euclideanBall_of_harmonic_eq_polynomial_inner (hd : 0 < d) {R ρ : ℝ}
    (hρ : 0 < ρ) (hρR : ρ ≤ R) {u : Vec d → ℝ}
    (hu : ContDiffOn ℝ 2 u (euclideanBall (0 : Vec d) R))
    (huh : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0)
    (p : MvPolynomial (Fin d) ℝ)
    (hup : Set.EqOn u (fun x => MvPolynomial.eval x p) (euclideanBall (0 : Vec d) ρ)) :
    Set.EqOn u (fun x => MvPolynomial.eval x p) (euclideanBall (0 : Vec d) R) :=
  eqOn_euclideanBall_of_analyticOnNhd hρ hρR (analyticOnNhd_of_harmonicOn_C2 hd hu huh)
    ((analyticOnNhd_eval_mvPolynomial p).mono (Set.subset_univ _)) hup

/-- The Euler field `x ↦ x · ∇u` of a `C²` harmonic function on a ball is harmonic there. -/
theorem euclideanCoordLaplacian_euler_of_harmonicOn (hd : 0 < d) {R : ℝ} {u : Vec d → ℝ}
    (hu : ContDiffOn ℝ 2 u (euclideanBall (0 : Vec d) R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0) :
    ∀ x ∈ euclideanBall (0 : Vec d) R,
      euclideanCoordLaplacian (fun y => vecDot y (classicalGradient u y)) x = 0 :=
  fun _ hx => euclideanCoordLaplacian_euler_eq_zero (isOpen_euclideanBall 0 R)
    (contDiffOn_top_of_harmonicOn hd hu hharm) hharm hx

/-- The Euler field `x ↦ x · ∇u` of a `C²` harmonic function on a ball is smooth there. -/
theorem contDiffOn_euler_of_harmonicOn (hd : 0 < d) {R : ℝ} {u : Vec d → ℝ}
    (hu : ContDiffOn ℝ 2 u (euclideanBall (0 : Vec d) R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y => vecDot y (classicalGradient u y))
      (euclideanBall (0 : Vec d) R) :=
  contDiffOn_euler (isOpen_euclideanBall 0 R) (contDiffOn_top_of_harmonicOn hd hu hharm)

/-- Each coordinate derivative of a `C²` harmonic function on a ball is smooth and harmonic. -/
theorem contDiffOn_euclideanCoordDeriv_of_harmonicOn (hd : 0 < d) {R : ℝ} {u : Vec d → ℝ}
    (hu : ContDiffOn ℝ 2 u (euclideanBall (0 : Vec d) R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0) (i : Fin d) :
    ContDiffOn ℝ (⊤ : ℕ∞) (euclideanCoordDeriv i u) (euclideanBall (0 : Vec d) R) ∧
      ∀ x ∈ euclideanBall (0 : Vec d) R,
        euclideanCoordLaplacian (euclideanCoordDeriv i u) x = 0 :=
  contDiffOn_euclideanCoordDeriv_and_harmonic (isOpen_euclideanBall 0 R)
    (contDiffOn_top_of_harmonicOn hd hu hharm) hharm i

/-- Each component of `classicalGradient u` is smooth on the ball. -/
theorem contDiffOn_classicalGradient_apply_of_harmonicOn (hd : 0 < d) {R : ℝ} {u : Vec d → ℝ}
    (hu : ContDiffOn ℝ 2 u (euclideanBall (0 : Vec d) R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0) (i : Fin d) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y => classicalGradient u y i) (euclideanBall (0 : Vec d) R) :=
  (contDiffOn_euclideanCoordDeriv_of_harmonicOn hd hu hharm i).1

end

end PDE
