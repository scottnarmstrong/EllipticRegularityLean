module

public import PDEFoundation.Monotonicity.Defs
public import PDEFoundation.PDE.HarmonicWeylRepresentative
public import PDEFoundation.Sobolev.H1.Smooth
public import PDEFoundation.Sobolev.Cutoff.Ball
public import PDEFoundation.Analysis.LocalDivergenceIBP
public import PDEFoundation.Geometry.ConvexDomain

/-!
# Chapter 2 harmonic facade: `C²` harmonic functions are smooth

A classically harmonic `C²` function on a round ball is weakly harmonic on every smaller ball
(after localisation by a cutoff), hence equals its smooth Weyl representative.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace PDE

noncomputable section

variable {d : ℕ}

/-- Coordinate Laplacians agree for functions that agree on an open set. -/
theorem euclideanCoordLaplacian_congr_of_eqOn_open
    {f g : Vec d → ℝ} {U : Set (Vec d)} (hU : IsOpen U)
    (hfg : Set.EqOn f g U) {x : Vec d} (hx : x ∈ U) :
    euclideanCoordLaplacian f x = euclideanCoordLaplacian g x := by
  unfold euclideanCoordLaplacian
  apply Finset.sum_congr rfl
  intro i _
  unfold euclideanCoordSecondDeriv
  have hderiv : Set.EqOn (euclideanCoordDeriv i f) (euclideanCoordDeriv i g) U := by
    intro y hy
    unfold euclideanCoordDeriv
    have hev : f =ᶠ[𝓝 y] g := by
      filter_upwards [hU.mem_nhds hy] with z hz
      exact hfg hz
    rw [hev.fderiv_eq]
  have hev : euclideanCoordDeriv i f =ᶠ[𝓝 x] euclideanCoordDeriv i g := by
    filter_upwards [hU.mem_nhds hx] with z hz
    exact hderiv hz
  rw [hev.fderiv_eq]

/-- A globally `C²` function that is classically harmonic on a ball is a weak solution there. -/
theorem isWeakSolution_ball_of_contDiff_harmonic
    {ρ : ℝ} (hρ : 0 < ρ) {f : Vec d → ℝ} (hf : ContDiff ℝ 2 f)
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) ρ, euclideanCoordLaplacian f x = 0) :
    IsWeakDivergenceFormSolutionOn (fun _ : Vec d => (1 : Mat d))
      (euclideanBall (0 : Vec d) ρ)
      (H1Function.ofContDiffOnIsOpenBoundedConvexDomain
        (isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) hρ)
        (hf.of_le (by norm_num))) 0 0 := by
  have hUopen : IsOpen (euclideanBall (0 : Vec d) ρ) := isOpen_euclideanBall 0 ρ
  intro φ
  have hJ : ∀ i, ContDiffOn ℝ 1 (fun x => classicalGradient f x i)
      (euclideanBall (0 : Vec d) ρ) := by
    intro i
    have h1 : ContDiff ℝ 1 (fun x => fderiv ℝ f x (basisVec i)) := by
      have := hf.fderiv_right (m := 1) (by norm_num)
      exact this.clm_apply contDiff_const
    exact h1.contDiffOn
  have hgrad : ∀ x, (H1Function.ofContDiffOnIsOpenBoundedConvexDomain
        (isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) hρ)
        (hf.of_le (by norm_num))).grad x = classicalGradient f x := fun _ => rfl
  have hmat (x : Vec d) : matVecMul (1 : Mat d) (classicalGradient f x) =
      classicalGradient f x := by
    change (1 : Mat d).mulVec _ = _
    exact Matrix.one_mulVec _
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · simp only [hgrad, hmat]
    change IntegrableOn (fun x => ∑ i : Fin d, classicalGradient f x i * φ.partialDeriv i x) _
    exact integrable_finsetSum _ fun i _ =>
      φ.integrableOn_mul_partialDeriv_of_continuousOn hUopen (hJ i).continuousOn i
  · simp
  · simp [vecDot]
  · simp only [hgrad, hmat]
    have := integral_vecDot_weakTestFunction_grad_eq_neg_integral_divergence_mul hUopen
      (classicalGradient f) hJ φ
    rw [this]
    have hz : ∀ x ∈ euclideanBall (0 : Vec d) ρ,
        (∑ i : Fin d, classicalGradient (fun y => classicalGradient f y i) x i) * φ x = 0 := by
      intro x hx
      have : (∑ i : Fin d, classicalGradient (fun y => classicalGradient f y i) x i) =
          euclideanCoordLaplacian f x := rfl
      rw [this, hharm x hx, zero_mul]
    rw [setIntegral_congr_fun hUopen.measurableSet hz]
    simp [vecDot]

/-- Cutoff localisation of a `C²` function on a ball is globally `C²`. -/
theorem contDiff_cutoff_mul {R ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) {u : Vec d → ℝ}
    (hu : ContDiffOn ℝ 2 u (euclideanBall (0 : Vec d) R)) :
    ContDiff ℝ 2 (fun x => canonicalBallCutoff (0 : Vec d) ρ R x * u x) := by
  have hR : 0 < R := hρ.trans hρR
  have hχ : ContDiff ℝ 2 (canonicalBallCutoff (0 : Vec d) ρ R) :=
    by exact_mod_cast contDiff_infty.1 (canonicalBallCutoff_smooth (0 : Vec d) hρ.le hρR) 2
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ euclideanBall (0 : Vec d) R
  · exact hχ.contDiffAt.mul (hu.contDiffAt ((isOpen_euclideanBall 0 R).mem_nhds hx))
  · have hxs : x ∉ tsupport (canonicalBallCutoff (0 : Vec d) ρ R) := fun h =>
      hx (canonicalBallCutoff_tsupport_subset_outer hρ.le hρR h)
    have hev := notMem_tsupport_iff_eventuallyEq.1 hxs
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hev] with y hy
    simp [hy]

/-- **Weyl regularity for `C²` harmonic functions on a ball (smaller radius).** -/
theorem contDiffOn_top_of_harmonicOn_aux (hd : 0 < d) {R ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    {u : Vec d → ℝ} (hu : ContDiffOn ℝ 2 u (euclideanBall (0 : Vec d) R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) u (euclideanBall (0 : Vec d) ρ) := by
  have hsub : euclideanBall (0 : Vec d) ρ ⊆ euclideanBall (0 : Vec d) R := by
    intro x hx
    have hR : 0 < R := hρ.trans hρR
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hR]
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hρ] at hx
    linarith
  set f : Vec d → ℝ := fun x => canonicalBallCutoff (0 : Vec d) ρ R x * u x with hfdef
  have hf : ContDiff ℝ 2 f := contDiff_cutoff_mul hρ hρR hu
  have hfu : Set.EqOn f u (euclideanBall (0 : Vec d) ρ) := by
    intro x hx
    simp [hfdef, canonicalBallCutoff_eq_one_on_inner hρ.le hρR hx]
  have hfharm : ∀ x ∈ euclideanBall (0 : Vec d) ρ, euclideanCoordLaplacian f x = 0 := by
    intro x hx
    rw [euclideanCoordLaplacian_congr_of_eqOn_open (isOpen_euclideanBall 0 ρ) hfu hx]
    exact hharm x (hsub hx)
  obtain ⟨v, hv, -, hae, -⟩ := exists_harmonicWeylRepresentative hd hρ
    (H1Function.ofContDiffOnIsOpenBoundedConvexDomain
      (isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) hρ) (hf.of_le (by norm_num)))
    (isWeakSolution_ball_of_contDiff_harmonic hρ hf hfharm)
  have hvf : Set.EqOn v f (euclideanBall (0 : Vec d) ρ) := by
    have hae2 : v =ᵐ[volume.restrict (euclideanBall (0 : Vec d) ρ)] f := hae
    exact Measure.eqOn_open_of_ae_eq hae2 (isOpen_euclideanBall 0 ρ) hv.continuousOn
      hf.continuous.continuousOn
  have hvu : Set.EqOn v u (euclideanBall (0 : Vec d) ρ) := fun x hx => (hvf hx).trans (hfu hx)
  exact hv.congr fun x hx => (hvu hx).symm

end

end PDE
