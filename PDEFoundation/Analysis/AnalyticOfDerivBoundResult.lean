module

public import PDEFoundation.Analysis.AnalyticOfDerivBoundGlobal
public import PDEFoundation.Analysis.AnalyticOfDerivBoundLocalize

/-!
# Real analyticity from coordinate Cauchy-type derivative bounds
-/

@[expose] public section

namespace PDE

open scoped Topology

/-- Locally uniform bounds of order `M (K m)^m` on all coordinate evaluations
of iterated derivatives imply real analyticity at the center of the round ball. -/
theorem analyticAt_of_smooth_iteratedFDeriv_coordinate_bound {d : ℕ}
    (f : Vec d → ℝ) (x₀ : Vec d) {δ M K : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (euclideanBall x₀ δ))
    (hbound : ∀ y ∈ euclideanBall x₀ δ,
      ∀ m : ℕ, ∀ ι : Fin m → Fin d,
        |iteratedFDeriv ℝ m f y (fun k => Pi.single (ι k) 1)| ≤
          M * (K * m) ^ m) :
    AnalyticAt ℝ f x₀ := by
  let r : ℝ := δ / 2
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hrR : r < δ := by dsimp [r]; linarith
  let χ : Vec d → ℝ := canonicalBallCutoff x₀ r δ
  let g : Vec d → ℝ := fun y => χ y * f y
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ := canonicalBallCutoff_smooth x₀ hr hrR
  have hsupp : tsupport χ ⊆ euclideanBall x₀ δ :=
    canonicalBallCutoff_tsupport_subset_outer hr hrR
  have hg : ContDiff ℝ (⊤ : ℕ∞) g :=
    contDiff_mul_of_contDiffOn_of_tsupport_subset hf
      (isOpen_euclideanBall x₀ δ) hχ hsupp
  have heq (y : Vec d) (hy : y ∈ euclideanBall x₀ r) : g y = f y := by
    simp only [g, χ, canonicalBallCutoff_eq_one_on_inner hr hrR hy, one_mul]
  have hevent (y : Vec d) (hy : y ∈ euclideanBall x₀ r) :
      g =ᶠ[𝓝 y] f := by
    filter_upwards [(isOpen_euclideanBall x₀ r).mem_nhds hy] with z hz
    exact heq z hz
  have hsmall : euclideanBall x₀ r ⊆ euclideanBall x₀ δ :=
    euclideanBall_mono hr hrR.le
  have hboundG : ∀ y ∈ euclideanBall x₀ r,
      ∀ m : ℕ, ∀ ι : Fin m → Fin d,
        |iteratedFDeriv ℝ m g y (fun k => Pi.single (ι k) 1)| ≤
          M * (K * m) ^ m := by
    intro y hy m ι
    have hderiv : iteratedFDeriv ℝ m g y = iteratedFDeriv ℝ m f y :=
      ((hevent y hy).iteratedFDeriv ℝ m).eq_of_nhds
    rw [hderiv]
    exact hbound y (hsmall hy) m ι
  have hanalyticG : AnalyticAt ℝ g x₀ :=
    analyticAt_of_global_coordinate_deriv_bound g hg x₀
      (by dsimp [r]; linarith) hM hK hboundG
  have hx₀ : x₀ ∈ euclideanBall x₀ r := by
    change euclideanSqDist x₀ x₀ < r ^ 2
    rw [euclideanSqDist_self]
    have : 0 < r := by dsimp [r]; linarith
    positivity
  exact hanalyticG.congr (hevent x₀ hx₀)

/-- The requested `ContDiffOn ℝ ⊤` formulation follows from the genuinely
smooth criterion above; in Mathlib's order notation, `⊤` denotes analytic
regularity and `(⊤ : ℕ∞)` denotes smooth regularity. -/
theorem analyticAt_of_iteratedFDeriv_coordinate_bound {d : ℕ}
    (f : Vec d → ℝ) (x₀ : Vec d) {δ M K : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hf : ContDiffOn ℝ ⊤ f (euclideanBall x₀ δ))
    (hbound : ∀ y ∈ euclideanBall x₀ δ,
      ∀ m : ℕ, ∀ ι : Fin m → Fin d,
        |iteratedFDeriv ℝ m f y (fun k => Pi.single (ι k) 1)| ≤
          M * (K * m) ^ m) :
    AnalyticAt ℝ f x₀ :=
  analyticAt_of_smooth_iteratedFDeriv_coordinate_bound f x₀ hδ hM hK
    (hf.of_le (by simp)) hbound

end PDE
