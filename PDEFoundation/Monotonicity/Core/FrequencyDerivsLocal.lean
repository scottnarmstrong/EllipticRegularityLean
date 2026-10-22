module

public import PDEFoundation.Monotonicity.Core.Bridge
public import PDEFoundation.Sobolev.Cutoff.Ball
public import PDEFoundation.Geometry.EuclideanBall.Topology

/-!
# Chapter 2 frequency derivatives: localization and congruence lemmas

A function that is `C^∞` on a ball agrees near a smaller ball with a globally `C^∞` function, and
sphere means, sphere integrals and ball energies only depend on the function on the ball.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace PDE

noncomputable section

variable {d : ℕ}

/-- Localization of a function that is `C^∞` on a ball to a globally `C^∞` function. -/
theorem exists_contDiff_top_localization {u : Vec d → ℝ} {R ρ : ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (euclideanBall 0 R)) (hρ : 0 < ρ) (hρR : ρ < R) :
    ∃ (ρ' : ℝ) (v : Vec d → ℝ), ρ < ρ' ∧ ρ' < R ∧ ContDiff ℝ (⊤ : ℕ∞) v ∧
      EqOn v u (euclideanBall 0 ρ') := by
  set ρ' : ℝ := (ρ + R) / 2 with hρ'
  have h1 : ρ < ρ' := by rw [hρ']; linarith
  have h2 : ρ' < R := by rw [hρ']; linarith
  have hρ'0 : 0 ≤ ρ' := by linarith
  set χ := canonicalBallCutoff (0 : Vec d) ρ' R with hχ
  have hχs : ContDiff ℝ (⊤ : ℕ∞) χ := canonicalBallCutoff_smooth (0 : Vec d) hρ'0 h2
  have hts : tsupport χ ⊆ euclideanBall 0 R :=
    canonicalBallCutoff_tsupport_subset_outer hρ'0 h2
  have hopen : IsOpen (euclideanBall (0 : Vec d) R) := isOpen_euclideanBall 0 R
  refine ⟨ρ', (euclideanBall 0 R).indicator (fun x => χ x * u x), h1, h2, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ euclideanBall (0 : Vec d) R
    · have hat : ContDiffAt ℝ (⊤ : ℕ∞) (fun x => χ x * u x) x :=
        hχs.contDiffAt.mul (hu.contDiffAt (hopen.mem_nhds hx))
      refine hat.congr_of_eventuallyEq ?_
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact indicator_of_mem hy _
    · have hxt : x ∉ tsupport χ := fun h => hx (hts h)
      have hn : (tsupport χ)ᶜ ∈ nhds x := (isClosed_tsupport χ).isOpen_compl.mem_nhds hxt
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hn] with y hy
      by_cases hyb : y ∈ euclideanBall (0 : Vec d) R
      · rw [indicator_of_mem hyb, image_eq_zero_of_notMem_tsupport hy, zero_mul]
      · rw [indicator_of_notMem hyb]
  · intro x hx
    have hxR : x ∈ euclideanBall (0 : Vec d) R := euclideanBall_mono hρ'0 h2.le hx
    simp only [indicator_of_mem hxR]
    have h1x : χ x = 1 := canonicalBallCutoff_eq_one_on_inner hρ'0 h2 hx
    rw [h1x, one_mul]

/-- Points of the sphere `s • ω` with `|s| < ρ` lie in the ball of radius `ρ`. -/
theorem smul_toVec_mem_euclideanBall {ρ s : ℝ} (hρ : 0 < ρ) (hs : |s| < ρ)
    (ω : Metric.sphere (0 : HilbertVec d) 1) :
    (0 : Vec d) + s • (ω : HilbertVec d).toVec ∈ euclideanBall 0 ρ := by
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hρ, zero_add, sub_zero, vecEuclideanNorm_smul,
    ← HilbertVec.norm_eq_vecEuclideanNorm]
  simpa using hs

/-- The sphere integral over `∂B_s` only depends on the function on `B_ρ` when `|s| < ρ`. -/
theorem sphereIntegral_congr_of_eqOn {f g : Vec d → ℝ} {ρ s : ℝ} (hρ : 0 < ρ) (hs : |s| < ρ)
    (h : EqOn f g (euclideanBall 0 ρ)) : sphereIntegral 0 s f = sphereIntegral 0 s g := by
  unfold sphereIntegral
  have : (fun ω : Metric.sphere (0 : HilbertVec d) 1 => f (0 + s • (ω : HilbertVec d).toVec)) =
      fun ω : Metric.sphere (0 : HilbertVec d) 1 => g (0 + s • (ω : HilbertVec d).toVec) :=
    funext fun ω => h (smul_toVec_mem_euclideanBall hρ hs ω)
  rw [this]

/-- The sphere mean over `∂B_s` only depends on the function on `B_ρ` when `|s| < ρ`. -/
theorem sphereMean_congr_of_eqOn {f g : Vec d → ℝ} {ρ s : ℝ} (hρ : 0 < ρ) (hs : |s| < ρ)
    (h : EqOn f g (euclideanBall 0 ρ)) : sphereMean 0 s f = sphereMean 0 s g := by
  unfold sphereMean
  have : (fun ω : Metric.sphere (0 : HilbertVec d) 1 => f (0 + s • (ω : HilbertVec d).toVec)) =
      fun ω : Metric.sphere (0 : HilbertVec d) 1 => g (0 + s • (ω : HilbertVec d).toVec) :=
    funext fun ω => h (smul_toVec_mem_euclideanBall hρ hs ω)
  rw [this]

/-- The classical gradient only depends on the function on an open set containing the point. -/
theorem classicalGradient_congr_of_eqOn_open {f g : Vec d → ℝ} {U : Set (Vec d)}
    (hU : IsOpen U) (h : EqOn f g U) {x : Vec d} (hx : x ∈ U) :
    classicalGradient f x = classicalGradient g x := by
  have hev : f =ᶠ[𝓝 x] g := by
    filter_upwards [hU.mem_nhds hx] with z hz using h hz
  ext i
  simp only [classicalGradient_apply, hev.fderiv_eq]

end

end PDE
