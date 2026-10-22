module

public import PDEFoundation.Monotonicity.ACF.Interface
public import PDEFoundation.Sobolev.H1.Composition
public import PDEFoundation.Monotonicity.Core.BallDivergence
public import PDEFoundation.Geometry.ConvexDomain

/-!
# The weak gradient of `u²` for a continuous `H¹` function on a ball

If `u ∈ H¹(B_R)` is continuous on `B_R`, then on every smaller ball `B_ρ` it is bounded and
`u²` has weak gradient `2 u ∇u` (weak chain rule applied to a compactly supported `C^∞` function
equal to `t²` on the range of `u`).
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

noncomputable section

variable {d : ℕ}

theorem euclideanBall_zero_subset {ρ R : ℝ} (h : ρ ≤ R) (hρ : 0 ≤ ρ) :
    euclideanBall (0 : Vec d) ρ ⊆ euclideanBall (0 : Vec d) R := by
  intro x hx
  rw [mem_euclideanBall_zero_iff] at hx ⊢
  nlinarith

theorem mem_euclideanClosedBall_zero_iff {x : Vec d} {r : ℝ} :
    x ∈ euclideanClosedBall (0 : Vec d) r ↔ vecNormSq x ≤ r ^ 2 := by
  unfold euclideanClosedBall
  simp only [mem_ofPred_eq, BallDivergence.euclideanSqDist_zero_right]

/-- Congruence of weak gradients on a measurable set. -/
theorem hasWeakGradientOn_congr {U : Set (Vec d)} (hU : MeasurableSet U) {f f' : Vec d → ℝ}
    {g g' : Vec d → Vec d} (hf : ∀ x ∈ U, f x = f' x) (hg : ∀ x ∈ U, g x = g' x)
    (h : HasWeakGradientOn U f g) : HasWeakGradientOn U f' g' := by
  intro i φ hφ hc hs
  have h1 := h i φ hφ hc hs
  have e1 : ∫ x in U, f' x * (fderiv ℝ φ x) (basisVec i) =
      ∫ x in U, f x * (fderiv ℝ φ x) (basisVec i) := by
    refine setIntegral_congr_fun hU fun x hx => ?_
    rw [hf x hx]
  have e2 : ∫ x in U, g' x i * φ x = ∫ x in U, g x i * φ x := by
    refine setIntegral_congr_fun hU fun x hx => ?_
    rw [hg x hx]
  rw [e1, e2]
  exact h1

/-- A smooth compactly supported function that equals `t²` on `[-M, M]` and has bounded
derivative. -/
theorem exists_clamped_square (M : ℝ) :
    ∃ G : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) G ∧ (∃ B : ℝ, ∀ t, |deriv G t| ≤ B) ∧
      ∀ t, |t| < M → G t = t ^ 2 ∧ deriv G t = 2 * t := by
  let b : ContDiffBump (0 : ℝ) := ⟨|M| + 1, |M| + 2, by positivity, by linarith [abs_nonneg M]⟩
  refine ⟨fun t => t ^ 2 * b t, ?_, ?_, ?_⟩
  · exact (contDiff_id.pow 2).mul b.contDiff
  · have hcs : HasCompactSupport (fun t : ℝ => t ^ 2 * b t) :=
      b.hasCompactSupport.mul_left
    have hd : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => t ^ 2 * b t) :=
      (contDiff_id.pow 2).mul b.contDiff
    have hcont : Continuous (deriv fun t : ℝ => t ^ 2 * b t) :=
      hd.continuous_deriv (by simp)
    obtain ⟨B, hB⟩ := (hcont.norm.bounded_above_of_compact_support hcs.deriv.norm)
    exact ⟨B, fun t => by simpa using hB t⟩
  · intro t ht
    have hb : ∀ s, |s| < |M| + 1 → b s = 1 := fun s hs =>
      b.one_of_mem_closedBall (by simpa [Real.dist_eq] using hs.le)
    have hev : (fun s : ℝ => s ^ 2 * b s) =ᶠ[nhds t] fun s => s ^ 2 := by
      have : ∀ᶠ s in nhds t, |s| < |M| + 1 := by
        have hm : |t| < |M| + 1 := lt_of_lt_of_le ht (by linarith [le_abs_self M])
        exact (continuous_abs.continuousAt.eventually (gt_mem_nhds hm))
      filter_upwards [this] with s hs
      rw [hb s hs, mul_one]
    refine ⟨?_, ?_⟩
    · have hm : |t| < |M| + 1 := lt_of_lt_of_le ht (by linarith [le_abs_self M])
      show t ^ 2 * b t = t ^ 2
      rw [hb t hm, mul_one]
    · rw [hev.deriv_eq]
      simp

/-- **Weak gradient of `u²`.** -/
theorem hasWeakGradient_sq_ball {R : ℝ} (u : H1Function (euclideanBall (0 : Vec d) R))
    (hcont : ContinuousOn u.toFun (euclideanBall (0 : Vec d) R)) {ρ : ℝ} (hρ : 0 < ρ)
    (hρR : ρ < R) :
    HasWeakGradientOn (euclideanBall (0 : Vec d) ρ) (fun x => u.toFun x ^ 2)
      (fun x i => 2 * u.toFun x * u.grad x i) := by
  have hR : 0 < R := hρ.trans hρR
  have hsub : euclideanBall (0 : Vec d) ρ ⊆ euclideanBall (0 : Vec d) R :=
    euclideanBall_zero_subset hρR.le hρ.le
  have hclosedsub : euclideanClosedBall (0 : Vec d) ρ ⊆ euclideanBall (0 : Vec d) R := by
    intro x hx
    rw [mem_euclideanClosedBall_zero_iff] at hx
    rw [mem_euclideanBall_zero_iff]
    nlinarith
  obtain ⟨C, hC⟩ := (isCompact_euclideanClosedBall (0 : Vec d) hρ.le).exists_bound_of_continuousOn
    (hcont.mono hclosedsub)
  obtain ⟨G, hG, ⟨B, hB⟩, hGM⟩ := exists_clamped_square (|C| + 1)
  have hUb := isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) hρ
  let u' := u.restrict hUb.isOpen hsub
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have h := H1Function.hasWeakGradient_comp_contDiff_of_deriv_bounded hUb u' (hG.of_le (by simp))
    hB0 hB
  refine hasWeakGradientOn_congr hUb.isOpen.measurableSet ?_ ?_ h
  · intro x hx
    have hx' : |u.toFun x| < |C| + 1 := by
      have := hC x (euclideanBall_subset_euclideanClosedBall (0 : Vec d) ρ hx)
      rw [Real.norm_eq_abs] at this
      linarith [le_abs_self C]
    exact (hGM _ hx').1
  · intro x hx
    have hx' : |u.toFun x| < |C| + 1 := by
      have := hC x (euclideanBall_subset_euclideanClosedBall (0 : Vec d) ρ hx)
      rw [Real.norm_eq_abs] at this
      linarith [le_abs_self C]
    funext i
    show deriv G (u.toFun x) * u.grad x i = 2 * u.toFun x * u.grad x i
    rw [(hGM _ hx').2]

end

end PDE
