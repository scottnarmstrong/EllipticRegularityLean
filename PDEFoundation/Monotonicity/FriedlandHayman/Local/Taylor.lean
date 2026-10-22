module

public import PDEFoundation.Monotonicity.FriedlandHayman.Local.Moment
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Friedland--Hayman: uniform first-order Taylor expansion on the sphere

For a `C¹` function `f` on `Vec D` and `η > 0` there is `δ > 0` such that for all points `x, y` of
the unit sphere with `|y - x| < δ`,
`|f(y) - f(x) - ⟪∇f(x), y - x⟫| ≤ η |y - x|`.
-/

@[expose] public section

open MeasureTheory Metric

namespace PDE.FHLane

noncomputable section

namespace Local

variable {D : ℕ}

/-- The classical gradient at a point of the sphere, as a `HilbertVec`. -/
def gradH (f : Vec D → ℝ) (x : Sph D) : HilbertVec D :=
  Vec.toHilbertVec (classicalGradient f (x : HilbertVec D).toVec)

theorem taylor_vec {f : Vec D → ℝ} (hf : ContDiff ℝ 1 f) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, δ ≤ 1 ∧ ∀ x y : Vec D, ‖x‖ ≤ 1 → ‖y - x‖ < δ →
      ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ η * ‖y - x‖ := by
  have hUC : UniformContinuousOn (fderiv ℝ f) (closedBall (0 : Vec D) 2) :=
    (isCompact_closedBall (0 : Vec D) 2).uniformContinuousOn_of_continuous
      (hf.continuous_fderiv (by simp)).continuousOn
  obtain ⟨δ₀, hδ₀, hUC⟩ := Metric.uniformContinuousOn_iff.1 hUC η hη
  refine ⟨min δ₀ 1, lt_min hδ₀ one_pos, min_le_right _ _, fun x y hx hxy => ?_⟩
  have hdiff : ∀ z : Vec D, DifferentiableAt ℝ (fun z => f z - fderiv ℝ f x z) z := fun z =>
    (hf.differentiable (by simp) z).sub (fderiv ℝ f x).differentiableAt
  have hfd : ∀ z : Vec D, fderiv ℝ (fun z => f z - fderiv ℝ f x z) z = fderiv ℝ f z - fderiv ℝ f x := by
    intro z
    rw [fderiv_fun_sub (hf.differentiable (by simp) z) (fderiv ℝ f x).differentiableAt,
      ContinuousLinearMap.fderiv]
  have hmem : y ∈ ball x (min δ₀ 1) := by simpa [dist_eq_norm, norm_sub_rev] using hxy
  have hbound : ∀ z ∈ ball x (min δ₀ 1), ‖fderiv ℝ (fun z => f z - fderiv ℝ f x z) z‖ ≤ η := by
    intro z hz
    rw [hfd]
    have hz' : dist z x < min δ₀ 1 := hz
    have h1 : ‖z - x‖ < 1 := by
      have := lt_of_lt_of_le hz' (min_le_right _ _); simpa [dist_eq_norm] using this
    have hzK : z ∈ closedBall (0 : Vec D) 2 := by
      rw [mem_closedBall, dist_zero_right]
      have : ‖z‖ ≤ ‖x‖ + ‖z - x‖ := by
        simpa using norm_add_le x (z - x)
      linarith
    have hxK : x ∈ closedBall (0 : Vec D) 2 := by
      rw [mem_closedBall, dist_zero_right]; linarith
    have := hUC z hzK x hxK (lt_of_lt_of_le hz' (min_le_left _ _))
    rw [dist_eq_norm] at this
    exact this.le
  have := (convex_ball x (min δ₀ 1)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hdiff z) hbound (mem_ball_self (lt_min hδ₀ one_pos)) hmem
  simpa [map_sub, sub_sub, sub_add_eq_sub_sub, add_comm, sub_eq_add_neg, add_assoc,
    add_left_comm] using this

theorem inner_toHilbertVec (a b : Vec D) :
    inner ℝ (Vec.toHilbertVec a) (Vec.toHilbertVec b) = vecDot b a := by
  rw [PiLp.inner_apply]
  simp [vecDot, Vec.toHilbertVec]

theorem taylor_sph {f : Vec D → ℝ} (hf : ContDiff ℝ 1 f) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, δ ≤ 1 ∧ ∀ x y : Sph D, ‖(y : HilbertVec D) - x‖ < δ →
      |f (y : HilbertVec D).toVec - f (x : HilbertVec D).toVec -
          inner ℝ (gradH f x) ((y : HilbertVec D) - x)| ≤ η * ‖(y : HilbertVec D) - x‖ := by
  obtain ⟨δ, hδ, hδ1, h⟩ := taylor_vec hf hη
  refine ⟨δ, hδ, hδ1, fun x y hxy => ?_⟩
  have hnx : ‖(x : HilbertVec D).toVec‖ ≤ 1 := by
    refine (norm_le_vecEuclideanNorm _).trans ?_
    rw [← HilbertVec.norm_eq_vecEuclideanNorm]; simp
  have hdiff : ‖(y : HilbertVec D).toVec - (x : HilbertVec D).toVec‖ ≤
      ‖(y : HilbertVec D) - x‖ := by
    refine (norm_le_vecEuclideanNorm _).trans ?_
    rw [HilbertVec.norm_eq_vecEuclideanNorm]
    exact le_rfl
  have h1 := h _ _ hnx (lt_of_le_of_lt hdiff hxy)
  have h2 : fderiv ℝ f (x : HilbertVec D).toVec ((y : HilbertVec D).toVec - (x : HilbertVec D).toVec)
      = inner ℝ (gradH f x) ((y : HilbertVec D) - x) := by
    rw [fderiv_apply_eq_vecDot_classicalGradient, gradH, vecDot_comm]
    exact (inner_toHilbertVec (classicalGradient f (x : HilbertVec D).toVec)
      ((y : HilbertVec D).toVec - (x : HilbertVec D).toVec)).symm
  rw [h2, Real.norm_eq_abs] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left hdiff hη.le)

end Local

end

end PDE.FHLane
