module

public import PDEFoundation.Geometry.C1Boundary
public import PDEFoundation.Geometry.EuclideanBall
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Euclidean balls have `C¹` boundary

The defining function `φ(y) = |y - x₀|² - R²` on `W = {y ≠ x₀}` witnesses `HasC1Boundary` for every
Euclidean ball; in particular the hypotheses of `PDE.isoperimetric_inequality` are satisfiable.
-/

@[expose] public section

namespace PDE

/-- Euclidean balls have `C¹` boundary (non-vacuity of the hypothesis of the isoperimetric inequality). -/
theorem hasC1Boundary_euclideanBall {d : ℕ} (x₀ : Vec d) (R : ℝ) : HasC1Boundary (euclideanBall x₀ R) := by
  intro x hx
  set φ : Vec d → ℝ := fun y => euclideanSqDist y x₀ - R ^ 2 with hφ
  have hsm : ContDiff ℝ 1 φ :=
    ((contDiff_euclideanSqDist_left x₀).of_le (by exact_mod_cast le_top)).sub contDiff_const
  refine ⟨{y | y ≠ x₀}, isOpen_ne, ?_, φ, hsm, ?_, ?_⟩
  · intro hx0
    rw [frontier, (isOpen_euclideanBall x₀ R).interior_eq] at hx
    obtain ⟨hcl, hnb⟩ := hx
    have hx0' : x = x₀ := hx0
    subst hx0'
    apply hnb
    rcases eq_or_ne R 0 with hR | hR
    · exfalso
      subst hR
      have : euclideanBall x 0 = ∅ := by
        ext z; simp only [euclideanBall, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        simpa using euclideanSqDist_nonneg z x
      rw [this, closure_empty] at hcl
      exact hcl
    · simp only [euclideanBall, Set.mem_ofPred_eq, euclideanSqDist_self]
      positivity
  · intro y hy h0
    have e : x₀ + (1:ℝ) • (y - x₀) = y := by simp
    have h1 : HasDerivAt (fun t : ℝ => x₀ + t • (y - x₀)) (y - x₀) 1 := by
      have := (hasDerivAt_const_add_iff x₀).2 (HasDerivAt.smul_const (hasDerivAt_id' (1:ℝ)) (y - x₀))
      simpa using this
    have hd : HasDerivAt (fun t : ℝ => φ (x₀ + t • (y - x₀))) (fderiv ℝ φ y (y - x₀)) 1 := by
      have h2 := (((hsm.differentiable (by simp)) (x₀ + (1:ℝ) • (y - x₀))).hasFDerivAt).comp_hasDerivAt (1:ℝ) h1
      rw [e] at h2
      exact h2
    have hfun : (fun t : ℝ => φ (x₀ + t • (y - x₀))) = fun t => t ^ 2 * euclideanSqDist y x₀ - R ^ 2 := by
      funext t
      simp only [hφ, euclideanSqDist]
      have : x₀ + t • (y - x₀) - x₀ = t • (y - x₀) := by abel
      rw [this, vecNormSq_smul]
    rw [hfun] at hd
    have hd2 : HasDerivAt (fun t : ℝ => t ^ 2 * euclideanSqDist y x₀ - R ^ 2) (2 * euclideanSqDist y x₀) 1 := by
      have := (hasDerivAt_sub_const_iff (R^2)).2 (HasDerivAt.mul_const (HasDerivAt.mul (hasDerivAt_id' (1:ℝ)) (hasDerivAt_id' (1:ℝ))) (euclideanSqDist y x₀))
      convert this using 1
      · funext t; simp only [Pi.mul_apply]; ring
      · ring
    have := hd.unique hd2
    simp at this h0
    rw [h0] at this
    have hpos : 0 < euclideanSqDist y x₀ := by
      unfold euclideanSqDist
      rcases (vecNormSq_nonneg (y - x₀)).lt_or_eq with h | h
      · exact h
      · exact absurd (sub_eq_zero.mp (vecNormSq_eq_zero h.symm)) hy
    simp at this
    linarith
  · ext y
    simp only [euclideanBall, hφ, Set.mem_inter_iff, Set.mem_ofPred_eq, sub_neg]
    tauto

end PDE
