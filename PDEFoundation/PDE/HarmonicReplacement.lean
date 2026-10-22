module

public import PDEFoundation.Sobolev.H1.GraphPairing
public import PDEFoundation.Sobolev.H1.ZeroBoundaryRepresentative
public import PDEFoundation.Sobolev.Inequalities.ZeroBoundaryBall

/-!
# Dirichlet harmonic replacement on native round balls

The round-ball Poincaré inequality discharges the closed-gradient projection
construction. The resulting harmonic function has the original boundary
class, witnessed by an actual member of the existing `H10Function` carrier.
Its gradient energy is at most the original gradient energy, with constant one.
-/

@[expose] public section

open scoped ENNReal RealInnerProductSpace

namespace PDE

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The scalar component of every zero-boundary graph on a round ball is
controlled by its gradient, with explicit constant `2R`. -/
theorem h10Graph_value_norm_le_two_mul_radius_gradient_norm
    (hd : 0 < d) {z : Vec d} {R : ℝ} (hR : 0 < R)
    (w : H10Graph (isOpen_euclideanBall z R)) :
    ‖w.1.1.1‖ ≤ (2 * R) * ‖h10GradientCLM (isOpen_euclideanBall z R) w‖ := by
  obtain ⟨v, hv⟩ := H10Graph.exists_toH10Function (isOpen_euclideanBall z R) w
  have hp := h10_setIntegral_sq_le_four_mul_radius_sq_setIntegral_vecNormSq_grad_on_euclideanBall
    hd hR v
  rw [v.toH1Function.setIntegral_sq_toFun_eq_norm_sq,
    v.toH1Function.setIntegral_vecNormSq_grad_eq_norm_sq] at hp
  rw [← hv]
  change ‖v.toH1Function.toW1pFunction.toW1pGraph.1.1‖ ≤
    (2 * R) * ‖h1GradientCLM v.toH1Function.toW1pFunction.toW1pGraph‖
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) (norm_nonneg _))).mp
  simpa only [mul_pow] using hp

/-- Harmonic replacement with an actual zero-boundary difference and the
exact constant-one Dirichlet energy comparison. No analytic precursor is
assumed by this theorem. -/
theorem exists_harmonicReplacement_on_euclideanBall
    (hd : 0 < d) {z : Vec d} {R : ℝ} (hR : 0 < R)
    (u : H1Function (euclideanBall z R)) :
    ∃ h : H1Function (euclideanBall z R),
      ∃ w : H10Function (euclideanBall z R),
        h.toFun = (fun x => u.toFun x - w.toH1Function.toFun x) ∧
        h.grad = (fun x => u.grad x - w.toH1Function.grad x) ∧
        (∀ v : H10Function (euclideanBall z R),
          ∫ x in euclideanBall z R, vecDot (h.grad x) (v.toH1Function.grad x) = 0) ∧
        (∫ x in euclideanBall z R, vecNormSq (h.grad x)) ≤
          ∫ x in euclideanBall z R, vecNormSq (u.grad x) := by
  let hU := isOpen_euclideanBall z R
  obtain ⟨wG, horth, henergy⟩ := exists_harmonicReplacement_graph hU
    (h10Graph_value_norm_le_two_mul_radius_gradient_norm hd hR)
    u.toW1pFunction.toW1pGraph
  obtain ⟨w, hw⟩ := H10Graph.exists_toH10Function hU wG
  let h := u - w.toH1Function
  have hgraph : h.toW1pFunction.toW1pGraph =
      u.toW1pFunction.toW1pGraph - wG.1 := by
    rw [H1Function.toW1pGraph_sub]
    have hw' := congrArg Subtype.val hw
    exact congrArg (fun q => u.toW1pFunction.toW1pGraph - q) hw'
  refine ⟨h, w, rfl, rfl, ?_, ?_⟩
  · intro v
    rw [H1Function.setIntegral_vecDot_grad_eq_inner, hgraph]
    exact horth (v.toH10Graph hU)
  · rw [h.setIntegral_vecNormSq_grad_eq_norm_sq,
      u.setIntegral_vecNormSq_grad_eq_norm_sq, hgraph]
    exact pow_le_pow_left₀ (norm_nonneg _) henergy 2

end

end PDE
