module

public import PDEFoundation.Monotonicity.Defs
public import PDEFoundation.Monotonicity.Core.RellichSphere

/-!
# ACF-S1: smooth slices on spheres

For a `C¹` function `f` and `r > 0`, the classical slice identity
`|∇f(rω)|² = (∇f(rω)·ω)² + r⁻² |∇_θ (f(r·))|²(ω)` on the unit sphere, and the Rayleigh bound
`λ(Ω) ∫ f(r·)² ≤ ∫ |∇_θ (f(r·))|²` on a slice whose nonvanishing set has closure inside `Ω`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

noncomputable section

variable {d : ℕ}

theorem continuous_vecDot_of_continuous {f g : Vec d → Vec d} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => vecDot (f x) (g x) := by
  unfold vecDot
  refine continuous_finsetSum _ fun i _ => ?_
  exact ((continuous_apply i).comp hf).mul ((continuous_apply i).comp hg)

/-- Chain rule for the gradient of a dilation. -/
theorem classicalGradient_comp_smul {f : Vec d → ℝ} (hf : Differentiable ℝ f) (r : ℝ)
    (y : Vec d) :
    classicalGradient (fun z => f (r • z)) y = r • classicalGradient f (r • y) := by
  have h : HasFDerivAt (fun z : Vec d => f (r • z))
      ((fderiv ℝ f (r • y)).comp (r • ContinuousLinearMap.id ℝ (Vec d))) y :=
    (hf (r • y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_smul r)
  funext i
  rw [classicalGradient_apply, h.fderiv]
  simp

/-- Pointwise slice identity (purely algebraic; the unit-sphere condition is not needed). -/
theorem vecNormSq_gradient_eq_radial_add_tangential {f : Vec d → ℝ}
    (hf : Differentiable ℝ f) {r : ℝ} (hr : r ≠ 0) {ω : Vec d} :
    vecNormSq (classicalGradient f (r • ω)) =
      vecDot (classicalGradient f (r • ω)) ω ^ 2 +
        r⁻¹ ^ 2 * tangentialGradientNormSq (fun y => f (r • y)) ω := by
  unfold tangentialGradientNormSq
  rw [classicalGradient_comp_smul hf]
  have h1 : vecNormSq (r • classicalGradient f (r • ω)) =
      r ^ 2 * vecNormSq (classicalGradient f (r • ω)) := vecNormSq_smul _ _
  have h2 : vecDot (r • classicalGradient f (r • ω)) ω =
      r * vecDot (classicalGradient f (r • ω)) ω := by
    unfold vecDot
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp [mul_assoc]
  rw [h1, h2]
  field_simp
  ring

/-- Radial derivative term and squared gradient as functions of the unit-sphere variable. -/
theorem sphereIntegral_gradient_slice {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f) {r : ℝ}
    (hr : r ≠ 0) :
    sphereIntegral (0 : Vec d) 1 (fun y => vecNormSq (classicalGradient f (r • y))) =
      sphereIntegral (0 : Vec d) 1 (fun y => vecDot (classicalGradient f (r • y)) y ^ 2) +
        r⁻¹ ^ 2 * sphereIntegral (0 : Vec d) 1
          (tangentialGradientNormSq (fun y => f (r • y))) := by
  have hgc : Continuous (classicalGradient f) := PDE.ContDiff.continuous_classicalGradient hf
  have hsm : Continuous fun y : Vec d => r • y := continuous_const_smul r
  have hA : Continuous fun y : Vec d => vecNormSq (classicalGradient f (r • y)) :=
    continuous_vecDot_of_continuous (hgc.comp hsm) (hgc.comp hsm)
  have hB : Continuous fun y : Vec d => vecDot (classicalGradient f (r • y)) y ^ 2 :=
    (continuous_vecDot_of_continuous (hgc.comp hsm) continuous_id).pow 2
  have hg1 : ContDiff ℝ 1 fun y : Vec d => f (r • y) := hf.comp (contDiff_const_smul r)
  have hgc1 : Continuous (classicalGradient fun y : Vec d => f (r • y)) :=
    PDE.ContDiff.continuous_classicalGradient hg1
  have hT : Continuous (tangentialGradientNormSq fun y : Vec d => f (r • y)) :=
    (continuous_vecDot_of_continuous hgc1 hgc1).sub
      ((continuous_vecDot_of_continuous hgc1 continuous_id).pow 2)
  have hT' : sphereIntegral (0 : Vec d) 1 (tangentialGradientNormSq fun y => f (r • y)) =
      r ^ 2 * sphereIntegral (0 : Vec d) 1
          (fun y => vecNormSq (classicalGradient f (r • y))) -
        r ^ 2 * sphereIntegral (0 : Vec d) 1
          (fun y => vecDot (classicalGradient f (r • y)) y ^ 2) := by
    rw [← sphereIntegral_zero_sub_const_mul hA.continuousOn hB.continuousOn]
    refine sphereIntegral_zero_congr fun x _ => ?_
    have := vecNormSq_gradient_eq_radial_add_tangential
      (hf.differentiable one_ne_zero) hr (ω := x)
    have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
    rw [this]
    field_simp
    ring
  rw [hT']
  field_simp
  ring

end

end PDE
