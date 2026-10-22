module

public import PDEFoundation.Monotonicity.Core.FrequencyMono
public import PDEFoundation.Monotonicity.Core.Dichotomy

/-!
# Chapter 2: monotonicity of the Almgren frequency

For `u` of class `C²` and harmonic on `B_R ⊆ ℝᵈ` (`d ≥ 1`), `r ↦ almgrenFrequency u r` is
monotone nondecreasing on `(0, R)`: by the dichotomy either `u ≡ 0` (frequency identically `0`)
or `H > 0` on `(0, R)`, where the derivative is nonnegative.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

noncomputable section

variable {d : ℕ}

/-- Monotonicity from the dichotomy as an explicit hypothesis. -/
theorem monotoneOn_almgrenFrequency_of_dichotomy (hd : 0 < d) {u : Vec d → ℝ} {R : ℝ}
    (hu : ContDiffOn ℝ 2 u (euclideanBall 0 R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0)
    (hdich : (∀ x ∈ euclideanBall (0 : Vec d) R, u x = 0) ∨
      ∀ r ∈ Ioo (0 : ℝ) R, 0 < sphereIntegral 0 r (fun x => u x ^ 2)) :
    MonotoneOn (almgrenFrequency u) (Ioo 0 R) := by
  rcases hdich with h | h
  · intro a ha b hb _
    rw [almgrenFrequency_eq_zero_of_eqOn_zero h ha, almgrenFrequency_eq_zero_of_eqOn_zero h hb]
  · refine monotoneOn_of_deriv_nonneg (convex_Ioo 0 R) ?_ ?_ ?_
    · exact fun r hr => (hasDerivAt_almgrenFrequency_of_pos hd hu hharm hr.1 hr.2
        (h r hr)).continuousAt.continuousWithinAt
    · rw [interior_Ioo]
      exact fun r hr => (hasDerivAt_almgrenFrequency_of_pos hd hu hharm hr.1 hr.2
        (h r hr)).differentiableAt.differentiableWithinAt
    · rw [interior_Ioo]
      exact fun r hr => deriv_almgrenFrequency_nonneg hd hu hharm hr.1 hr.2 (h r hr)

/-- **Monotonicity of the Almgren frequency** on `(0, R)`. -/
theorem monotoneOn_almgrenFrequency (hd : 0 < d) {u : Vec d → ℝ} {R : ℝ}
    (hu : ContDiffOn ℝ 2 u (euclideanBall 0 R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0) :
    MonotoneOn (almgrenFrequency u) (Ioo 0 R) :=
  monotoneOn_almgrenFrequency_of_dichotomy hd hu hharm
    (dichotomy_zero_or_sphereIntegral_sq_pos hd hu hharm)

end

end PDE

