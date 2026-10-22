module

public import PDEFoundation.Monotonicity.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import PDEFoundation.Sobolev.ClassicalLaplacian
public import PDEFoundation.Monotonicity.Almgren.Equality

/-!
# Proof of `PDE.almgren_monotonicity` (Theorem 2.2)

`PDE.AlmgrenMonotonicityProof.result` combines monotonicity of the frequency
(`monotoneOn_almgrenFrequency`) with the equality case: `N' (r) = 0` iff `u` is a homogeneous
polynomial on `B_R`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE.AlmgrenMonotonicityProof

theorem result (d : ℕ) (hd : 0 < d) (R : ℝ) (hR : 0 < R)
    (u : Vec d → ℝ)
    (hu : ContDiffOn ℝ 2 u (euclideanBall (0 : Vec d) R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0) :
    MonotoneOn (almgrenFrequency u) (Set.Ioo 0 R) ∧
      ∀ r ∈ Set.Ioo 0 R,
        deriv (almgrenFrequency u) r = 0 ↔
          ∃ (k : ℕ) (p : MvPolynomial (Fin d) ℝ), p.IsHomogeneous k ∧
            ∀ x ∈ euclideanBall (0 : Vec d) R, u x = MvPolynomial.eval x p := by
  have _ := hR
  refine ⟨monotoneOn_almgrenFrequency hd hu hharm, fun r hr => ⟨fun h0 => ?_, ?_⟩⟩
  · rcases dichotomy_zero_or_sphereIntegral_sq_pos hd hu hharm with hz | hpos
    · exact ⟨0, 0, MvPolynomial.isHomogeneous_zero _ _ _, fun x hx => by simp [hz x hx]⟩
    · exact exists_homogeneous_of_deriv_almgrenFrequency_eq_zero hd hu hharm hr.1 hr.2 hpos h0
  · rintro ⟨k, p, hp, hup⟩
    exact deriv_almgrenFrequency_eq_zero_of_homogeneous hd hu hharm hr hp hup

end PDE.AlmgrenMonotonicityProof
