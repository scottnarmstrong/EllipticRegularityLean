module

public import PDEFoundation.Sobolev.Inequalities.JohnNirenbergProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- The John–Nirenberg inequality on balls (Proposition 1.17); `M` is any
upper bound for the `BMO(B)` seminorm. -/
theorem exists_johnNirenberg_constant (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : Vec d) (R : ℝ), 0 < R → ∀ (u : Vec d → ℝ) (M : ℝ), 0 < M →
      LocallyIntegrableOn u (euclideanBall x R) volume →
      (∀ (y : Vec d) (r : ℝ), 0 < r → closure (euclideanBall y r) ⊆ euclideanBall x R →
        integralAverage (euclideanBall y r) (fun z => |u z - integralAverage (euclideanBall y r) u|) ≤ M) →
      IntegrableOn u (euclideanBall x R) volume ∧
      ∀ t : ℝ, 0 < t →
        (volume {z ∈ euclideanBall x R | t < |u z - integralAverage (euclideanBall x R) u|}).toReal ≤
          C * Real.exp (-(t / (C * M))) * (volume (euclideanBall x R)).toReal := by exact PDE.JohnNirenbergProof.result d hd

end PDE
