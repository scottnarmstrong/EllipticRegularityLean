module

public import PDEFoundation

@[expose] public section

namespace PDE

open MeasureTheory

/-- Pointwise derivative bounds and real analyticity for harmonic functions
(Proposition 2.1). -/
theorem exists_harmonic_pointwise_derivative_bound
    (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (r : ℝ), 0 < r →
      ∀ (u : H1Function (euclideanBall (0 : Vec d) r)),
      IsWeakDivergenceFormSolutionOn (fun _ => (1 : Mat d))
          (euclideanBall (0 : Vec d) r) u (0 : Vec d → ℝ)
          (0 : Vec d → Vec d) →
      ∃ v : Vec d → ℝ,
        AnalyticOnNhd ℝ v (euclideanBall (0 : Vec d) r) ∧
        (∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) r), v x = u.toFun x) ∧
        ∀ m : ℕ, 1 ≤ m →
          Real.sqrt (∑ ι : Fin m → Fin d,
              (iteratedFDeriv ℝ m v 0 (fun k => Pi.single (ι k) 1)) ^ 2) ≤
            (C * m / r) ^ m *
              Real.sqrt (integralAverage (euclideanBall (0 : Vec d) r)
                (fun x => (u.toFun x -
                  integralAverage (euclideanBall (0 : Vec d) r) u.toFun) ^ 2)) := by exact PDE.HarmonicPointwiseProof.result d hd

end PDE
