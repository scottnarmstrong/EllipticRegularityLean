module

public import PDEFoundation.PDE.HarmonicPointwiseAssembly
public import PDEFoundation.PDE.HarmonicWeylRepresentative

/-!
# The harmonic pointwise derivative bound

Proposition 2.1: a weakly harmonic `H¹` function on a
round ball has a real-analytic representative whose `m`-th derivative
tensor at the center satisfies the sharp `(C m / r)^m` bound. The
representative comes from Weyl smoothing; the estimates come from the
assembly theorem.
-/

@[expose] public section

namespace PDE.HarmonicPointwiseProof

open MeasureTheory

theorem result
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
                  integralAverage (euclideanBall (0 : Vec d) r) u.toFun) ^ 2)) := by
  refine ⟨harmonicPointwiseConst d, harmonicPointwiseConst_pos hd, ?_⟩
  intro r hr u hsol
  obtain ⟨v, hv, hharm, hae, -⟩ := exists_harmonicWeylRepresentative hd hr u hsol
  obtain ⟨hanalytic, hbound⟩ := harmonicPointwise_of_representative hd hr u hv hharm hae
  exact ⟨v, hanalytic, hae, hbound⟩

end PDE.HarmonicPointwiseProof
