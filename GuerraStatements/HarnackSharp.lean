module

public import EllipticRegularity.Guerra.HarnackSharpProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- Corollary 4.32, Harnack half, for symmetric coefficients,
`d ≥ 3`, `Λ ≥ 6400`: there is a symmetric measurable `a` with `IsEllipticMatrix 1 Λ` on `B₁` and a
positive continuous weak solution `w ∈ H¹(B₁)` (test space `H¹₀`) whose pointwise sup and inf over
the open `B_{1/2}` (equal to the essential ones by continuity) are finite, `inf > 0`, and satisfy
`sup ≥ exp(√Λ/40) · inf`. -/
theorem guerra_harnack_sharp (d : ℕ) (hd : 3 ≤ d) (Λ : ℝ) (hΛ : 6400 ≤ Λ) :
    ∃ a : CoeffField d,
      (∀ i j : Fin d, Measurable (fun x => a x i j)) ∧
      (∀ x : Vec d, ∀ i j : Fin d, a x i j = a x j i) ∧
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) ∧
      ∃ w : H1Function (euclideanBall (0 : Vec d) 1),
        ContinuousOn w.toFun (euclideanBall (0 : Vec d) 1) ∧
        (∀ x ∈ euclideanBall (0 : Vec d) 1, 0 < w.toFun x) ∧
        IsWeakDivergenceFormH10SolutionOn a (euclideanBall (0 : Vec d) 1) w
          (0 : Vec d → ℝ) 0 ∧
        ∃ M m : ℝ, IsLUB (w.toFun '' euclideanBall (0 : Vec d) (1 / 2)) M ∧
          IsGLB (w.toFun '' euclideanBall (0 : Vec d) (1 / 2)) m ∧ 0 < m ∧
          Real.exp (Real.sqrt Λ / 40) * m ≤ M := by exact PDE.GuerraHarnackSharpProof.result d hd Λ hΛ

end PDE
