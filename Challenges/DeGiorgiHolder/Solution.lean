module

public import EllipticRegularity.DeGiorgi.DeGiorgiHolderProof

@[expose] public section

open scoped BigOperators ENNReal

namespace PDE

open MeasureTheory

/-- De Giorgi's interior Hölder estimate (Theorem 4.8).  For `d ≥ 3` there is `C > 0`, depending only on `d`,
such that for every `Λ ≥ 1` there is an exponent `α ∈ (0, 1]` with `exp (-C Λ^{(d+2)/4}) ≤ α` such that for every
measurable coefficient field `a` on `B₁` with `IsEllipticMatrix 1 Λ (a x)` on `B₁` and every weak solution
`u ∈ H¹(B₁)` of `-div (a ∇u) = 0`, there is a representative `v` of `u` on `B_{1/2}` with `|v| ≤ M₀` and
Hölder seminorm at most `M₁` (exponent `α`) on `B_{1/2}`, where `M₀ + M₁ ≤ C Λ^{d/4} ‖u‖_{L²(B₁)}`. -/
theorem exists_deGiorgi_holder_constant (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧
      Real.exp (-(C * Λ ^ (((d : ℝ) + 2) / 4))) ≤ α ∧
      ∀ (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u (0 : Vec d → ℝ) 0 →
        ∃ (v : Vec d → ℝ) (M₀ M₁ : ℝ), v =ᵐ[volumeOn (euclideanBall (0 : Vec d) (1 / 2))] u.toFun ∧
          0 ≤ M₀ ∧ 0 ≤ M₁ ∧ (∀ x ∈ euclideanBall (0 : Vec d) (1 / 2), |v x| ≤ M₀) ∧
          EuclideanHolderSeminormLE (euclideanBall (0 : Vec d) (1 / 2)) v α M₁ ∧
          ENNReal.ofReal (M₀ + M₁) ≤ ENNReal.ofReal (C * Λ ^ ((d : ℝ) / 4)) *
            eLpNorm u.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1)) :=
  PDE.DeGiorgiHolderProof.result d hd

end PDE
