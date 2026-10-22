module

public import EllipticRegularity.Ch4.Sharp2dNotHolderProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- Sharpness of the exponent in `d = 2` (Proposition 4.27(ii)).
For `Λ > 1`, `α' ∈ (Λ^{-1/2}, 1]`, the Meyers pair (`d=2`, `α = Λ^{-1/2}`) satisfies the
hypotheses of (i) but has no representative in `C^{0,α'}(B_{1/2})`. -/
theorem sharp2d_not_holder (Λ : ℝ) (hΛ : 1 < Λ) (α' : ℝ)
    (hα1 : Λ ^ (-(1 / 2 : ℝ)) < α') (hα2 : α' ≤ 1)
    (a : CoeffField 2)
    (ha : a = fun x => if x = 0 then (1 : Mat 2) else
      fun i j => (if i = j then (1 : ℝ) else 0) + (Λ - 1) * x i * x j / vecNormSq x)
    (u : Vec 2 → ℝ)
    (hu : u = fun x => if x = 0 then 0 else
      vecEuclideanNorm x ^ (Λ ^ (-(1 / 2 : ℝ)) - 1) * x 0) :
    ((∀ i j : Fin 2, AEMeasurable (fun x => a x i j)
        (volumeOn (euclideanBall (0 : Vec 2) 1))) ∧
      (∀ x ∈ euclideanBall (0 : Vec 2) 1, ∀ i j : Fin 2, a x i j = a x j i) ∧
      (∀ x ∈ euclideanBall (0 : Vec 2) 1, IsEllipticMatrix 1 Λ (a x)) ∧
      ∃ v : H1Function (euclideanBall (0 : Vec 2) 1), v.toFun = u ∧
        IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec 2) 1) v
          (0 : Vec 2 → ℝ) 0) ∧
    ¬ ∃ (v : Vec 2 → ℝ) (M : ℝ), v =ᵐ[volumeOn (euclideanBall (0 : Vec 2) (1 / 2))] u ∧
        EuclideanHolderSeminormLE (euclideanBall (0 : Vec 2) (1 / 2)) v α' M := by exact PDE.Sharp2dNotHolderProof.result Λ hΛ α' hα1 hα2 a ha u hu

end PDE
