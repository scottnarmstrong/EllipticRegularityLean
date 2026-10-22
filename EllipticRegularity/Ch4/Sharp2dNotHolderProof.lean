module

public import EllipticRegularity.Ch4.Meyers.Sharp2d
public import PDEFoundation

/-!
# Proof of `PDE.sharp2d_not_holder` (Proposition 4.27)

-/

@[expose] public section

namespace PDE.Sharp2dNotHolderProof

open MeasureTheory

theorem result (Λ : ℝ) (hΛ : 1 < Λ) (α' : ℝ)
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
        EuclideanHolderSeminormLE (euclideanBall (0 : Vec 2) (1 / 2)) v α' M :=
  PDE.Ch4Meyers.sharp2d_not_holder_full  Λ hΛ α' hα1 hα2 a ha u hu

end PDE.Sharp2dNotHolderProof
