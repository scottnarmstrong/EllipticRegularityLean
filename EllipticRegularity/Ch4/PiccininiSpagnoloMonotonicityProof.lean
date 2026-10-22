module

public import EllipticRegularity.Ch4.Spagnolo.Monotonicity
public import Ch4Statements.WirtingerInequality
public import PDEFoundation

/-!
# Proof of `PDE.piccinini_spagnolo_monotonicity` (Theorem 4.24)

-/

@[expose] public section

namespace PDE.PiccininiSpagnoloMonotonicityProof

open MeasureTheory

theorem result (Λ : ℝ) (a : CoeffField 2)
    (hmeas : ∀ i j : Fin 2, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec 2) 1)))
    (hsymm : ∀ x ∈ euclideanBall (0 : Vec 2) 1, ∀ i j : Fin 2, a x i j = a x j i)
    (hell : ∀ x ∈ euclideanBall (0 : Vec 2) 1, IsEllipticMatrix 1 Λ (a x))
    (u : H1Function (euclideanBall (0 : Vec 2) 1))
    (hsol : IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec 2) 1) u
      (0 : Vec 2 → ℝ) 0) :
    MonotoneOn
      (fun r : ℝ => r ^ (-(2 / Real.sqrt Λ)) *
        ∫ x in euclideanBall (0 : Vec 2) r, vecDot (u.grad x) (matVecMul (a x) (u.grad x)))
      (Set.Ioo 0 1) :=
  PDE.Ch4Spagnolo.piccinini_spagnolo_monotonicity_full (fun w h1 h2 h3 => PDE.wirtinger_inequality w h1 h2 h3) Λ a hmeas hsymm hell u hsol

end PDE.PiccininiSpagnoloMonotonicityProof
