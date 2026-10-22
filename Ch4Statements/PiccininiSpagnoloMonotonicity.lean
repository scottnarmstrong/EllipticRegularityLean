module

public import EllipticRegularity.Ch4.PiccininiSpagnoloMonotonicityProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- Piccinini--Spagnolo monotonicity formula (Theorem 4.24), `d = 2`.
For measurable symmetric `a` with (4.1) and a weak solution `u ∈ H¹(B_1)` of
`-∇·a∇u = 0`, `r ↦ r^{-2/√Λ} ∫_{B_r} ∇u·a∇u` is nondecreasing on `(0,1)`. -/
theorem piccinini_spagnolo_monotonicity (Λ : ℝ) (a : CoeffField 2)
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
      (Set.Ioo 0 1) := by exact PDE.PiccininiSpagnoloMonotonicityProof.result Λ a hmeas hsymm hell u hsol

end PDE
