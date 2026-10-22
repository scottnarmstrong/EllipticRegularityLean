module

public import EllipticRegularity.Ch4.HarnackConstantGeOneProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- The constant `1 ≤ C` in `sup ≤ exp(C √Λ) inf` (Proposition 4.20, last
sentence; `d ≥ 2`): if the Harnack inequality holds with `exp(C √Λ)` for every `Λ ≥ 1`, then
`C ≥ 1`. -/
theorem harnack_constant_ge_one (d : ℕ) (hd : 2 ≤ d) (C : ℝ)
    (h : ∀ Λ : ℝ, 1 ≤ Λ → ∀ a : CoeffField d,
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j)
        (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ v : H1Function (euclideanBall (0 : Vec d) 1),
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 < v.toFun x) →
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) v (0 : Vec d → ℝ) 0 →
        essSup (fun x => ENNReal.ofReal (v.toFun x))
            (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
          ENNReal.ofReal (Real.exp (C * Real.sqrt Λ)) *
            essInf (fun x => ENNReal.ofReal (v.toFun x))
              (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) :
    1 ≤ C := by exact PDE.HarnackConstantGeOneProof.result d hd C h

end PDE
