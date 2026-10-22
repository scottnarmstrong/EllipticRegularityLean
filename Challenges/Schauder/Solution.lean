module

public import EllipticRegularity.Schauder.CalphaProof

@[expose] public section

open scoped ENNReal NNReal

namespace PDE

open MeasureTheory

/-- The `C^{0,1-}` Schauder estimate (Proposition 3.1).  For `d ≥ 1` there is `C = C(d) > 0` such
that for every `α ∈ (0,1)`, every measurable coefficient field `a` on `B₁` within distance
`2^{-3-d/2} (1-α)` of the identity, every `F ∈ L^{d/(1-α)}(B₁)`, and every weak solution
`u ∈ H¹(B₁)` of `-div (a ∇u) = div F`, the function `u` has a Hölder representative on `B_{1/2}`
with seminorm at most `(C/α) (‖∇u‖_{L²(B₁)} + (1-α)⁻¹ ‖F‖_{L^{d/(1-α)}(B₁)})`. -/
theorem exists_schauderCalpha_constant {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ}, 0 < α → α < 1 →
      ∀ {a : CoeffField d} (u : H1Function (euclideanBall (0 : Vec d) 1))
        {F : Vec d → Vec d},
      (∀ i j, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
        IsMatrixPerturbationLE ((2 : ℝ) ^ (-3 - (d : ℝ) / 2) * (1 - α)) (a x) 1) →
      (∀ i : Fin d, AEStronglyMeasurable (fun x => F x i)
        (volumeOn (euclideanBall (0 : Vec d) 1))) →
      ∀ hF : MemLp (fun x => vecEuclideanNorm (F x))
        (ENNReal.ofReal ((d : ℝ) / (1 - α))) (volumeOn (euclideanBall (0 : Vec d) 1)),
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u 0 F →
      HasEuclideanHolderRepresentativeOn (euclideanBall (0 : Vec d) (1 / 2)) u.toFun α
        ((C / α) * (Real.sqrt (∫ x in euclideanBall (0 : Vec d) 1, vecNormSq (u.grad x)) +
          euclideanFieldLpNormOn (euclideanBall (0 : Vec d) 1)
            (ENNReal.ofReal ((d : ℝ) / (1 - α))) F hF / (1 - α)))  :=
  PDE.SchauderCalphaProof.result hd

end PDE
