module

public import EllipticRegularity.Ch4.MeyersSharpnessExampleProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- Sharpness of the Meyers range (Proposition 4.7, parts (i) and (ii)).
For `d ≥ 2`, `Λ > 1`, `β = Λ^{-1/2}`, `p⋆ = 2/(1-β)`: the explicit planar-type symmetric field `a`
satisfies (i) the explicit `u = r^β cos ϑ` is a weak solution in `H¹(B₁)` with `∇u ∈ L^p(B_{1/2})`
iff `p < p⋆`; (ii) with cutoff `χ`, `U = χ u ∈ H¹₀(B₁)` solves `-div a∇U = div f`, `f` bounded,
and `∇U ∉ L^p(B₁)` for `p ≥ p⋆`. -/
theorem meyers_sharpness_example (d : ℕ) (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 < Λ) :
    ∃ a : CoeffField d,
      (∀ (x : Vec d) (i j : Fin d), a x i j =
        (if i = j then 1 else 0) +
          (if i.val < 2 ∧ j.val < 2 ∧ x ⟨0, by omega⟩ ^ 2 + x ⟨1, by omega⟩ ^ 2 ≠ 0 then
            (Λ - 1) * x i * x j / (x ⟨0, by omega⟩ ^ 2 + x ⟨1, by omega⟩ ^ 2) else 0)) ∧
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) ∧
      (∀ x, IsEllipticMatrix 1 Λ (a x)) ∧
      (∀ x i j, a x i j = a x j i) ∧
      -- (i)
      (∃ u : H1Function (euclideanBall (0 : Vec d) 1),
        (∀ x : Vec d, u.toFun x =
          (x ⟨0, by omega⟩ ^ 2 + x ⟨1, by omega⟩ ^ 2) ^ ((1 / Real.sqrt Λ - 1) / 2) *
            x ⟨0, by omega⟩) ∧
        IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u
          (0 : Vec d → ℝ) 0 ∧
        ∀ p : ℝ, 0 < p →
          (MemLp (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
              (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ↔
            p < 2 / (1 - 1 / Real.sqrt Λ))) ∧
      -- (ii)
      (∃ χ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
        tsupport χ ⊆ euclideanBall (0 : Vec d) 1 ∧
        (∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ euclideanBall (0 : Vec d) δ, χ x = 1) ∧
        ∃ f : Vec d → Vec d,
          (∀ i : Fin d, AEStronglyMeasurable (fun x => f x i)
            (volumeOn (euclideanBall (0 : Vec d) 1))) ∧
          (∃ M : ℝ, ∀ x ∈ euclideanBall (0 : Vec d) 1, vecEuclideanNorm (f x) ≤ M) ∧
          ∃ U : H10Function (euclideanBall (0 : Vec d) 1),
            (∀ x : Vec d, U.toFun x = χ x *
              ((x ⟨0, by omega⟩ ^ 2 + x ⟨1, by omega⟩ ^ 2) ^ ((1 / Real.sqrt Λ - 1) / 2) *
                x ⟨0, by omega⟩)) ∧
            IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) U.toH1Function
              (0 : Vec d → ℝ) f ∧
            ∀ p : ℝ, 2 / (1 - 1 / Real.sqrt Λ) ≤ p →
              ¬ MemLp (fun x => vecEuclideanNorm (U.grad x)) (ENNReal.ofReal p)
                (volumeOn (euclideanBall (0 : Vec d) 1))) := by exact PDE.MeyersSharpnessExampleProof.result d hd Λ hΛ

end PDE
