module

public import EllipticRegularity.Guerra.SharpExampleNonsymmetricProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- Nonsymmetric version (Remark after Corollary 4.32): `a = 2B`, `Λ = (40γ)²
= 1600γ²`, threshold `Λ ≥ 1600`, exponent `α ≤ exp(-√Λ/20)`, Harnack ratio `≥ exp(√Λ/20)`.
Same `α` (a function of `d, γ` only) and same `u` as `guerra_sharp_example`. No symmetry claimed. -/
theorem guerra_sharp_example_nonsymmetric (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : 1 ≤ γ) (Λ : ℝ)
    (hΛ : Λ = (40 * γ) ^ 2) (α : ℝ)
    (hα : α = (1 / 2) * (Real.sqrt (((d : ℝ) - 2) ^ 2 +
        4 * (2 * ((d : ℝ) - 1) * γ / Real.sinh (2 * γ)) / (400 * γ ^ 2)) - ((d : ℝ) - 2)))
    (u : Vec d → ℝ)
    (hu : u = fun x => if x = 0 then 0 else
      vecEuclideanNorm x ^ α * (Real.tanh (γ * x ⟨d - 1, by omega⟩ / vecEuclideanNorm x) /
        Real.tanh γ)) :
    ∃ a : CoeffField d,
      (∀ i j : Fin d, Measurable (fun x => a x i j)) ∧
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) ∧
      (0 < α ∧ α ≤ Real.exp (-(Real.sqrt Λ / 20))) ∧
      (ContinuousOn u (euclideanBall (0 : Vec d) 1) ∧
        (∀ x ∈ euclideanBall (0 : Vec d) 1, |u x| ≤ vecEuclideanNorm x ^ α) ∧
        (∀ s : ℝ, 0 < s → s < 1 → u (s • Pi.single ⟨d - 1, by omega⟩ 1) = s ^ α) ∧
        EuclideanHolderSeminormLE (euclideanBall (0 : Vec d) 1) u α (5 * γ)) ∧
      (∃ v : H1Function (euclideanBall (0 : Vec d) 1), v.toFun = u ∧
        IsWeakDivergenceFormH10SolutionOn a (euclideanBall (0 : Vec d) 1) v
          (0 : Vec d → ℝ) 0) ∧
      (∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∀ α' : ℝ, α < α' →
        ¬ ∃ (v : Vec d → ℝ) (M : ℝ), v =ᵐ[volumeOn (euclideanBall (0 : Vec d) ρ)] u ∧
          EuclideanHolderSeminormLE (euclideanBall (0 : Vec d) ρ) v α' M) ∧
      (∃ w : H1Function (euclideanBall (0 : Vec d) 1), w.toFun = (fun x => 1 + u x) ∧
        (∀ x ∈ euclideanBall (0 : Vec d) 1, 0 < w.toFun x) ∧
        IsWeakDivergenceFormH10SolutionOn a (euclideanBall (0 : Vec d) 1) w
          (0 : Vec d → ℝ) 0 ∧
        IsLUB (w.toFun '' euclideanBall (0 : Vec d) (1 / 2)) (1 + (1 / 2 : ℝ) ^ α) ∧
        IsGLB (w.toFun '' euclideanBall (0 : Vec d) (1 / 2)) (1 - (1 / 2 : ℝ) ^ α) ∧
        Real.exp (Real.sqrt Λ / 20) * (1 - (1 / 2 : ℝ) ^ α) ≤ 1 + (1 / 2 : ℝ) ^ α) := by exact PDE.GuerraSharpExampleNonsymmetricProof.result d hd γ hγ Λ hΛ α hα u hu

end PDE
