module

public import EllipticRegularity.Guerra.SharpExampleProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- Guerra's explicit example (Proposition 4.30), `d ≥ 3`, `γ ≥ 1`,
`Λ = (80γ)²`, `μ = 2(d-1)γ/sinh(2γ)`, `b = 400γ²`, `α = (√((d-2)²+4μ/b) - (d-2))/2`,
`u(x) = |x|^α tanh(γ x_d/|x|)/tanh γ` (`u(0)=0`). Conclusions: symmetric measurable `a` with
`IsEllipticMatrix 1 Λ` on `B₁`; `u ∈ H¹(B₁)` weak solution (test space `H¹₀`); `0<α≤exp(-√Λ/40)`;
`|u| ≤ |x|^α`; `[u]_{C^{0,α}(B₁)} ≤ 5γ`; `u(s e_d)=s^α`; no representative on any `B_ρ` in
`C^{0,α'}`, `α'>α`; `1+u` is a positive weak solution with exact pointwise sup/inf over the open
`B_{1/2}` (`u` continuous, so these are the essential ones) `1 ± 2^{-α}`, ratio `≥ exp(√Λ/40)`. -/
theorem guerra_sharp_example (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : 1 ≤ γ) (Λ : ℝ)
    (hΛ : Λ = (80 * γ) ^ 2) (α : ℝ)
    (hα : α = (1 / 2) * (Real.sqrt (((d : ℝ) - 2) ^ 2 +
        4 * (2 * ((d : ℝ) - 1) * γ / Real.sinh (2 * γ)) / (400 * γ ^ 2)) - ((d : ℝ) - 2)))
    (u : Vec d → ℝ)
    (hu : u = fun x => if x = 0 then 0 else
      vecEuclideanNorm x ^ α * (Real.tanh (γ * x ⟨d - 1, by omega⟩ / vecEuclideanNorm x) /
        Real.tanh γ)) :
    ∃ a : CoeffField d,
      (∀ i j : Fin d, Measurable (fun x => a x i j)) ∧
      (∀ x : Vec d, ∀ i j : Fin d, a x i j = a x j i) ∧
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) ∧
      (0 < α ∧ α ≤ Real.exp (-(Real.sqrt Λ / 40))) ∧
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
        Real.exp (Real.sqrt Λ / 40) * (1 - (1 / 2 : ℝ) ^ α) ≤ 1 + (1 / 2 : ℝ) ^ α) := by exact PDE.GuerraSharpExampleProof.result d hd γ hγ Λ hΛ α hα u hu

end PDE
