module

public import EllipticRegularity.Ch4.MeyersExampleProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- Meyers' example (Proposition 4.26), `d ≥ 2`, `Λ ≥ 1`.
With `α = α(d,Λ)`, `a(x) = I + (Λ-1) x⊗x/|x|²` (`a(0)=I`), `u(x) = |x|^{α-1} x₁` (`u(0)=0`):
(i) `α ∈ (0,1]`, `α=1 ↔ Λ=1`, `α(2,Λ)=Λ^{-1/2}`; (ii) `a` measurable, symmetric, (4.1);
(iii) `u ∈ C(B_1)∩H¹(B_1)` with pointwise gradient, weak solution; (iv) `u(te₁)=t^α`, not `C^{0,α'}`. -/
theorem meyers_example (d : ℕ) (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (α : ℝ)
    (hα : α = (1 / 2) * (-((d : ℝ) - 2) + Real.sqrt (((d : ℝ) - 2) ^ 2 + 4 * ((d : ℝ) - 1) / Λ)))
    (a : CoeffField d)
    (ha : a = fun x => if x = 0 then (1 : Mat d) else
      fun i j => (if i = j then (1 : ℝ) else 0) + (Λ - 1) * x i * x j / vecNormSq x)
    (u : Vec d → ℝ)
    (hu : u = fun x => if x = 0 then 0 else vecEuclideanNorm x ^ (α - 1) * x ⟨0, by omega⟩) :
    (0 < α ∧ α ≤ 1 ∧ (α = 1 ↔ Λ = 1) ∧ (d = 2 → α = Λ ^ (-(1 / 2 : ℝ)))) ∧
    ((∀ i j : Fin d, Measurable (fun x => a x i j)) ∧
      (∀ x : Vec d, ∀ i j : Fin d, a x i j = a x j i) ∧
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x))) ∧
    (ContinuousOn u (euclideanBall (0 : Vec d) 1) ∧
      ∃ v : H1Function (euclideanBall (0 : Vec d) 1), v.toFun = u ∧
        (∀ x ∈ euclideanBall (0 : Vec d) 1, x ≠ 0 →
          ∀ i : Fin d, v.grad x i = fderiv ℝ u x (Pi.single i 1)) ∧
        IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) v
          (0 : Vec d → ℝ) 0) ∧
    ((∀ t : ℝ, 0 < t → t < 1 → u (t • Pi.single ⟨0, by omega⟩ 1) = t ^ α) ∧
      ∀ α' : ℝ, α < α' → ∀ M : ℝ, ∃ t : ℝ, 0 < t ∧ t < 1 / 2 ∧
        M * t ^ α' < |u (t • Pi.single ⟨0, by omega⟩ 1) - u 0|) := by exact PDE.MeyersExampleProof.result d hd Λ hΛ α hα a ha u hu

end PDE
