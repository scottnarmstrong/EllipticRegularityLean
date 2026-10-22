module

public import PDEFoundation

@[expose] public section

namespace PDE

open MeasureTheory

/-- Green function of `-div (a ∇ ·)` in `B_R` with pole at the origin (Definition 4.39).
`G` is measurable, in `L²(B_R \ B_ε)` for `ε ∈ (0,R)`, and for every `g ∈ L²(B_R)` vanishing
a.e. in some `B_ε` and every `H¹₀(B_R)` solution `v` of `-div (aᵗ ∇ v) = g`, the averages of `v`
over `B_ρ(0)` converge as `ρ → 0` to `∫ G g`. -/
def IsGreenFunction {d : ℕ} (a : CoeffField d) (R : ℝ) (G : Vec d → ℝ) : Prop :=
  Measurable G ∧
  (∀ ε : ℝ, 0 < ε → ε < R →
    MemL2On (euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) ε) G) ∧
  ∀ ε : ℝ, 0 < ε → ε < R → ∀ g : Vec d → ℝ,
    MemL2On (euclideanBall (0 : Vec d) R) g →
    (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) ε)), g x = 0) →
    ∀ v : H10Function (euclideanBall (0 : Vec d) R),
      IsWeakDivergenceFormH10SolutionOn (adjointCoeffField a) (euclideanBall (0 : Vec d) R)
        v.toH1Function g (0 : Vec d → Vec d) →
      Filter.Tendsto (fun ρ : ℝ => integralAverage (euclideanBall (0 : Vec d) ρ) v.toH1Function.toFun)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ x in euclideanBall (0 : Vec d) R, G x * g x))

end PDE
