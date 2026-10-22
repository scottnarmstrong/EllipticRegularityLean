module

public import EllipticRegularity.Parabolic.ParabolicDef

/-!
# Definition module for the Cauchy problem layer of Section 5.3

Energy solutions of `∂ₜu - ∇·(a∇u) = 0` on `ℝ^d × [s,T]` with initial datum `f ∈ L²(ℝ^d)`.
Reuses `ParH1Function` / `IsParabolicWeakSolution` of `ParabolicDef` with `U = univ` and the
*closed* bounded interval `I = Icc s T`: a finite horizon is forced because `u ∈ L²(ℝ^d × I)`
fails on `[s,∞)` in low dimension, and the closed endpoint makes `weakCont` (weak continuity on `I`)
control `u(s)`.  The initial condition is `u(·,s) = f` a.e. (every-time slice at `s`).
Test functions are `C¹_c(ℝ^d × (s,T))` (interior of `I`), so no boundary term enters the weak
formulation; the datum is carried entirely by `weakCont` and `initial`.

The backward adjoint problem is not given its own class: by the reflection `τ ↦ s + t - τ` a
backward solution on `[s,t]` with terminal datum `g` at `t` is a *forward* solution for
`parAdjCoeff a (s + t)` with datum `g`; its value at the final time `t` is the adjoint evolution
at time `s`.
-/

@[expose] public section

namespace PDE

open MeasureTheory Set

/-- Reversed-time transposed coefficients `ã(x,τ) = a(x, c - τ)ᵀ` (use `c = s + t`). -/
def parAdjCoeff {d : ℕ} (a : ParCoeffField d) (c : ℝ) : ParCoeffField d :=
  fun z => Matrix.transpose (a (z.1, c - z.2))

/-- `u` is an energy solution of the Cauchy problem on `ℝ^d × [s,T]` with datum `f` at time `s`:
a weak solution in `H¹_par(ℝ^d × [s,T])` whose every-time slice at `s` is `f` a.e. -/
def IsCauchySolution {d : ℕ} (a : ParCoeffField d) (s T : ℝ) (f : Vec d → ℝ)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T)) : Prop :=
  IsParabolicWeakSolution a univ (Icc s T) u ∧ ∀ᵐ x : Vec d, u.toFun (x, s) = f x

end PDE
