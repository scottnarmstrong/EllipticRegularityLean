module

public import PDEFoundation.Ambient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Sets with `C¹` boundary

The notion of `C¹` boundary used by the
isoperimetric inequality Proposition 1.1.
-/

@[expose] public section

namespace PDE

/-- `E` has `C¹` boundary: near every boundary point, `E` is the strict sublevel set `{φ < 0}`
of a `C¹` function with nowhere-vanishing derivative (equivalently, locally the open epigraph of a
`C¹` graph in rotated coordinates). -/
def HasC1Boundary {d : ℕ} (E : Set (Vec d)) : Prop :=
  ∀ x ∈ frontier E, ∃ W : Set (Vec d), IsOpen W ∧ x ∈ W ∧
    ∃ φ : Vec d → ℝ, ContDiff ℝ 1 φ ∧ (∀ y ∈ W, fderiv ℝ φ y ≠ 0) ∧
      E ∩ W = {y | y ∈ W ∧ φ y < 0}

end PDE
