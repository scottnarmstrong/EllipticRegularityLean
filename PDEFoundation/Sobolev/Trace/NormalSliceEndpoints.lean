module

public import PDEFoundation.Sobolev.Trace.NormalSliceCore
public import PDEFoundation.Sobolev.Trace.Square

/-!
# Endpoint provenance for normal coordinate slices

The four identities here are pointwise identities of the *same* smooth
approximants, transported to their canonical uniform-Cauchy limits. They do
not use almost-everywhere slice statements, and consequently do not assert
that a normal weak representative exists on a boundary-coordinate line.
-/

@[expose] public section

namespace PDE

noncomputable section

private theorem uniformCauchySeqLimit_eq_of_forall_eq
    {F G : ℕ → ℝ → ℝ} {s t : ℝ} (h : ∀ n, F n s = G n t) :
    uniformCauchySeqLimit F s = uniformCauchySeqLimit G t := by
  unfold uniformCauchySeqLimit
  congr 1
  funext n
  exact h n

/-- At its upper endpoint, the canonical limit on any vertical coordinate
line is the canonical top-side limit of the same smooth sequence. -/
theorem verticalSliceUniformLimit_eq_topUniformLimit
    (F : ℕ → Vec 2 → ℝ) (x₀ : Vec 2) (r s : ℝ) :
    verticalSliceUniformLimit F s (x₀ 1 + r) =
      squareLoopTopUniformLimit F x₀ r s := by
  apply uniformCauchySeqLimit_eq_of_forall_eq
  intro n
  simp only [verticalSlice, squareLoopTopRestriction]
  congr 1

/-- At its lower endpoint, the canonical limit on any vertical coordinate
line is the canonical bottom-side limit of the same smooth sequence. -/
theorem verticalSliceUniformLimit_eq_bottomUniformLimit
    (F : ℕ → Vec 2 → ℝ) (x₀ : Vec 2) (r s : ℝ) :
    verticalSliceUniformLimit F s (x₀ 1 - r) =
      squareLoopBottomUniformLimit F x₀ r s := by
  apply uniformCauchySeqLimit_eq_of_forall_eq
  intro n
  simp only [verticalSlice, squareLoopBottomRestriction]
  congr 1

/-- At its right endpoint, the canonical limit on any horizontal coordinate
line is the canonical right-side limit of the same smooth sequence. -/
theorem horizontalSliceUniformLimit_eq_rightUniformLimit
    (F : ℕ → Vec 2 → ℝ) (x₀ : Vec 2) (r t : ℝ) :
    horizontalSliceUniformLimit F t (x₀ 0 + r) =
      squareLoopRightUniformLimit F x₀ r t := by
  apply uniformCauchySeqLimit_eq_of_forall_eq
  intro n
  simp only [horizontalSlice, squareLoopRightRestriction]
  congr 1

/-- At its left endpoint, the canonical limit on any horizontal coordinate
line is the canonical left-side limit of the same smooth sequence. -/
theorem horizontalSliceUniformLimit_eq_leftUniformLimit
    (F : ℕ → Vec 2 → ℝ) (x₀ : Vec 2) (r t : ℝ) :
    horizontalSliceUniformLimit F t (x₀ 0 - r) =
      squareLoopLeftUniformLimit F x₀ r t := by
  apply uniformCauchySeqLimit_eq_of_forall_eq
  intro n
  simp only [horizontalSlice, squareLoopLeftRestriction]
  congr 1

end

end PDE
