module

public import PDEFoundation.Sobolev.Trace.NormalSliceEndpoints

/-!
# Common-sequence provenance for square traces

`SquareSideTrace` deliberately records only the resulting one-dimensional
trace data. This companion certificate retains the common planar smooth
sequence that produced those traces. In particular, it gives exact endpoint
identities between normal-slice canonical limits and the four side traces; it
does not promote almost-everywhere normal-slice assertions to boundary lines.
-/

@[expose] public section

namespace PDE

noncomputable section

/-- A four-side trace together with the exact common smooth sequence whose
canonical uniform limits are its four sides. -/
structure SquareTraceProvenance
    (F : ℕ → Vec 2 → ℝ) (u : Vec 2 → ℝ) (g : Vec 2 → Vec 2)
    (x₀ : Vec 2) (r : ℝ) : Type where
  trace : SquareSideTrace u g x₀ r
  right_eq : trace.right = squareLoopRightUniformLimit F x₀ r
  left_eq : trace.left = squareLoopLeftUniformLimit F x₀ r
  top_eq : trace.top = squareLoopTopUniformLimit F x₀ r
  bottom_eq : trace.bottom = squareLoopBottomUniformLimit F x₀ r

namespace SquareTraceProvenance

/-- The upper endpoint of a vertical canonical slice is the supplied top
trace. This is a common-sequence identity and needs no assertion about the
boundary coordinate being a good normal slice. -/
theorem verticalSliceUniformLimit_eq_top
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {x₀ : Vec 2} {r s : ℝ}
    (T : SquareTraceProvenance F u g x₀ r) :
    verticalSliceUniformLimit F s (x₀ 1 + r) = T.trace.top s := by
  rw [verticalSliceUniformLimit_eq_topUniformLimit, ← T.top_eq]

/-- The lower endpoint of a vertical canonical slice is the supplied bottom
trace. -/
theorem verticalSliceUniformLimit_eq_bottom
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {x₀ : Vec 2} {r s : ℝ}
    (T : SquareTraceProvenance F u g x₀ r) :
    verticalSliceUniformLimit F s (x₀ 1 - r) = T.trace.bottom s := by
  rw [verticalSliceUniformLimit_eq_bottomUniformLimit, ← T.bottom_eq]

/-- The right endpoint of a horizontal canonical slice is the supplied right
trace. -/
theorem horizontalSliceUniformLimit_eq_right
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {x₀ : Vec 2} {r t : ℝ}
    (T : SquareTraceProvenance F u g x₀ r) :
    horizontalSliceUniformLimit F t (x₀ 0 + r) = T.trace.right t := by
  rw [horizontalSliceUniformLimit_eq_rightUniformLimit, ← T.right_eq]

/-- The left endpoint of a horizontal canonical slice is the supplied left
trace. -/
theorem horizontalSliceUniformLimit_eq_left
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {x₀ : Vec 2} {r t : ℝ}
    (T : SquareTraceProvenance F u g x₀ r) :
    horizontalSliceUniformLimit F t (x₀ 0 - r) = T.trace.left t := by
  rw [horizontalSliceUniformLimit_eq_leftUniformLimit, ← T.left_eq]

end SquareTraceProvenance

end

end PDE
