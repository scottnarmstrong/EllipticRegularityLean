module

public import PDEFoundation.Sobolev.Trace.NormalSlices
public import PDEFoundation.Sobolev.Trace.SquareTraceProvenance

/-!
# Common provenance for square traces and normal slices

`SquareNormalTraceCertificate` is the exact interface needed when a square
trace construction and the ACL normal-slice construction must be compared.
It retains one common smooth sequence, rather than independently choosing a
sequence for each conclusion.  Thus its endpoint identities are pointwise
identities of canonical uniform limits, while its normal-slice assertions
remain almost-everywhere statements on interior coordinate lines.
-/

@[expose] public section

namespace PDE

open MeasureTheory Set

noncomputable section

/-- A common smooth approximation which simultaneously constructs the four
continuous square-side traces and the canonical normal-slice representatives
on the centered square. -/
structure SquareNormalTraceCertificate
    (F : ℕ → Vec 2 → ℝ) (u : Vec 2 → ℝ) (g : Vec 2 → Vec 2)
    (x₀ : Vec 2) (r : ℝ) : Type where
  radius_pos : 0 < r
  traceProvenance : SquareTraceProvenance F u g x₀ r
  normalSliceData : AxisBoxSmoothApproximationData F u g
    (x₀ 0 - r) (x₀ 0 + r) (x₀ 1 - r) (x₀ 1 + r)

namespace SquareNormalTraceCertificate

/-- Almost every vertical interior coordinate line of the certified square
has the canonical continuous weak normal-slice representative. -/
theorem ae_hasVerticalNormalSliceLimit
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {x₀ : Vec 2} {r : ℝ}
    (C : SquareNormalTraceCertificate F u g x₀ r) :
    ∀ᵐ s ∂(volume.restrict (Ioo (x₀ 0 - r) (x₀ 0 + r))),
      HasVerticalNormalSliceLimit F u g (x₀ 1 - r) (x₀ 1 + r) s := by
  apply ae_hasVerticalNormalSliceLimit_of_summable_dyadic_error
    (a := x₀ 0 - r) (b := x₀ 0 + r)
  · linarith [C.radius_pos]
  · exact C.normalSliceData

/-- Almost every horizontal interior coordinate line of the certified square
has the canonical continuous weak normal-slice representative. -/
theorem ae_hasHorizontalNormalSliceLimit
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {x₀ : Vec 2} {r : ℝ}
    (C : SquareNormalTraceCertificate F u g x₀ r) :
    ∀ᵐ t ∂(volume.restrict (Ioo (x₀ 1 - r) (x₀ 1 + r))),
      HasHorizontalNormalSliceLimit F u g (x₀ 0 - r) (x₀ 0 + r) t := by
  apply ae_hasHorizontalNormalSliceLimit_of_summable_dyadic_error
    (c := x₀ 1 - r) (d := x₀ 1 + r)
  · linarith [C.radius_pos]
  · exact C.normalSliceData

/-- The upper endpoint of any canonical vertical limit is exactly the top
trace supplied by the common sequence. -/
theorem verticalSliceUniformLimit_eq_top
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {x₀ : Vec 2} {r s : ℝ}
    (C : SquareNormalTraceCertificate F u g x₀ r) :
    verticalSliceUniformLimit F s (x₀ 1 + r) = C.traceProvenance.trace.top s :=
  C.traceProvenance.verticalSliceUniformLimit_eq_top

/-- The lower endpoint of any canonical vertical limit is exactly the bottom
trace supplied by the common sequence. -/
theorem verticalSliceUniformLimit_eq_bottom
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {x₀ : Vec 2} {r s : ℝ}
    (C : SquareNormalTraceCertificate F u g x₀ r) :
    verticalSliceUniformLimit F s (x₀ 1 - r) = C.traceProvenance.trace.bottom s :=
  C.traceProvenance.verticalSliceUniformLimit_eq_bottom

/-- The right endpoint of any canonical horizontal limit is exactly the right
trace supplied by the common sequence. -/
theorem horizontalSliceUniformLimit_eq_right
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {x₀ : Vec 2} {r t : ℝ}
    (C : SquareNormalTraceCertificate F u g x₀ r) :
    horizontalSliceUniformLimit F t (x₀ 0 + r) = C.traceProvenance.trace.right t :=
  C.traceProvenance.horizontalSliceUniformLimit_eq_right

/-- The left endpoint of any canonical horizontal limit is exactly the left
trace supplied by the common sequence. -/
theorem horizontalSliceUniformLimit_eq_left
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {x₀ : Vec 2} {r t : ℝ}
    (C : SquareNormalTraceCertificate F u g x₀ r) :
    horizontalSliceUniformLimit F t (x₀ 0 - r) = C.traceProvenance.trace.left t :=
  C.traceProvenance.horizontalSliceUniformLimit_eq_left

end SquareNormalTraceCertificate

end

end PDE
