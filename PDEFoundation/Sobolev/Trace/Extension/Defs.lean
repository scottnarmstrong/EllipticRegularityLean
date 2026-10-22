module

public import PDEFoundation.Sobolev.Trace.Extension.Flat
public import PDEFoundation.Sobolev.Trace.Model.ExtDefs

/-!
# The extension operator on `Ω`: construction

Given a trace atlas (charts `φⱼ`, partition `ζⱼ` near `∂Ω`) and cutoffs `ηⱼ` with compact support in
the chart cylinders and `ηⱼ = 1` on `tsupport ζⱼ`, the extension of a boundary function `g` is
`E g (x) = ∑ⱼ ηⱼ(x) · (modelExt n gⱼ)(φⱼ⁻¹ x)`, `gⱼ = flatPullback φⱼ ζⱼ g`, and its upward shifts
`∑ⱼ ηⱼ(x) · (modelExt n gⱼ)(φⱼ⁻¹ x + (0, τ))` serve as `C¹(Ω̄)` approximants.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

/-- Extension data: a trace atlas and cutoffs equal to one on the partition supports. -/
structure ExtData (Ω : Set (Vec (n + 1))) where
  A : TraceAtlas Ω
  η : Fin A.N → Vec (n + 1) → ℝ
  η_smooth : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (η j)
  η_compact : ∀ j, HasCompactSupport (η j)
  η_tsupport : ∀ j, tsupport (η j) ⊆ (A.chart j).dom
  η_one : ∀ j x, x ∈ tsupport (A.ζ j) → η j x = 1

/-- The flat boundary data of chart `j`. -/
noncomputable def ExtData.flat (D : ExtData Ω) (j : Fin D.A.N) (g : Vec (n + 1) → ℝ) :
    Vec n → ℝ :=
  flatPullback (D.A.chart j) (D.A.ζ j) g

/-- The extension `E g` (as a function on `Vec (n+1)`). -/
noncomputable def ExtData.ext (D : ExtData Ω) (g : Vec (n + 1) → ℝ) (x : Vec (n + 1)) : ℝ :=
  ∑ j, D.η j x * modelExt n (D.flat j g) ((D.A.chart j).inv x)

/-- The upward shift of the extension by `τ`. -/
noncomputable def ExtData.shift (D : ExtData Ω) (τ : ℝ) (g : Vec (n + 1) → ℝ)
    (x : Vec (n + 1)) : ℝ :=
  ∑ j, D.η j x * modelExt n (D.flat j g) ((D.A.chart j).inv x + (0, τ))

end PDE.TraceLane
