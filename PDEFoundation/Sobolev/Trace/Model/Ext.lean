module

public import PDEFoundation.Sobolev.Trace.Model.ExtShift

/-!
# The model extension operator (facade)

`modelExt n g (x', t) = χ(t) ∫ t⁻ⁿ ρ((x' - y') / t) g(y') dy'` for `t > 0`, with the mollifier
`extKernel n` and the cutoff `extCutoff`.  The properties established in the `Model/Ext*` modules:

* `modelExt_add`, `modelExt_smul` (`ExtDefs`): linearity,
* `modelExt_eq_zero` (`ExtDefs`): vanishing for `t ≥ 1`,
* `modelExt_contDiffOn` (here): `C¹` on the open upper half-space,
* `modelExt_bound` (`ExtAe`): the `W^{1,p}` energy bound by `‖g‖_p^p + [g]^p`,
* `modelExt_tendsto_boundary` (`ExtBoundary`): `E g(·, τ) → g` in `L^p` as `τ → 0+`,
* `modelExt_tendsto_shift` (`ExtShift`): upward shifts converge in `W^{1,p}` of the half-space.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory

/-- `E g` is `C¹` on the open upper half-space. -/
theorem modelExt_contDiffOn {n : ℕ} {p : ℝ} (hp : 1 < p) (g : Vec n → ℝ)
    (hg : MemLp g (ENNReal.ofReal p) volume) :
    ContDiffOn ℝ 1 (modelExt n g) (upperHalf n) :=
  contDiffOn_modelExt (hg.locallyIntegrable (by simpa using ENNReal.ofReal_le_ofReal hp.le))

end PDE.TraceLane
