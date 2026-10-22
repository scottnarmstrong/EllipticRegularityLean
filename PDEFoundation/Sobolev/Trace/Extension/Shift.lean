module

public import PDEFoundation.Sobolev.Trace.Extension.ShiftSmooth
public import PDEFoundation.Sobolev.Trace.Extension.ShiftBoundary
public import PDEFoundation.Sobolev.Trace.Extension.ShiftW1p

/-!
# Upward shifts of the extension: `C¹(Ω̄)` approximants

Facade for the shifted extensions `D.shift τ g`: they are `C¹` on `Ω̄` for `τ > 0`
(`ExtData.shift_contDiffOn`), converge to `D.ext g` in `W^{1,p}(Ω)` along `τ = 1/(k+1)`
(`ExtData.tendsto_shift_w1p`) and converge to `g` in `L^p(∂Ω)` (`ExtData.tendsto_shift_boundary`).
-/

@[expose] public section
