module

public import PDEFoundation.Sobolev.Trace.Extension.FlatLp
public import PDEFoundation.Sobolev.Trace.Extension.FlatTransfer

/-!
# Flat pull-back of a cut-off boundary function

Facade for the pull-back `flatPullback φ ζ g = (ζ g) ∘ Ψ₀` of a cut-off boundary function to the
flat chart and its two estimates: the `L^p` bound `flatPullback_Lp_le` and the flat Gagliardo bound
`flatPullback_gagliardo_le` (kernel exponent `n + p - 1`).
-/

@[expose] public section
