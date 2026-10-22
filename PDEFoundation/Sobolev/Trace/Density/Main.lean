module

public import PDEFoundation.Sobolev.Trace.Density.Atlas

/-!
# Density of smooth functions in `W^{1,p}(Ω)` (facade)

Facade for the density development for the trace theorem: continuity of translation in `L^p`
(`Translation`), local commutation of mollification with weak derivatives (`LocalMollify`),
extension by zero across a closed set (`Glue`), translate-and-mollify approximation (`Core`,
`Approx`, `Piece`), inward translation of graph charts (`Chart`), and the assembly over a trace
atlas (`Pieces`, `Atlas`).  The main result is `PDE.TraceLane.densityProp`.
-/

@[expose] public section
