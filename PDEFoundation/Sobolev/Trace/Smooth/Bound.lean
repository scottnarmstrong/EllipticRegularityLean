module

public import PDEFoundation.Sobolev.Trace.Smooth.Assemble

/-!
# Smooth trace bound (facade)

Public facade for the manuscript Step 4 assembly: `smoothTraceBound_of_model` derives
`SmoothTraceBound Ω p` from the half-space bounds `ModelTraceLp n p` and
`ModelTraceGagliardo n p` and a trace atlas.  The proof is split into `Scalar`, `GagSum`, `Split`
(Gagliardo-integral bookkeeping), `Calculus`, `Pullback`, `ChainRule`, `PullbackBound`, `Transfer`
(half-space pullback), `Sigma` (surface measure comparison), `ChartLp`, `ChartGag`,
`ChartGagliardo` (per-chart bounds) and `Assemble`.
-/

@[expose] public section
