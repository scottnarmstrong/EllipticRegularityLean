module

public import PDEFoundation.Sobolev.Trace.TraceInequalityProof

@[expose] public section

open scoped ENNReal NNReal

namespace PDE

open MeasureTheory
open scoped NNReal

/-- Trace inequality (Theorem 1.23).  Let `Ω ⊆ ℝ^d` be a bounded, connected, open set with `C¹`
boundary and `1 < p < ∞`.  There is a constant `C` such that every `u ∈ W^{1,p}(Ω)` has a trace
`g` on `∂Ω` (a limit in `L^p(∂Ω)` of restrictions of `C¹(Ω̄)` functions converging to `u` in
`W^{1,p}(Ω)`), the trace is unique `σ`-almost everywhere, and
`‖g‖_{B^{1-1/p}_{p,p}(∂Ω)} ≤ C ‖u‖_{W^{1,p}(Ω)}`. -/
theorem trace_inequality (d : ℕ) (hd : 1 ≤ d) (Ω : Set (Vec d))
    (hΩo : IsOpen Ω) (hΩc : IsConnected Ω) (hΩb : Bornology.IsBounded Ω)
    (hΩ : HasC1Boundary Ω) (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ≥0, ∀ u : W1pFunction Ω (ENNReal.ofReal p),
      (∃ g, IsTraceOf Ω p u g) ∧
      (∀ g g', IsTraceOf Ω p u g → IsTraceOf Ω p u g' →
        g =ᵐ[boundarySurfaceMeasure Ω] g') ∧
      ∀ g, IsTraceOf Ω p u g →
        besovNorm Ω (1 - 1 / p) p g ≤ (C : ℝ≥0∞) * w1pNorm Ω p u :=
  PDE.TraceInequalityProof.result d hd Ω hΩo hΩc hΩb hΩ p hp

end PDE
