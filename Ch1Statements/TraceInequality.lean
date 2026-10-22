module

public import PDEFoundation.Sobolev.Trace.TraceInequalityProof

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal NNReal

/-- Trace inequality (Theorem 1.23). -/
theorem trace_inequality (d : ℕ) (hd : 1 ≤ d) (Ω : Set (Vec d))
    (hΩo : IsOpen Ω) (hΩc : IsConnected Ω) (hΩb : Bornology.IsBounded Ω)
    (hΩ : HasC1Boundary Ω) (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ≥0, ∀ u : W1pFunction Ω (ENNReal.ofReal p),
      (∃ g, IsTraceOf Ω p u g) ∧
      (∀ g g', IsTraceOf Ω p u g → IsTraceOf Ω p u g' →
        g =ᵐ[boundarySurfaceMeasure Ω] g') ∧
      ∀ g, IsTraceOf Ω p u g →
        besovNorm Ω (1 - 1 / p) p g ≤ (C : ℝ≥0∞) * w1pNorm Ω p u := by exact PDE.TraceInequalityProof.result d hd Ω hΩo hΩc hΩb hΩ p hp

end PDE
