module

public import PDEFoundation.Sobolev.Trace.Defs
public import PDEFoundation.Sobolev.Trace.Assembly.TraceInequality
public import PDEFoundation.Sobolev.Trace.Smooth.Bound
public import PDEFoundation.Sobolev.Trace.Density.Main
public import PDEFoundation.Sobolev.Trace.Model.TraceBound
public import PDEFoundation.Sobolev.Trace.Chart.Atlas
public import PDEFoundation.Sobolev.Trace.Chart.Surface

/-!
# Proof of `PDE.trace_inequality` (Theorem 1.23)

`PDE.TraceInequalityProof.result` (Theorem 1.23): write `d = n + 1`, take a trace atlas of
`Ω` (`exists_traceAtlas`), so the surface measure is finite; the half-space bounds
(`model_trace_Lp`, `model_trace_gagliardo`, manuscript Steps 1-3) give the trace bound for `C¹(Ω̄)`
functions (`smoothTraceBound_of_model`, Step 4), and with the density of `C¹` functions
(`densityProp`) the completion argument `trace_inequality_of_props` (Step 5) gives existence,
uniqueness and the Besov bound.
-/

@[expose] public section

namespace PDE.TraceInequalityProof

open MeasureTheory PDE.TraceLane
open scoped ENNReal NNReal

/-- Trace inequality (Theorem 1.23). -/
theorem result (d : ℕ) (hd : 1 ≤ d) (Ω : Set (Vec d))
    (hΩo : IsOpen Ω) (_hΩc : IsConnected Ω) (hΩb : Bornology.IsBounded Ω)
    (hΩ : HasC1Boundary Ω) (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ≥0, ∀ u : W1pFunction Ω (ENNReal.ofReal p),
      (∃ g, IsTraceOf Ω p u g) ∧
      (∀ g g', IsTraceOf Ω p u g → IsTraceOf Ω p u g' →
        g =ᵐ[boundarySurfaceMeasure Ω] g') ∧
      ∀ g, IsTraceOf Ω p u g →
        besovNorm Ω (1 - 1 / p) p g ≤ (C : ℝ≥0∞) * w1pNorm Ω p u := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  obtain ⟨A⟩ := exists_traceAtlas hΩo hΩb hΩ
  have := boundarySurfaceMeasure_isFiniteMeasure A hΩb
  exact trace_inequality_of_props hΩo hp
    (smoothTraceBound_of_model hΩo hΩb A hp (fun _ hv hK => model_trace_Lp n hp hv hK)
      (model_trace_gagliardo n hp))
    (densityProp hΩo hΩb A hp)

end PDE.TraceInequalityProof
