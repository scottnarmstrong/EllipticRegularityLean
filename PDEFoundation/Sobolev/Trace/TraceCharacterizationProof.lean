module

public import PDEFoundation.Sobolev.Trace.Defs
public import PDEFoundation.Sobolev.Trace.Assembly.Characterization
public import PDEFoundation.Sobolev.Trace.Assembly.TraceInequality
public import PDEFoundation.Sobolev.Trace.Assembly.RightInverse
public import PDEFoundation.Sobolev.Trace.Smooth.Bound
public import PDEFoundation.Sobolev.Trace.Density.Main
public import PDEFoundation.Sobolev.Trace.Model.TraceBound
public import PDEFoundation.Sobolev.Trace.Chart.Atlas
public import PDEFoundation.Sobolev.Trace.Chart.Surface

/-!
# Proof of `PDE.trace_space_characterization` (Corollary 1.26)

`PDE.TraceCharacterizationProof.result` (Corollary 1.26): with `d = n + 1`, a trace atlas
and extension data, the trace inequality (`trace_inequality_of_props`, as in the proof of
Theorem 1.23) and the right inverse (`right_inverse_of_extData`, as in the proof of Theorem 1.25)
feed `characterization_of`, which takes the trace operator to be a choice of trace and derives its
a.e.-linearity and `T (E g) = g`.
-/

@[expose] public section

namespace PDE.TraceCharacterizationProof

open MeasureTheory PDE.TraceLane
open scoped ENNReal NNReal

/-- Characterization of the trace space (Corollary 1.26). -/
theorem result (d : ℕ) (hd : 1 ≤ d) (Ω : Set (Vec d))
    (hΩo : IsOpen Ω) (_hΩc : IsConnected Ω) (hΩb : Bornology.IsBounded Ω)
    (hΩ : HasC1Boundary Ω) (p : ℝ) (hp : 1 < p) :
    haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.2 hp.le⟩
    ∃ (C : ℝ≥0) (T : W1pFunction Ω (ENNReal.ofReal p) → Vec d → ℝ)
      (E : (Vec d → ℝ) → W1pFunction Ω (ENNReal.ofReal p)),
      (∀ u, IsTraceOf Ω p u (T u) ∧ IsBesov Ω (1 - 1 / p) p (T u) ∧
        besovNorm Ω (1 - 1 / p) p (T u) ≤ (C : ℝ≥0∞) * w1pNorm Ω p u) ∧
      (∀ u v, T (u + v) =ᵐ[boundarySurfaceMeasure Ω] T u + T v) ∧
      (∀ (a : ℝ) u, T (a • u) =ᵐ[boundarySurfaceMeasure Ω] a • T u) ∧
      (∀ g h, IsBesov Ω (1 - 1 / p) p g → IsBesov Ω (1 - 1 / p) p h → E (g + h) = E g + E h) ∧
      (∀ (a : ℝ) g, IsBesov Ω (1 - 1 / p) p g → E (a • g) = a • E g) ∧
      (∀ g, IsBesov Ω (1 - 1 / p) p g →
        w1pNorm Ω p (E g) ≤ (C : ℝ≥0∞) * besovNorm Ω (1 - 1 / p) p g ∧
        T (E g) =ᵐ[boundarySurfaceMeasure Ω] g) := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.2 hp.le⟩
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  obtain ⟨A⟩ := exists_traceAtlas hΩo hΩb hΩ
  have := boundarySurfaceMeasure_isFiniteMeasure A hΩb
  obtain ⟨D, -⟩ := exists_extData A
  exact characterization_of hΩo hp
    (trace_inequality_of_props hΩo hp
      (smoothTraceBound_of_model hΩo hΩb A hp (fun _ hv hK => model_trace_Lp n hp hv hK)
        (model_trace_gagliardo n hp))
      (densityProp hΩo hΩb A hp))
    (right_inverse_of_extData D hΩo hΩb hp)

end PDE.TraceCharacterizationProof
