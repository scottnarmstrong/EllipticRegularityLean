module

public import PDEFoundation.Sobolev.Trace.Defs
public import PDEFoundation.Sobolev.Trace.Assembly.RightInverse
public import PDEFoundation.Sobolev.Trace.Chart.Atlas
public import PDEFoundation.Sobolev.Trace.Chart.Surface

/-!
# Proof of `PDE.trace_right_inverse` (Theorem 1.25)

`PDE.TraceRightInverseProof.result` (Theorem 1.25): write `d = n + 1`, take a trace
atlas and extension data (`exists_traceAtlas`, `exists_extData`) and apply
`right_inverse_of_extData`: the half-space extension `modelExt` (manuscript (1.53)) transported
by the charts and glued by the partition of unity.
-/

@[expose] public section

namespace PDE.TraceRightInverseProof

open MeasureTheory PDE.TraceLane
open scoped ENNReal NNReal

/-- Right inverse for the trace (Theorem 1.25). -/
theorem result (d : ℕ) (hd : 1 ≤ d) (Ω : Set (Vec d))
    (hΩo : IsOpen Ω) (_hΩc : IsConnected Ω) (hΩb : Bornology.IsBounded Ω)
    (hΩ : HasC1Boundary Ω) (p : ℝ) (hp : 1 < p) :
    haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.2 hp.le⟩
    ∃ (C : ℝ≥0) (E : (Vec d → ℝ) → W1pFunction Ω (ENNReal.ofReal p)),
      (∀ g h, IsBesov Ω (1 - 1 / p) p g → IsBesov Ω (1 - 1 / p) p h → E (g + h) = E g + E h) ∧
      (∀ (a : ℝ) g, IsBesov Ω (1 - 1 / p) p g → E (a • g) = a • E g) ∧
      ∀ g, IsBesov Ω (1 - 1 / p) p g →
        IsTraceOf Ω p (E g) g ∧
        w1pNorm Ω p (E g) ≤ (C : ℝ≥0∞) * besovNorm Ω (1 - 1 / p) p g := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.2 hp.le⟩
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  obtain ⟨A⟩ := exists_traceAtlas hΩo hΩb hΩ
  obtain ⟨D, -⟩ := exists_extData A
  exact right_inverse_of_extData D hΩo hΩb hp

end PDE.TraceRightInverseProof
