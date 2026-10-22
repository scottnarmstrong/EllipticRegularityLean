module

public import PDEFoundation.Sobolev.Trace.TraceRightInverseProof

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal NNReal

/-- Right inverse for the trace (Theorem 1.25). -/
theorem trace_right_inverse (d : ℕ) (hd : 1 ≤ d) (Ω : Set (Vec d))
    (hΩo : IsOpen Ω) (hΩc : IsConnected Ω) (hΩb : Bornology.IsBounded Ω)
    (hΩ : HasC1Boundary Ω) (p : ℝ) (hp : 1 < p) :
    haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.2 hp.le⟩
    ∃ (C : ℝ≥0) (E : (Vec d → ℝ) → W1pFunction Ω (ENNReal.ofReal p)),
      (∀ g h, IsBesov Ω (1 - 1 / p) p g → IsBesov Ω (1 - 1 / p) p h → E (g + h) = E g + E h) ∧
      (∀ (a : ℝ) g, IsBesov Ω (1 - 1 / p) p g → E (a • g) = a • E g) ∧
      ∀ g, IsBesov Ω (1 - 1 / p) p g →
        IsTraceOf Ω p (E g) g ∧
        w1pNorm Ω p (E g) ≤ (C : ℝ≥0∞) * besovNorm Ω (1 - 1 / p) p g := by exact PDE.TraceRightInverseProof.result d hd Ω hΩo hΩc hΩb hΩ p hp

end PDE
