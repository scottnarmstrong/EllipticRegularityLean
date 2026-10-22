module

public import PDEFoundation.Sobolev.Trace.TraceCharacterizationProof

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal NNReal

/-- Characterization of the trace space (Corollary 1.26). -/
theorem trace_space_characterization (d : ℕ) (hd : 1 ≤ d) (Ω : Set (Vec d))
    (hΩo : IsOpen Ω) (hΩc : IsConnected Ω) (hΩb : Bornology.IsBounded Ω)
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
        T (E g) =ᵐ[boundarySurfaceMeasure Ω] g) := by exact PDE.TraceCharacterizationProof.result d hd Ω hΩo hΩc hΩb hΩ p hp

end PDE
