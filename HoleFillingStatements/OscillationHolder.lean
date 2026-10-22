module

public import PDEFoundation.Regularity.OscillationHolderProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- Hölder continuity from decay of the essential oscillation on cubes
(Lemma 1.20). -/
theorem exists_holderRepresentative_of_essOsc_decay
    (d : ℕ) {α K R : ℝ} (x₀ : Vec d)
    (hα : 0 < α) (hα₁ : α ≤ 1) (hK : 0 ≤ K) (hR : 0 < R)
    (u : Vec d → ℝ) (hu : IntegrableOn u (centeredAxisCube x₀ R))
    (hosc : ∀ (x : Vec d) (r : ℝ), 0 < r →
      centeredAxisCube x r ⊆ centeredAxisCube x₀ R →
      ∃ a b : ℝ,
        (∀ᵐ y ∂volumeOn (centeredAxisCube x r), u y ∈ Set.Icc a b) ∧
        b - a ≤ K * r ^ α) :
    ∃ v : Vec d → ℝ,
      (∀ᵐ y ∂volumeOn (closedCenteredAxisCube x₀ (R / 8)), v y = u y) ∧
      ∀ x ∈ closedCenteredAxisCube x₀ (R / 8),
        ∀ y ∈ closedCenteredAxisCube x₀ (R / 8),
          |v x - v y| ≤ 2 ^ α * K * vecEuclideanNorm (x - y) ^ α := by exact PDE.OscillationHolderProof.result d x₀ hα hα₁ hK hR u hu hosc

end PDE
