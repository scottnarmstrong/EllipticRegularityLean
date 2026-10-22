module

public import EllipticRegularity.Euler.YudovichUniquenessProof

@[expose] public section

open scoped ENNReal NNReal

namespace PDE

open MeasureTheory
open Set

/-- Yudovich weak-strong uniqueness for 2d Euler (Proposition 3.12): `v₁` satisfies the energy
inequality, `v₂` has bounded vorticity. -/
theorem yudovich_uniqueness (T : ℝ) (hT : 0 < T) (M : ℝ) (v₀ : Vec 2 → Vec 2)
    (v₁ v₂ : Vec 2 × ℝ → Vec 2)
    (h₁ : IsEulerWeakSolutionWithDatum T v₀ v₁) (h₂ : IsEulerWeakSolutionWithDatum T v₀ v₂)
    (hb₁ : ∃ B : ℝ, ∀ᵐ z ∂(eulerMeasure T), vecNormSq (v₁ z) ≤ B)
    (hb₂ : ∃ B : ℝ, ∀ᵐ z ∂(eulerMeasure T), vecNormSq (v₂ z) ≤ B)
    (hω : HasBoundedVorticity T M v₂) (hE : HasEnergyInequality T v₀ v₁) :
    ∀ᵐ z ∂(eulerMeasure T), v₁ z = v₂ z :=
  PDE.YudovichUniquenessProof.result T hT M v₀ v₁ v₂ h₁ h₂ hb₁ hb₂ hω hE

end PDE
