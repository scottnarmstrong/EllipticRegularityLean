module

public import PDEFoundation.Euler.Defs
import EllipticRegularity.Euler.YudovichAssembly

/-!
# Proof of `PDE.yudovich_uniqueness`

Yudovich weak–strong uniqueness for the 2d Euler equations on the unit torus: the
relative energy inequality, the periodic Calderón–Zygmund bound `‖∇v₂‖_p ≤ K p M`, Hölder
interpolation and the Osgood argument (`EllipticRegularity.Euler.YudovichAssembly`).
-/

@[expose] public section

open MeasureTheory Set

namespace PDE.YudovichUniquenessProof

theorem result (T : ℝ) (hT : 0 < T) (M : ℝ) (v₀ : Vec 2 → Vec 2)
    (v₁ v₂ : Vec 2 × ℝ → Vec 2)
    (h₁ : IsEulerWeakSolutionWithDatum T v₀ v₁) (h₂ : IsEulerWeakSolutionWithDatum T v₀ v₂)
    (hb₁ : ∃ B : ℝ, ∀ᵐ z ∂(eulerMeasure T), vecNormSq (v₁ z) ≤ B)
    (hb₂ : ∃ B : ℝ, ∀ᵐ z ∂(eulerMeasure T), vecNormSq (v₂ z) ≤ B)
    (hω : HasBoundedVorticity T M v₂) (hE : HasEnergyInequality T v₀ v₁) :
    ∀ᵐ z ∂(eulerMeasure T), v₁ z = v₂ z :=
  yudovich_uniqueness_proof T hT M v₀ v₁ v₂ h₁ h₂ hb₁ hb₂ hω hE

end PDE.YudovichUniquenessProof
