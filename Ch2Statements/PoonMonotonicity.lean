module

public import PDEFoundation.Monotonicity.PoonMonotonicityProof

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE

/-- Monotonicity of Poon's parabolic frequency on `8 A s < 1` (Theorem 2.15). -/
theorem poon_monotonicity (d : ℕ) (hd : 0 < d) (T : ℝ) (hT : 0 < T)
    (u : ℝ → Vec d → ℝ)
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec d => u p.1 p.2)
      (Set.Ioo (-T) 0 ×ˢ Set.univ))
    (hheat : ∀ t ∈ Set.Ioo (-T) 0, ∀ x : Vec d,
      HasDerivAt (fun τ : ℝ => u τ x) (euclideanCoordLaplacian (u t) x) t)
    (A C : ℝ)
    (hgrowth : ∀ t ∈ Set.Ioo (-T) 0, ∀ x : Vec d, |u t x| ≤ C * Real.exp (A * vecNormSq x)) :
    MonotoneOn (poonFrequency u) {s : ℝ | 0 < s ∧ s < T ∧ 8 * A * s < 1} := by exact PDE.PoonMonotonicityProof.result d hd T hT u hsmooth hheat A C hgrowth

end PDE
