module

public import PDEFoundation.Monotonicity.Defs
public import PDEFoundation.Sobolev.ClassicalLaplacian
import PDEFoundation.Monotonicity.Poon.AssemblyMono

/-!
# Proof of `PDE.poon_monotonicity` (Theorem 2.15)

The proof follows Theorem 2.15 of the manuscript: with `v(s,x) = u(-s,x)` and `w = x·∇v - 2sΔv`,
integration by parts against the heat kernel gives `H' = 2D`, `∫ v w Φ = 2 s D` and
`s D' + D = (1/(2s)) ∫ w² Φ` on `{0 < s < T, 8 A s < 1}` (the integrals converge by the
pointwise Gaussian-type derivative bounds of `Poon.DerivBounds`).  Cauchy–Schwarz in `L²(Φ dx)` then
gives `N' ≥ 0` where `H > 0`; the degenerate case `H = 0` is handled through monotonicity of `H`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE.PoonMonotonicityProof

theorem result (d : ℕ) (hd : 0 < d) (T : ℝ) (hT : 0 < T)
    (u : ℝ → Vec d → ℝ)
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec d => u p.1 p.2)
      (Set.Ioo (-T) 0 ×ˢ Set.univ))
    (hheat : ∀ t ∈ Set.Ioo (-T) 0, ∀ x : Vec d,
      HasDerivAt (fun τ : ℝ => u τ x) (euclideanCoordLaplacian (u t) x) t)
    (A C : ℝ)
    (hgrowth : ∀ t ∈ Set.Ioo (-T) 0, ∀ x : Vec d, |u t x| ≤ C * Real.exp (A * vecNormSq x)) :
    MonotoneOn (poonFrequency u) {s : ℝ | 0 < s ∧ s < T ∧ 8 * A * s < 1} := by
  have _ := hd
  have _ := hT
  exact poonFrequency_monotoneOn hsmooth hheat hgrowth

end PDE.PoonMonotonicityProof
