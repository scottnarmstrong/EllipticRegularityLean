module

public import EllipticRegularity.Ch4.WirtingerInequalityProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- Wirtinger inequality (Lemma 4.23).
A `2π`-periodic function absolutely continuous on `[0,2π]` with `w' ∈ L²(0,2π)` satisfies
`∫_0^{2π} (w - w̄)² ≤ ∫_0^{2π} (w')²`, where `w̄` is the mean over one period. -/
theorem wirtinger_inequality (w : ℝ → ℝ)
    (hper : Function.Periodic w (2 * Real.pi))
    (hac : AbsolutelyContinuousOnInterval w 0 (2 * Real.pi))
    (hderiv : MemLp (deriv w) 2 (volume.restrict (Set.Icc 0 (2 * Real.pi)))) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (w θ - (1 / (2 * Real.pi)) * ∫ t in (0 : ℝ)..(2 * Real.pi), w t) ^ 2 ≤
      ∫ θ in (0 : ℝ)..(2 * Real.pi), (deriv w θ) ^ 2 := by exact PDE.WirtingerInequalityProof.result w hper hac hderiv

end PDE
