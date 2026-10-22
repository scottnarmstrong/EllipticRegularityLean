module

public import EllipticRegularity.Ch4.Planar.Wirtinger
public import PDEFoundation

/-!
# Proof of `PDE.wirtinger_inequality` (Lemma 4.23)

-/

@[expose] public section

namespace PDE.WirtingerInequalityProof

open MeasureTheory

theorem result (w : ℝ → ℝ)
    (hper : Function.Periodic w (2 * Real.pi))
    (hac : AbsolutelyContinuousOnInterval w 0 (2 * Real.pi))
    (hderiv : MemLp (deriv w) 2 (volume.restrict (Set.Icc 0 (2 * Real.pi)))) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (w θ - (1 / (2 * Real.pi)) * ∫ t in (0 : ℝ)..(2 * Real.pi), w t) ^ 2 ≤
      ∫ θ in (0 : ℝ)..(2 * Real.pi), (deriv w θ) ^ 2 :=
  PDE.Ch4Planar.wirtinger_inequality_full  w hper hac hderiv

end PDE.WirtingerInequalityProof
