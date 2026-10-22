module

public import EllipticRegularity.Holder.GoodSquareMaximum
public import EllipticRegularity.Energy.SquareHoleFillingDecay
public import EllipticRegularity.Energy.CoefficientEnergyCaccioppoli

/-!
# Planar square oscillation estimates

The good-square maximum principle gives a bound on a selected intermediate
square. This file restricts that bound to the prescribed inner square and
combines it with quantitative coefficient-energy decay.
-/

@[expose] public section

namespace PDE

open MeasureTheory Set

noncomputable section

/-- A harmonic function's essential oscillation on an inner square is bounded
by sixteen times the square root of the surrounding shell energy. -/
theorem essentialOscillationLEOn_centeredAxisCube_of_harmonic
    {Lam : ℝ} {U : Set (Vec 2)} {a : CoeffField 2} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U)
    {x : Vec 2} {s : ℝ} (hs : 0 < s)
    (houter : centeredAxisCube x (2 * s) ⊆ U)
    (hEll : IsEllipticFieldOn 1 Lam U a)
    (hsol : IsWeakDivergenceFormHarmonicOn a U u) :
    HasEssentialOscillationLEOn u.toFun (centeredAxisCube x s)
      (16 * Real.sqrt (squareShellVectorEnergy u.grad x s)) := by
  obtain ⟨ρ, hρ, a₀, b₀, hrange, hwidth⟩ :=
    exists_radius_essentialOscillationLEOn_centeredAxisCube_of_harmonic
      hU hs houter hEll (by norm_num) hsol
  exact ⟨a₀, b₀, hrange.mono (centeredAxisCube_mono x hρ.1.le), hwidth⟩

/-- Unit-ball form of the planar good-square estimate. -/
theorem planar_essentialOscillationLEOn_goodSquare
    {Lam : ℝ} {a : CoeffField 2}
    {u : H1Function (euclideanBall (0 : Vec 2) 1)}
    {x : Vec 2} {s : ℝ} (hs : 0 < s)
    (houter : centeredAxisCube x (2 * s) ⊆
      euclideanBall (0 : Vec 2) 1)
    (hEll : IsEllipticFieldOn 1 Lam
      (euclideanBall (0 : Vec 2) 1) a)
    (hsol : IsWeakDivergenceFormHarmonicOn a
      (euclideanBall (0 : Vec 2) 1) u) :
    HasEssentialOscillationLEOn u.toFun (centeredAxisCube x s)
      (16 * Real.sqrt (squareShellVectorEnergy u.grad x s)) :=
  essentialOscillationLEOn_centeredAxisCube_of_harmonic
    (isOpenBoundedConvexDomain_euclideanBall (0 : Vec 2) (by norm_num))
    hs houter hEll hsol

end

end PDE
