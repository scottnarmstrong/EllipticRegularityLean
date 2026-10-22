module

public import PDEFoundation.PDE.WeakInequalities
public import PDEFoundation.Geometry.EuclideanBall.Basic

/-!
# Interface hypotheses of the logarithmic-supersolution package

This file records, as explicit `Prop`-valued definitions, the PDE-specific inputs of the
crossover estimate and of expansion of positivity that are established by the test-function
toolbox (a different work package):

* `LogEnergyHyp d`: the logarithmic Caccioppoli (`log`-energy) estimate for positive
  supersolutions (manuscript: (4.81), equivalently the ball form (4.82));
* `PosPartLogEnergyHyp d`: the same estimate for `(-log u)_+`, which is a subsolution
  (manuscript: Proposition 4.11, Steps 1-2, with Lemma 4.10);
* `LocMaxBallHyp d`: the `L^∞` estimate for subsolutions, transported to a ball
  `B_{1/8}(y)`, `B_{1/4}(y)` by translation and dilation.

The theorems of this package take these as explicit hypotheses of exactly these types.
-/

@[expose] public section

namespace PDE.DGNMLog

open MeasureTheory

/-- Logarithmic energy estimate: for a supersolution `u` on the unit ball bounded below by a
positive constant, `log u` has a representative `v ∈ H¹(B₁)` with
`∫_{B_r(y)} |∇v|² ≤ 4 Λ |B_s(y)| / (s-r)²` whenever `|y| + s < 1` and `0 < r < s`. -/
def LogEnergyHyp (d : ℕ) : Prop :=
  ∀ (Λ : ℝ) (a : CoeffField d),
    (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
    (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
    ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
    (∃ δ : ℝ, 0 < δ ∧ ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), δ ≤ u.toFun x) →
    IsWeakDivergenceFormSuperharmonicOn a (euclideanBall (0 : Vec d) 1) u →
    ∃ v : H1Function (euclideanBall (0 : Vec d) 1),
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), v.toFun x = Real.log (u.toFun x)) ∧
      ∀ (y : Vec d) (r s : ℝ), 0 < r → r < s → vecEuclideanNorm y + s < 1 →
        ∫ x in euclideanBall y r, vecNormSq (v.grad x) ≤
          4 * Λ * (volume (euclideanBall y s)).toReal / (s - r) ^ 2

/-- Logarithmic energy estimate for the positive part of `-log u`, which is a subsolution. -/
def PosPartLogEnergyHyp (d : ℕ) : Prop :=
  ∀ (Λ : ℝ) (a : CoeffField d),
    (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
    (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
    ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
    (∃ δ : ℝ, 0 < δ ∧ ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), δ ≤ u.toFun x) →
    IsWeakDivergenceFormSuperharmonicOn a (euclideanBall (0 : Vec d) 1) u →
    ∃ w : H1Function (euclideanBall (0 : Vec d) 1),
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)),
        w.toFun x = max (-Real.log (u.toFun x)) 0) ∧
      IsWeakDivergenceFormSubharmonicOn a (euclideanBall (0 : Vec d) 1) w ∧
      ∀ (y : Vec d) (r s : ℝ), 0 < r → r < s → vecEuclideanNorm y + s < 1 →
        ∫ x in euclideanBall y r, vecNormSq (w.grad x) ≤
          4 * Λ * (volume (euclideanBall y s)).toReal / (s - r) ^ 2

/-- The `L^∞` estimate for subsolutions (`PDE.exists_localMaxPrinciple_constant`),
rescaled to the balls `B_{1/8}(y) ⊆ B_{1/4}(y) ⊆ B₁`. -/
def LocMaxBallHyp (d : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (a : CoeffField d),
    (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
    (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
    ∀ w : H1Function (euclideanBall (0 : Vec d) 1),
    IsWeakDivergenceFormSubharmonicOn a (euclideanBall (0 : Vec d) 1) w →
    ∀ y : Vec d, vecEuclideanNorm y + 1 / 4 < 1 →
      essSup (fun x => ENNReal.ofReal (w.toFun x)) (volumeOn (euclideanBall y (1 / 8))) ≤
        ENNReal.ofReal (C * Λ ^ ((d : ℝ) / 4)) *
          eLpNorm w.toFun 2 (volumeOn (euclideanBall y (1 / 4)))

end PDE.DGNMLog
