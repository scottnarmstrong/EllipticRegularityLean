module

public import PDEFoundation.Ambient.CoefficientField
public import PDEFoundation.Geometry.ConvexDomain
public import PDEFoundation.Geometry.EuclideanBall.Basic
public import PDEFoundation.Measure.RestrictedVolume
public import PDEFoundation.PDE.WeakInequalities
public import PDEFoundation.Sobolev.H1.Mean
public import PDEFoundation.Sobolev.H1.Truncation

/-!
# Interface hypotheses for the Moser iterations

The Moser iterations of Propositions 4.13 and 4.14
consume a family of one-step reverse Holder estimates obtained by testing the equation
with powers of the solution, together with two qualitative facts for subsolutions.  These
are proved elsewhere; here each is written as an explicit `Prop` of exactly the type
consumed by the iteration, and taken as a hypothesis of the iteration theorems.  Each
abbreviation below is a plain `∀`/`∃` statement.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE.DGNMMoser

/-- (H1) One-step estimate for subsolutions bounded below by `δ > 0` and above on
`B_{3/4}` (manuscript (4.62)): for exponents `p > 1` and radii
`1/2 ≤ r < s ≤ 3/4`,
`‖u‖_{L^{pd/(d-2)}(B_r)} ≤ (C₁ (s-r)⁻² (Λ p²/(p-1)² + 1))^{1/p} ‖u‖_{L^p(B_s)}`. -/
abbrev MoserOneStepHyp (d : ℕ) : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (Λ : ℝ) (a : CoeffField d),
    (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
    (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
    ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
    IsWeakDivergenceFormSubharmonicOn a (euclideanBall (0 : Vec d) 1) u →
    ∀ δ M : ℝ, 0 < δ →
    (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), δ ≤ u.toFun x) →
    (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) (3 / 4))), u.toFun x ≤ M) →
    ∀ p : ℝ, 1 < p → ∀ r s : ℝ, 1 / 2 ≤ r → r < s → s ≤ 3 / 4 →
      eLpNorm u.toFun (ENNReal.ofReal (p * ((d : ℝ) / (d - 2))))
          (volumeOn (euclideanBall (0 : Vec d) r)) ≤
        ENNReal.ofReal
            ((C₁ / (s - r) ^ 2 * (Λ * p ^ 2 / (p - 1) ^ 2 + 1)) ^ (1 / p)) *
          eLpNorm u.toFun (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) s))

/-- (H0a) Local boundedness of subsolutions on `B_{3/4}` (consequence of the local
maximum principle after scaling, translation and a finite cover). -/
abbrev SubsolutionBoundedHyp (d : ℕ) : Prop :=
  ∀ (Λ : ℝ) (a : CoeffField d),
    (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
    (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
    ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
    IsWeakDivergenceFormSubharmonicOn a (euclideanBall (0 : Vec d) 1) u →
    ∃ M : ℝ, ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) (3 / 4))), u.toFun x ≤ M

/-- (H0b) The positive part of a subsolution is a subsolution (manuscript Step 0). -/
abbrev PositivePartSubsolutionHyp (d : ℕ) : Prop :=
  ∀ (Λ : ℝ) (a : CoeffField d),
    (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
    (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
    ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
    IsWeakDivergenceFormSubharmonicOn a (euclideanBall (0 : Vec d) 1) u →
    IsWeakDivergenceFormSubharmonicOn a (euclideanBall (0 : Vec d) 1)
      (u.positivePartSubConst
        (isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) one_pos) 0)

/-- (H2a) One-step estimate for the reciprocal of a supersolution bounded below by
`δ > 0` (manuscript (4.71)), for `p > 0` and `1/2 ≤ r < s ≤ 1`. -/
abbrev WeakHarnackInvOneStepHyp (d : ℕ) : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (Λ : ℝ) (a : CoeffField d),
    (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
    (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
    ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
    IsWeakDivergenceFormSuperharmonicOn a (euclideanBall (0 : Vec d) 1) u →
    ∀ δ : ℝ, 0 < δ →
    (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), δ ≤ u.toFun x) →
    ∀ p : ℝ, 0 < p → ∀ r s : ℝ, 1 / 2 ≤ r → r < s → s ≤ 1 →
      eLpNorm (fun x => (u.toFun x)⁻¹) (ENNReal.ofReal (p * ((d : ℝ) / (d - 2))))
          (volumeOn (euclideanBall (0 : Vec d) r)) ≤
        ENNReal.ofReal
            ((C₁ / (s - r) ^ 2 * (Λ * p ^ 2 / (1 + p) ^ 2 + 1)) ^ (1 / p)) *
          eLpNorm (fun x => (u.toFun x)⁻¹) (ENNReal.ofReal p)
            (volumeOn (euclideanBall (0 : Vec d) s))

/-- (H2b) One-step estimate for a supersolution bounded below by `δ > 0` and small
positive exponents (manuscript (4.72)), for `0 < p < 1` and `1/2 ≤ r < s ≤ 1`. -/
abbrev WeakHarnackSmallOneStepHyp (d : ℕ) : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (Λ : ℝ) (a : CoeffField d),
    (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
    (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
    ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
    IsWeakDivergenceFormSuperharmonicOn a (euclideanBall (0 : Vec d) 1) u →
    ∀ δ : ℝ, 0 < δ →
    (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), δ ≤ u.toFun x) →
    ∀ p : ℝ, 0 < p → p < 1 → ∀ r s : ℝ, 1 / 2 ≤ r → r < s → s ≤ 1 →
      eLpNorm u.toFun (ENNReal.ofReal (p * ((d : ℝ) / (d - 2))))
          (volumeOn (euclideanBall (0 : Vec d) r)) ≤
        ENNReal.ofReal
            ((C₁ / (s - r) ^ 2 * (Λ * p ^ 2 / (1 - p) ^ 2 + 1)) ^ (1 / p)) *
          eLpNorm u.toFun (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) s))

end PDE.DGNMMoser
