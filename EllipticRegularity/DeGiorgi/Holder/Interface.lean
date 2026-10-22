module

public import PDEFoundation.PDE.WeakInequalities
public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.Geometry.EuclideanBall.Basic
public import PDEFoundation.Measure.RestrictedVolume

/-!
# Interface hypotheses of the De Giorgi Hölder argument

The statements below are the exact types of the results which the Hölder argument
takes from other parts of the development, written as `abbrev`s so that they are transparent to
`exact`.

* `EoPStatement d C` is the conclusion of the expansion-of-positivity
  statement `PDE.exists_expansionOfPositivity_constant d hd` for the constant `C`;
* `LinftyStatement d C` is the conclusion of the `L^∞` estimate
  `PDE.exists_localMaxPrinciple_constant d hd` for the constant `C`;
* `AffineStability d`: solutions are stable under `u ↦ s * u + t`;
* `ScaleStability d`: solutions are stable under `u ↦ u (ρ • · + x₀)` for balls
  `B_ρ(x₀) ⊆ B_1` (the coefficient field is transformed, with the same `Λ`).
-/

@[expose] public section

namespace PDE.DGNMHolder

open PDE MeasureTheory

/-- The conclusion of the expansion-of-positivity statement for `C`. -/
abbrev EoPStatement (d : ℕ) (C : ℝ) : Prop :=
  ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 → ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSuperharmonicOn a (euclideanBall (0 : Vec d) 1) u →
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 ≤ u.toFun x) →
      ENNReal.ofReal (1 - θ) * volume (euclideanBall (0 : Vec d) 1) ≤
        volume {x ∈ euclideanBall (0 : Vec d) 1 | 1 ≤ u.toFun x} →
        ENNReal.ofReal (Real.exp (-(C * θ ^ ((1 : ℝ) / d) * Λ ^ (((d : ℝ) + 2) / 4)))) ≤
          essInf (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))

/-- The conclusion of the `L^∞` statement for `C`. -/
abbrev LinftyStatement (d : ℕ) (C : ℝ) : Prop :=
  ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSubharmonicOn a (euclideanBall (0 : Vec d) 1) u →
        essSup (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
          ENNReal.ofReal (C * Λ ^ ((d : ℝ) / 4)) *
            eLpNorm u.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1))

/-- Solutions are stable under `u ↦ s * u + t` (class-stability fact). -/
abbrev AffineStability (d : ℕ) : Prop :=
  ∀ (Λ : ℝ) (a : CoeffField d),
    (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
    (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
    ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
    IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u (0 : Vec d → ℝ) 0 →
    ∀ s t : ℝ, ∃ w : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) w (0 : Vec d → ℝ) 0 ∧
        w.toFun =ᵐ[volumeOn (euclideanBall (0 : Vec d) 1)] fun x => s * u.toFun x + t

/-- Solutions are stable under translation and dilation of balls contained in the
unit ball, with the same ellipticity `Λ` (class-stability fact). -/
abbrev ScaleStability (d : ℕ) : Prop :=
  ∀ (Λ : ℝ) (a : CoeffField d),
    (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
    (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
    ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
    IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u (0 : Vec d → ℝ) 0 →
    ∀ (x₀ : Vec d) (ρ : ℝ), 0 < ρ → euclideanBall x₀ ρ ⊆ euclideanBall (0 : Vec d) 1 →
      ∃ (a' : CoeffField d) (u' : H1Function (euclideanBall (0 : Vec d) 1)),
        (∀ i j : Fin d, AEMeasurable (fun x => a' x i j)
          (volumeOn (euclideanBall (0 : Vec d) 1))) ∧
        (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a' x)) ∧
        IsWeakDivergenceFormSolutionOn a' (euclideanBall (0 : Vec d) 1) u' (0 : Vec d → ℝ) 0 ∧
        u'.toFun =ᵐ[volumeOn (euclideanBall (0 : Vec d) 1)] fun y => u.toFun (ρ • y + x₀)

end PDE.DGNMHolder
