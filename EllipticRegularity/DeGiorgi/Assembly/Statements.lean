module

public import PDEFoundation.PDE.WeakInequalities
public import PDEFoundation.PDE.WeakDivergenceForm
public import PDEFoundation.Regularity.Holder
public import PDEFoundation.Measure.NormalizedLp

/-!
# Statements used by the De Giorgi-Nash-Moser assembly

Each `...Concl d` below is, verbatim, the body after `(d) (hd)` of the corresponding
statement theorem in `DGNMStatements`.  The assembly theorems take these as explicit
hypotheses, which are instantiated with the proved theorems.
-/

@[expose] public section

namespace PDE.DGNMAssembly

open MeasureTheory

/-- Conclusion of the statement `exists_weakHarnack0_constant` (after `(d) (hd)`). -/
def WeakHarnack0Concl (d : ℕ) : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 < u.toFun x) →
      IsWeakDivergenceFormSuperharmonicOn a (euclideanBall (0 : Vec d) 1) u →
      (∀ p : ℝ, 0 < p →
        ENNReal.ofReal ((Λ * p ^ 2 + 1) ^ (-((d : ℝ) / 2))) *
            (∫⁻ x in euclideanBall (0 : Vec d) 1, ENNReal.ofReal ((u.toFun x)⁻¹ ^ p) ∂volume)⁻¹ ≤
          ENNReal.ofReal C *
            (essInf (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) ^ p) ∧
      (∀ p q : ℝ, 0 < p → p ≤ q → q < 1 →
        (eLpNorm u.toFun (ENNReal.ofReal (q * d / (d - 2))) (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) ^ p ≤
          ENNReal.ofReal (C * (Λ * p ^ 2 / (1 - q) ^ 2 + 1) ^ (((d : ℝ) + 2) / 2)) *
            (eLpNorm u.toFun (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) 1))) ^ p ∧
        ∀ m : ℕ, 1 ≤ m → p = q * ((d : ℝ) / (d - 2)) ^ (-(m : ℝ)) →
          (eLpNorm u.toFun (ENNReal.ofReal (q * d / (d - 2))) (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) ^ p ≤
            ENNReal.ofReal (C * (Λ * p ^ 2 / (1 - q) ^ 2 + 1) ^ ((d : ℝ) / 2)) *
              (eLpNorm u.toFun (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) 1))) ^ p)

/-- Conclusion of the statement `exists_crossover_constants` (after `(d) (hd)`). -/
def CrossoverConcl (d : ℕ) : Prop :=
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ c ≤ 1 / 2 ∧ ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 < u.toFun x) →
      IsWeakDivergenceFormSuperharmonicOn a (euclideanBall (0 : Vec d) 1) u →
        eLpMeanNormOn (euclideanBall (0 : Vec d) (1 / 2)) 1
            (fun x => u.toFun x ^ (c * Λ ^ (-(1 : ℝ) / 2))) *
          eLpMeanNormOn (euclideanBall (0 : Vec d) (1 / 2)) 1
            (fun x => u.toFun x ^ (-(c * Λ ^ (-(1 : ℝ) / 2)))) ≤ ENNReal.ofReal C

/-- Conclusion of the statement `exists_localMaxPrinciple_constant` (after `(d) (hd)`). -/
def LocalMaxConcl (d : ℕ) : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSubharmonicOn a (euclideanBall (0 : Vec d) 1) u →
        essSup (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
          ENNReal.ofReal (C * Λ ^ ((d : ℝ) / 4)) *
            eLpNorm u.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1))

/-- Conclusion of the statement `exists_moserLocalMax_constant` (after `(d) (hd)`). -/
def MoserLocalMaxConcl (d : ℕ) : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSubharmonicOn a (euclideanBall (0 : Vec d) 1) u →
      ∀ p : ℝ, 1 < p →
        (essSup (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) ^ p ≤
          ENNReal.ofReal (C * Λ ^ ((d : ℝ) / 2) * (p / (p - 1)) ^ (d : ℝ)) *
            (eLpNorm u.toFun (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) 1))) ^ p

/-- Conclusion of the statement `exists_deGiorgi_holder_constant` (after `(d) (hd)`). -/
def DeGiorgiHolderConcl (d : ℕ) : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧
      Real.exp (-(C * Λ ^ (((d : ℝ) + 2) / 4))) ≤ α ∧
      ∀ (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u (0 : Vec d → ℝ) 0 →
        ∃ (v : Vec d → ℝ) (M₀ M₁ : ℝ), v =ᵐ[volumeOn (euclideanBall (0 : Vec d) (1 / 2))] u.toFun ∧
          0 ≤ M₀ ∧ 0 ≤ M₁ ∧ (∀ x ∈ euclideanBall (0 : Vec d) (1 / 2), |v x| ≤ M₀) ∧
          EuclideanHolderSeminormLE (euclideanBall (0 : Vec d) (1 / 2)) v α M₁ ∧
          ENNReal.ofReal (M₀ + M₁) ≤ ENNReal.ofReal (C * Λ ^ ((d : ℝ) / 4)) *
            eLpNorm u.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1))

/-- Conclusion of the statement `exists_weakHarnack_constant` (after `(d) (hd)`). -/
def WeakHarnackConcl (d : ℕ) : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 < u.toFun x) →
      IsWeakDivergenceFormSuperharmonicOn a (euclideanBall (0 : Vec d) 1) u →
      ∀ q : ℝ, 0 < q → q < 1 →
        eLpNorm u.toFun (ENNReal.ofReal (q * d / (d - 2))) (volumeOn (euclideanBall (0 : Vec d) (1 / 4))) ≤
          ENNReal.ofReal ((C / (1 - q) ^ C) ^ Real.sqrt Λ) *
            essInf (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (euclideanBall (0 : Vec d) (1 / 4)))

/-- Conclusion of the statement `exists_harnack_constant` (after `(d) (hd)`). -/
def HarnackConcl (d : ℕ) : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 < u.toFun x) →
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u (0 : Vec d → ℝ) 0 →
        essSup (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
          ENNReal.ofReal (Real.exp (C * Real.sqrt Λ)) *
            essInf (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))
/-- Affine change of variables `y ↦ x₀ + r y` for weak supersolutions on the unit ball
(interface for the class-stability toolbox).  The transformed function is given by its
pointwise formula. -/
def SuperAffineTransfer (d : ℕ) : Prop :=
    ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ (x₀ : Vec d) (r : ℝ), 0 < r → euclideanBall x₀ r ⊆ euclideanBall (0 : Vec d) 1 →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSuperharmonicOn a (euclideanBall (0 : Vec d) 1) u →
        ∃ v : H1Function (euclideanBall (0 : Vec d) 1),
          (∀ y, v.toFun y = u.toFun (x₀ + r • y)) ∧
          IsWeakDivergenceFormSuperharmonicOn (fun y => a (x₀ + r • y))
            (euclideanBall (0 : Vec d) 1) v

/-- Affine change of variables `y ↦ x₀ + r y` together with the affine change
`u ↦ c + s u` of the dependent variable, for weak solutions on the unit ball
(interface for the class-stability toolbox). -/
def SolAffineTransfer (d : ℕ) : Prop :=
    ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ (x₀ : Vec d) (r : ℝ), 0 < r → euclideanBall x₀ r ⊆ euclideanBall (0 : Vec d) 1 →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u (0 : Vec d → ℝ) 0 →
      ∀ s c : ℝ,
        ∃ v : H1Function (euclideanBall (0 : Vec d) 1),
          (∀ y, v.toFun y = c + s * u.toFun (x₀ + r • y)) ∧
          IsWeakDivergenceFormSolutionOn (fun y => a (x₀ + r • y))
            (euclideanBall (0 : Vec d) 1) v (0 : Vec d → ℝ) 0

end PDE.DGNMAssembly
