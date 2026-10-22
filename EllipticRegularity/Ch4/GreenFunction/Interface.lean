module

public import PDEFoundation
public import EllipticRegularity.Green.GreenFunctionDef

/-!
# Interface statements for the Green function

Each `...Concl d` below is, verbatim, the body after `(d) (hd)` of the corresponding
statement (`PDE.greenDirichlet`, `PDE.greenMaxPrinciple`).  The Green function theorems
take these as explicit hypotheses, which are instantiated with the proved theorems.

We also record two small algebraic facts used throughout the Green function development.
-/

@[expose] public section

namespace PDE.Ch4Green

open MeasureTheory PDE

/-- Conclusion of the statement `greenDirichlet` (after `(d) (hd)`). -/
def GreenDirichletConcl (d : ℕ) : Prop :=
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (Λ R : ℝ), 0 < R → ∀ a : CoeffField d,
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) R))) →
      (∀ x ∈ euclideanBall (0 : Vec d) R, IsEllipticMatrix 1 Λ (a x)) →
      ∀ b : CoeffField d, (b = a ∨ b = adjointCoeffField a) →
      ∀ (g : Vec d → ℝ) (F : Vec d → Vec d),
        MemL2On (euclideanBall (0 : Vec d) R) g →
        MemVectorL2On (euclideanBall (0 : Vec d) R) F →
        (∃ v : H10Function (euclideanBall (0 : Vec d) R),
          IsWeakDivergenceFormH10SolutionOn b (euclideanBall (0 : Vec d) R) v.toH1Function g F) ∧
        (∀ v w : H10Function (euclideanBall (0 : Vec d) R),
          IsWeakDivergenceFormH10SolutionOn b (euclideanBall (0 : Vec d) R) v.toH1Function g F →
          IsWeakDivergenceFormH10SolutionOn b (euclideanBall (0 : Vec d) R) w.toH1Function g F →
            v.toH1Function.toFun =ᵐ[volumeOn (euclideanBall (0 : Vec d) R)] w.toH1Function.toFun ∧
            v.toH1Function.grad =ᵐ[volumeOn (euclideanBall (0 : Vec d) R)] w.toH1Function.grad) ∧
        (F = (0 : Vec d → Vec d) →
          ∀ v : H10Function (euclideanBall (0 : Vec d) R),
          IsWeakDivergenceFormH10SolutionOn b (euclideanBall (0 : Vec d) R) v.toH1Function g F →
            eLpNorm (fun x => vecEuclideanNorm (v.toH1Function.grad x)) 2
                (volumeOn (euclideanBall (0 : Vec d) R)) ≤
              ENNReal.ofReal (C₁ * R) * eLpNorm g 2 (volumeOn (euclideanBall (0 : Vec d) R)) ∧
            eLpNorm v.toH1Function.toFun 2 (volumeOn (euclideanBall (0 : Vec d) R)) ≤
              ENNReal.ofReal (C₁ ^ 2 * R ^ 2) *
                eLpNorm g 2 (volumeOn (euclideanBall (0 : Vec d) R)))

/-- Conclusion of the statement `greenMaxPrinciple` (after `(d) (hd)`). -/
def GreenMaxPrincipleConcl (d : ℕ) : Prop :=
    ∀ (Λ R : ℝ) (_hR : 0 < R) (a : CoeffField d)
    (_hmeas : ∀ i j : Fin d,
      AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) R)))
    (_hell : ∀ x ∈ euclideanBall (0 : Vec d) R, IsEllipticMatrix 1 Λ (a x))
    (b : CoeffField d) (_hb : b = a ∨ b = adjointCoeffField a),
    (∀ v : H10Function (euclideanBall (0 : Vec d) R),
      (∀ φ : H10Function (euclideanBall (0 : Vec d) R),
        (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) R)), 0 ≤ φ.toH1Function.toFun x) →
        IntegrableOn (fun x => vecDot (φ.toH1Function.grad x) (matVecMul (b x) (v.toH1Function.grad x)))
            (euclideanBall (0 : Vec d) R) ∧
          0 ≤ ∫ x in euclideanBall (0 : Vec d) R,
            vecDot (φ.toH1Function.grad x) (matVecMul (b x) (v.toH1Function.grad x))) →
      ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) R)), 0 ≤ v.toH1Function.toFun x) ∧
    (∀ g : Vec d → ℝ, MemL2On (euclideanBall (0 : Vec d) R) g →
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) R)), 0 ≤ g x) →
      ∀ v : H10Function (euclideanBall (0 : Vec d) R),
      IsWeakDivergenceFormH10SolutionOn b (euclideanBall (0 : Vec d) R) v.toH1Function g
        (0 : Vec d → Vec d) →
      ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) R)), 0 ≤ v.toH1Function.toFun x)

variable {d : ℕ}

/-- Transposition moves a matrix across the Euclidean dot product. -/
theorem vecDot_matVecMul_matTranspose (A : Mat d) (ξ ζ : Vec d) :
    vecDot (matVecMul (matTranspose A) ξ) ζ = vecDot ξ (matVecMul A ζ) := by
  simp only [vecDot, matVecMul, matTranspose, Matrix.transpose_apply, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

@[simp] theorem vecDot_zero_left (y : Vec d) : vecDot (0 : Vec d) y = 0 := by
  simp [vecDot]

@[simp] theorem vecDot_zero_right (y : Vec d) : vecDot y (0 : Vec d) = 0 := by
  simp [vecDot]

/-- Ellipticity with lower constant `1` on a nonempty set forces `1 ≤ Λ`. -/
theorem one_le_of_elliptic {Λ : ℝ} {U : Set (Vec d)} {a : CoeffField d}
    (hne : U.Nonempty) (hell : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x)) : 1 ≤ Λ := by
  obtain ⟨x, hx⟩ := hne
  exact (hell x hx).lam_le_Lam

/-- The adjoint field is elliptic with the same constants. -/
theorem elliptic_adjoint {Λ : ℝ} {U : Set (Vec d)} {a : CoeffField d}
    (hell : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x)) :
    ∀ x ∈ U, IsEllipticMatrix 1 Λ (adjointCoeffField a x) := fun x hx =>
  isEllipticMatrix_transpose (hell x hx)

/-- The adjoint field has a.e.-measurable entries. -/
theorem aemeasurable_adjoint {U : Set (Vec d)} {a : CoeffField d}
    (hmeas : ∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn U)) :
    ∀ i j : Fin d, AEMeasurable (fun x => adjointCoeffField a x i j) (volumeOn U) :=
  fun i j => by simpa [adjointCoeffField_apply, matTranspose] using hmeas j i

end PDE.Ch4Green
