module

public import EllipticRegularity.Ch4.GreenDecay.MaxPrinciple

/-!
# `greenMaxPrinciple_full`

The exact type of the statement `greenMaxPrinciple` (Lemma 4.34).
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4GreenDecay

open MeasureTheory PDE

/-- Weak maximum principle: exact type of the statement `greenMaxPrinciple`. -/
theorem greenMaxPrinciple_full (d : ℕ) (hd : 2 ≤ d) (Λ R : ℝ) (hR : 0 < R) (a : CoeffField d)
    (hmeas : ∀ i j : Fin d,
      AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) R)))
    (hell : ∀ x ∈ euclideanBall (0 : Vec d) R, IsEllipticMatrix 1 Λ (a x))
    (b : CoeffField d) (hb : b = a ∨ b = adjointCoeffField a) :
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
      ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) R)), 0 ≤ v.toH1Function.toFun x) := by
  have hd0 : 0 < d := by omega
  obtain ⟨-, hbell⟩ := adjoint_coeff_hyps hmeas hell hb
  have h1 : ∀ v : H10Function (euclideanBall (0 : Vec d) R),
      (∀ φ : H10Function (euclideanBall (0 : Vec d) R),
        (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) R)), 0 ≤ φ.toH1Function.toFun x) →
        IntegrableOn (fun x => vecDot (φ.toH1Function.grad x) (matVecMul (b x) (v.toH1Function.grad x)))
            (euclideanBall (0 : Vec d) R) ∧
          0 ≤ ∫ x in euclideanBall (0 : Vec d) R,
            vecDot (φ.toH1Function.grad x) (matVecMul (b x) (v.toH1Function.grad x))) →
      ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) R)), 0 ≤ v.toH1Function.toFun x :=
    fun v hv => maxPrinciple_of_supersolution hd0 hR hbell v hv
  refine ⟨h1, fun g _ hg v hv => h1 v (fun φ hφ => supersolution_of_source_nonneg hg hv φ hφ)⟩

end PDE.Ch4GreenDecay
