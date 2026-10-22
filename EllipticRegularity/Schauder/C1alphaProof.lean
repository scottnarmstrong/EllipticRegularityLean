module

public import EllipticRegularity.Schauder.CalphaProof
public import PDEFoundation.Regularity.FieldHolderSeminorm
public import EllipticRegularity.Schauder.C1alphaOneDimensional
public import EllipticRegularity.Schauder.C1alphaHigherDimensional

/-! # Proof of `PDE.exists_schauderC1alpha_constant` -/

@[expose] public section

namespace PDE.SchauderC1Proof

open MeasureTheory Filter
open scoped ENNReal Topology

theorem result
    {d : ℕ} (hd : 0 < d) {Λ : ℝ} :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ}, 0 < α → α < 1 →
      ∀ {r₀ : ℝ}, 0 < r₀ → r₀ ≤ 1 / 4 →
      ∀ (a : CoeffField d) (F : Vec d → Vec d),
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ ha : ∃ K : ℝ, 0 ≤ K ∧
        EuclideanMatrixHolderSeminormLE (euclideanBall (0 : Vec d) 1) a α K,
      ∀ hF : ∃ K : ℝ, 0 ≤ K ∧
        EuclideanFieldHolderSeminormLE (euclideanBall (0 : Vec d) 1) F α K,
      r₀ ^ α * euclideanMatrixHolderSeminormOn (euclideanBall (0 : Vec d) 1) a α ha ≤
        C⁻¹ * α * (1 - α) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u 0 F →
      ∃ G : Vec d → Vec d,
      ∃ hG : ∃ K : ℝ, 0 ≤ K ∧
        EuclideanFieldHolderSeminormLE (euclideanBall (0 : Vec d) (1 / 2)) G α K,
      ∃ hgrad : MemLp (fun x => vecEuclideanNorm (u.grad x)) ∞
        (volumeOn (euclideanBall (0 : Vec d) (1 / 2))),
      G =ᵐ[volumeOn (euclideanBall (0 : Vec d) (1 / 2))] u.grad ∧
      euclideanFieldLpNormOn (euclideanBall (0 : Vec d) (1 / 2)) ∞ u.grad hgrad +
        r₀ ^ α * euclideanFieldHolderSeminormOn
          (euclideanBall (0 : Vec d) (1 / 2)) G α hG ≤
        (C / α ^ 2) * (r₀ ^ (-(d : ℝ) / 2) *
          Real.sqrt (integralAverage (euclideanBall (0 : Vec d) 1)
            (fun x => vecNormSq (u.grad x))) +
          r₀ ^ α / (1 - α) *
            euclideanFieldHolderSeminormOn (euclideanBall (0 : Vec d) 1) F α hF) := by
  by_cases hd1 : d = 1
  · subst d
    simpa only [Nat.cast_one] using
      (exists_schauderC1alpha_constant_oneDimensional (Λ := Λ))
  · exact exists_schauderC1alpha_constant_higherDimensional (by omega : 2 ≤ d)

end PDE.SchauderC1Proof
