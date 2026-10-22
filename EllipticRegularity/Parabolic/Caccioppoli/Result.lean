module

public import EllipticRegularity.Parabolic.Caccioppoli.Assembly
public import EllipticRegularity.Parabolic.Energy.Result

/-!
# Parabolic Caccioppoli inequality (Lemma 5.8)

`PDE.Parabolic.caccioppoli` combines `energy_identity` with the hypothesis-taking variant.
-/

@[expose] public section

namespace PDE

namespace Parabolic

open MeasureTheory Set

/-- The parabolic Caccioppoli inequality (Lemma 5.8), given the energy identity for
`u` and `φ`. -/
theorem caccioppoli_of_energy_identity (d : ℕ) (lam Lam : ℝ) (a : ParCoeffField d)
    (ha : IsParabolicCoeff lam Lam a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (φ : ParCutoff (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (t₁ : ℝ) (ht₁ : t₁ ∈ Ioc (-1 : ℝ) 0)
    (henergy : ParabCaccioppoli.EnergyConclusion a (euclideanBall (0 : Vec d) 1)
      (Ioc (-1 : ℝ) 0) u φ) :
    (∫⁻ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) t₁,
        ENNReal.ofReal (φ.toFun z ^ 2 * vecDot (u.grad z) (matVecMul (a z) (u.grad z)))) +
      (∫⁻ x in euclideanBall (0 : Vec d) 1,
        ENNReal.ofReal (φ.toFun (x, t₁) ^ 2 * u.toFun (x, t₁) ^ 2))
      ≤ ∫⁻ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) t₁,
          ENNReal.ofReal (u.toFun z ^ 2 *
            (2 * |φ.toFun z| * |parTimeDeriv φ.toFun z| +
              4 * Lam * vecNormSq (parSpaceGrad φ.toFun z))) ∧
    (∫⁻ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) t₁,
          ENNReal.ofReal (u.toFun z ^ 2 *
            (2 * |φ.toFun z| * |parTimeDeriv φ.toFun z| +
              4 * Lam * vecNormSq (parSpaceGrad φ.toFun z)))) < ⊤ :=
  ParabCaccioppoli.caccioppoli_of_energy d lam Lam a ha u φ t₁ ht₁ henergy

/-- The parabolic Caccioppoli inequality (Lemma 5.8), (statement of `PDE.parabCaccioppoli`). -/
theorem caccioppoli (d : ℕ) (lam Lam : ℝ) (a : ParCoeffField d)
    (ha : IsParabolicCoeff lam Lam a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (hu : IsParabolicWeakSolution a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u)
    (φ : ParCutoff (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (t₁ : ℝ) (ht₁ : t₁ ∈ Ioc (-1 : ℝ) 0) :
    (∫⁻ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) t₁,
        ENNReal.ofReal (φ.toFun z ^ 2 * vecDot (u.grad z) (matVecMul (a z) (u.grad z)))) +
      (∫⁻ x in euclideanBall (0 : Vec d) 1,
        ENNReal.ofReal (φ.toFun (x, t₁) ^ 2 * u.toFun (x, t₁) ^ 2))
      ≤ ∫⁻ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) t₁,
          ENNReal.ofReal (u.toFun z ^ 2 *
            (2 * |φ.toFun z| * |parTimeDeriv φ.toFun z| +
              4 * Lam * vecNormSq (parSpaceGrad φ.toFun z))) ∧
    (∫⁻ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) t₁,
          ENNReal.ofReal (u.toFun z ^ 2 *
            (2 * |φ.toFun z| * |parTimeDeriv φ.toFun z| +
              4 * Lam * vecNormSq (parSpaceGrad φ.toFun z)))) < ⊤ :=
  caccioppoli_of_energy_identity d lam Lam a ha u φ t₁ ht₁
    (energy_identity d lam Lam _ (isOpen_euclideanBall _ _) _ Set.ordConnected_Ioc a ha u hu φ)

end Parabolic

end PDE
