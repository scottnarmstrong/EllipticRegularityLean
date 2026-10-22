module

public import EllipticRegularity.Parabolic.Caccioppoli.Result

/-!
# Proof of `PDE.parabCaccioppoli` (Lemma 5.8)

Thin wrapper around `PDE.Parabolic.caccioppoli` (full proof in `Parabolic/Caccioppoli/`).
-/

@[expose] public section

namespace PDE.ParabCaccioppoliProof

open MeasureTheory Set PDE

/-- The parabolic Caccioppoli inequality, with the type of `PDE.parabCaccioppoli`. -/
theorem result (d : ℕ) (lam Lam : ℝ) (a : ParCoeffField d)
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
  PDE.Parabolic.caccioppoli d lam Lam a ha u hu φ t₁ ht₁

end PDE.ParabCaccioppoliProof
