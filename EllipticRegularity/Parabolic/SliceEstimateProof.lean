module

public import EllipticRegularity.Parabolic.SliceEstimate.Result

/-!
# Proof of `PDE.parabSliceEstimate` (Lemma 5.10)

Thin wrapper around `PDE.Parabolic.slice_estimate` (full proof in
`EllipticRegularity/Parabolic/SliceEstimate/`).
-/

@[expose] public section

namespace PDE.ParabSliceEstimateProof

open MeasureTheory Set PDE

/-- The parabolic slice estimate, with the type of `PDE.parabSliceEstimate`. -/
theorem result (d : ℕ) (lam Lam : ℝ) (a₀ : Vec d → Mat d)
    (ha : IsParabolicCoeff lam Lam (fun z : Vec d × ℝ => a₀ z.1)
      (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (hu : IsParabolicWeakSolution (fun z : Vec d × ℝ => a₀ z.1)
      (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u)
    (v : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (hv : ∀ ψ : ParTestFunction (euclideanBall (0 : Vec d) 1) (interior (Ioc (-1 : ℝ) 0)),
      ∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0, v.toFun z * ψ.toFun z =
        -∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0,
          u.toFun z * parTimeDeriv ψ.toFun z)
    (φ : ParCutoff (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (hφ : ∀ z ∈ euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0, |φ.toFun z| ≤ 1) :
    (∫⁻ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0 ∩ {z | φ.toFun z ≠ 0},
        ENNReal.ofReal (vecDot (u.grad z)
          (matVecMul (symmPart (a₀ z.1)) (u.grad z)))) < ⊤ ∧
    ∀ᵐ t ∂(volume.restrict (Ioc (-1 : ℝ) 0)),
      (∫⁻ x in euclideanBall (0 : Vec d) 1,
          ENNReal.ofReal (φ.toFun (x, t) ^ 4 * vecDot (u.grad (x, t))
            (matVecMul (symmPart (a₀ x)) (u.grad (x, t)))))
        ≤ 7 * ENNReal.ofReal (Lam / lam) *
          (4 * eLpNormEssSup (fun z => parTimeDeriv φ.toFun z)
              (volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)) +
            16 * ENNReal.ofReal Lam *
              eLpNormEssSup (fun z => Real.sqrt (vecNormSq (parSpaceGrad φ.toFun z)))
                (volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)) ^ 2) *
          ∫⁻ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0 ∩ {z | φ.toFun z ≠ 0},
            ENNReal.ofReal (vecDot (u.grad z)
              (matVecMul (symmPart (a₀ z.1)) (u.grad z))) :=
  PDE.Parabolic.slice_estimate d lam Lam a₀ ha u hu v hv φ hφ

end PDE.ParabSliceEstimateProof
