module

public import EllipticRegularity.Parabolic.SliceEstimateProof

@[expose] public section

namespace PDE

open MeasureTheory Set

/-- Lemma 5.10: time slice estimate on `(-1,0] × B₁` for a time-independent coefficient
field and `v = ∂ₜu ∈ H¹_par`; for a.e. `t`,
`∫_{B₁} φ⁴ ∇u·s∇u (t,·) ≤ 7 (Λ/λ) M G`, `M = 4‖∂ₜφ‖_∞ + 16 Λ ‖∇φ‖_∞²`,
`G = ∫_{φ≠0} ∇u·s∇u`, and `G < ∞`. -/
theorem parabSliceEstimate (d : ℕ) (lam Lam : ℝ) (a₀ : Vec d → Mat d)
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
              (matVecMul (symmPart (a₀ z.1)) (u.grad z))) := by exact PDE.ParabSliceEstimateProof.result d lam Lam a₀ ha u hu v hv φ hφ

end PDE
