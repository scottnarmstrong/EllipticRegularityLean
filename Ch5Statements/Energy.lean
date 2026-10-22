module

public import EllipticRegularity.Parabolic.EnergyProof

@[expose] public section

namespace PDE

open MeasureTheory Set

/-- Lemma 5.6: energy identity, with explicit integrability and continuity of `E`
(local absolute continuity follows from the identity). -/
theorem parabEnergy (d : ℕ) (lam Lam : ℝ) (U : Set (Vec d)) (hU : IsOpen U)
    (I : Set ℝ) (hI : I.OrdConnected) (a : ParCoeffField d)
    (ha : IsParabolicCoeff lam Lam a U I)
    (u : ParH1Function U I) (hu : IsParabolicWeakSolution a U I u)
    (φ : ParCutoff U I) :
    (∀ t ∈ I, Integrable (fun x => φ.toFun (x, t) ^ 2 * u.toFun (x, t) ^ 2) (volume.restrict U)) ∧
    ContinuousOn (fun t => (1 / 2 : ℝ) * ∫ x in U, φ.toFun (x, t) ^ 2 * u.toFun (x, t) ^ 2) I ∧
    ∀ s t : ℝ, s ∈ I → t ∈ I → s < t →
      IntegrableOn (fun z => u.toFun z ^ 2 * φ.toFun z * parTimeDeriv φ.toFun z)
          (U ×ˢ Ioc s t) ∧
      IntegrableOn (fun z => vecDot (matVecMul (a z) (u.grad z))
          (φ.toFun z ^ 2 • u.grad z + (2 * φ.toFun z * u.toFun z) • parSpaceGrad φ.toFun z))
          (U ×ˢ Ioc s t) ∧
      ((1 / 2 : ℝ) * ∫ x in U, φ.toFun (x, t) ^ 2 * u.toFun (x, t) ^ 2) -
          (1 / 2 : ℝ) * ∫ x in U, φ.toFun (x, s) ^ 2 * u.toFun (x, s) ^ 2 =
        (∫ z in U ×ˢ Ioc s t, u.toFun z ^ 2 * φ.toFun z * parTimeDeriv φ.toFun z) -
          ∫ z in U ×ˢ Ioc s t, vecDot (matVecMul (a z) (u.grad z))
            (φ.toFun z ^ 2 • u.grad z + (2 * φ.toFun z * u.toFun z) • parSpaceGrad φ.toFun z) := by exact PDE.ParabEnergyProof.result d lam Lam U hU I hI a ha u hu φ

end PDE
