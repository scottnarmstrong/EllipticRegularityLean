module

public import EllipticRegularity.Parabolic.Energy.Conclusion

/-!
# The energy identity (Lemma 5.6)

`PDE.Parabolic.energy_identity` is the full proof of the statement `PDE.parabEnergy`.
See `Energy/README.md` for the API.
-/

@[expose] public section

namespace PDE.Parabolic

open MeasureTheory Set PDE PDE.Parabolic.Energy

/-- Lemma 5.6: energy identity, with explicit integrability and continuity of `E`
(local absolute continuity follows from the identity). -/
theorem energy_identity (d : ℕ) (lam Lam : ℝ) (U : Set (Vec d)) (hU : IsOpen U)
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
            (φ.toFun z ^ 2 • u.grad z + (2 * φ.toFun z * u.toFun z) • parSpaceGrad φ.toFun z) :=
  ⟨fun _t ht => slice_integrable hU u φ ht, energy_continuousOn hU hI ha u hu φ,
    fun _s _t hs ht hst => slab_conclusion hU hI ha u hu φ hs ht hst⟩

end PDE.Parabolic
