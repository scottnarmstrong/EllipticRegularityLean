module

public import EllipticRegularity.Parabolic.Cauchy.Lions.ClosureData
public import EllipticRegularity.Parabolic.Cauchy.Lions.PairingWeakDerivative
public import EllipticRegularity.Parabolic.Cauchy.Lions.PairingLp
public import EllipticRegularity.Parabolic.Cauchy.Lions.ScalarTrace
public import EllipticRegularity.Parabolic.Cauchy.Lions.EndpointTest

/-! # Continuous representatives of smooth spatial pairings -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set
open scoped Interval

namespace PDE.Parabolic.Lions

/-- Every smooth compactly supported spatial pairing of the Lions field has a continuous scalar
time representative on the closed horizon, whose initial value is the corresponding pairing of
the datum. -/
theorem exists_cauchy_scalar_pairing_representative
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 (volume : Measure (Vec d)))
    (u : CauchyX d s T)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (ψ : Vec d → ℝ) (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    ∃ v : ℝ → ℝ, ContinuousOn v (Icc s T) ∧
      cauchyValuePairing u ψ =ᵐ[volume.restrict (Icc s T)] v ∧
      v s = ∫ x, f x * ψ x ∧
      ∀ x ∈ Icc s T, ∀ y ∈ Icc s T,
        v y - v x = ∫ t in x..y, -cauchyFluxPairing a u ψ t := by
  have hvalueLp : MemLp (cauchyValuePairing u ψ) 2 (volume.restrict (Icc s T)) :=
    cauchySpatialPairing_memLp (cauchyEnergyValue_memLp u)
      (memLp_space_of_continuous_compact hψ.continuous hψc)
  have hfluxLp : MemLp (cauchyFluxPairing a u ψ) 2 (volume.restrict (Icc s T)) :=
    cauchyFluxPairing_memLp ha u hψ hψc
  have hvalueOpen : MemLp (cauchyValuePairing u ψ) 2 (volume.restrict (Ioo s T)) := by
    rw [Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact hvalueLp
  have hweak := cauchyLions_pairing_hasWeakDerivOnIoo ha f hf u hrep ψ hψ hψc
  obtain ⟨θ, hθ, hθc, hθs, hθT⟩ := exists_cauchy_endpoint_test hsT
  have hBg : cauchyFluxPairing a u ψ =ᵐ[volume.restrict (Icc s T)]
      fun t => -(-cauchyFluxPairing a u ψ t) := by
    exact Filter.Eventually.of_forall fun _ => by ring
  have htrace : ∫ t in Icc s T,
      (-(cauchyValuePairing u ψ t * deriv θ t) +
        cauchyFluxPairing a u ψ t * θ t) = ∫ x, f x * ψ x := by
    simpa [hθs] using
      cauchyLions_pairing_testIdentity ha f hf u hrep ψ hψ hψc θ hθ hθc hθT
  obtain ⟨v, hvcont, hvAe, hvInit, hvInc⟩ :=
    exists_scalar_time_representative_with_initial_value hsT hvalueOpen hfluxLp.neg
      hweak hBg θ hθ hθT hθs htrace
  refine ⟨v, hvcont, hvAe, ?_, hvInc⟩
  simpa using hvInit

end PDE.Parabolic.Lions
