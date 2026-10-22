module

public import EllipticRegularity.Parabolic.Cauchy.Lions.ClosureData
public import EllipticRegularity.Parabolic.Cauchy.Lions.PairingTrace
public import EllipticRegularity.Parabolic.Cauchy.LionsBound.GlobalSliceBound
public import EllipticRegularity.Parabolic.Cauchy.LionsRep.MollifiedGlobalBound

/-! # Uniform bounds for the continuous scalar traces -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace PDE.Parabolic.Lions

/-- Almost every spatial slice of the Lions value pairs with any spatial `L²` function with the
Hilbert-space bound coming from the global slice estimate. No smoothness or compact support is
needed for this almost-everywhere estimate. -/
theorem cauchyValuePairing_ae_slice_bound
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 (volume : Measure (Vec d)))
    (u : CauchyX d s T) {u₀ : CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (ψ : Vec d → ℝ) (hψ : MemLp ψ 2 (volume : Measure (Vec d))) :
    ∀ᵐ t ∂(volume.restrict (Icc s T)),
      |cauchyValuePairing u ψ t| ≤
        Real.sqrt (PDE.Parabolic.LionsRep.cauchySliceEnergyBound (a := a) f u) *
          (eLpNorm ψ 2 (volume : Measure (Vec d))).toReal := by
  let C : ℝ := Real.sqrt
    (PDE.Parabolic.LionsRep.cauchySliceEnergyBound (a := a) f u)
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hslice := cauchyEnergyValue_ae_slice_norm_bound hsT ha f hf u hclose hrep
  have hslice' : ∀ᵐ t ∂(volume.restrict (Icc s T)),
      MemLp (fun x : Vec d => cauchyEnergyValue u (x, t)) 2
          (volume : Measure (Vec d)) ∧
        eLpNorm (fun x : Vec d => cauchyEnergyValue u (x, t)) 2 volume ≤
          ENNReal.ofReal C := by
    simpa [C, PDE.Parabolic.LionsRep.cauchySliceEnergyBound] using hslice
  filter_upwards [hslice'] with t ht
  let htLp := ht.1.toLp (fun x : Vec d => cauchyEnergyValue u (x, t))
  have hnorm : ‖htLp‖ ≤ C := by
    rw [Lp.norm_toLp]
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top ht.2
    simpa [ENNReal.toReal_ofReal hC] using hreal
  have hinner : cauchyValuePairing u ψ t =
      inner ℝ htLp (hψ.toLp ψ) := by
    rw [cauchyValuePairing, MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ht.1.coeFn_toLp, hψ.coeFn_toLp] with x hx hψx
    rw [hx, hψx]
    change cauchyEnergyValue u (x, t) * ψ x = ψ x * cauchyEnergyValue u (x, t)
    ring
  calc
    |cauchyValuePairing u ψ t| = |inner ℝ htLp (hψ.toLp ψ)| := by rw [hinner]
    _ ≤ ‖htLp‖ * ‖hψ.toLp ψ‖ := abs_real_inner_le_norm _ _
    _ ≤ C * ‖hψ.toLp ψ‖ := mul_le_mul hnorm le_rfl (norm_nonneg _) hC
    _ = C * (eLpNorm ψ 2 volume).toReal := by rw [Lp.norm_toLp]
    _ = _ := rfl

/-- The continuous scalar trace of a smooth compactly supported spatial pairing inherits the
uniform spatial `L²` bound of the unmollified Lions field.  The estimate is valid at every time,
including both endpoints; the input slice bound itself is only almost everywhere in time. -/
theorem exists_cauchy_scalar_pairing_sliceNorm_bound
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 (volume : Measure (Vec d)))
    (u : CauchyX d s T) {u₀ : CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (ψ : Vec d → ℝ) (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    ∃ v : ℝ → ℝ, ContinuousOn v (Icc s T) ∧
      cauchyValuePairing u ψ =ᵐ[volume.restrict (Icc s T)] v ∧
      v s = ∫ x, f x * ψ x ∧
      ∀ t ∈ Icc s T,
        |v t| ≤ Real.sqrt (PDE.Parabolic.LionsRep.cauchySliceEnergyBound (a := a) f u) *
          (eLpNorm ψ 2 (volume : Measure (Vec d))).toReal := by
  obtain ⟨v, hvcont, hvae, hvis, _hvinc⟩ :=
    exists_cauchy_scalar_pairing_representative hsT ha f hf u hrep ψ hψ hψc
  let C : ℝ := Real.sqrt
    (PDE.Parabolic.LionsRep.cauchySliceEnergyBound (a := a) f u)
  have hψLp : MemLp ψ 2 (volume : Measure (Vec d)) :=
    hψ.continuous.memLp_of_hasCompactSupport hψc
  have hpairBound := cauchyValuePairing_ae_slice_bound hsT ha f hf u hclose hrep ψ hψLp
  have hvBoundAE : ∀ᵐ t ∂(volume.restrict (Icc s T)),
      |v t| ≤ C * (eLpNorm ψ 2 volume).toReal := by
    filter_upwards [hpairBound, hvae] with t hpair heq
    change |cauchyValuePairing u ψ t| ≤ C * (eLpNorm ψ 2 volume).toReal at hpair
    rw [← heq]
    exact hpair
  have hmaxAE :
      (fun t => max |v t| (C * (eLpNorm ψ 2 volume).toReal)) =ᵐ[
        volume.restrict (Icc s T)] fun _ => C * (eLpNorm ψ 2 volume).toReal := by
    filter_upwards [hvBoundAE] with t ht
    exact max_eq_right ht
  have hmaxCont : ContinuousOn
      (fun t => max |v t| (C * (eLpNorm ψ 2 volume).toReal)) (Icc s T) := by
    apply (continuousOn_iff_continuous_domRestrict).2
    change Continuous fun t : Icc s T => max |v t.1| (C * (eLpNorm ψ 2 volume).toReal)
    exact hvcont.domRestrict.abs.max continuous_const
  have hmaxEq := Measure.eqOn_Icc_of_ae_eq volume (ne_of_lt hsT) hmaxAE hmaxCont
    continuousOn_const
  refine ⟨v, hvcont, hvae, hvis, ?_⟩
  intro t ht
  have hEq := hmaxEq ht
  exact (max_eq_right_iff).1 hEq

end PDE.Parabolic.Lions
