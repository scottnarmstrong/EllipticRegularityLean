module

public import EllipticRegularity.Parabolic.Cauchy.Lions.ClosureData
public import EllipticRegularity.Parabolic.Cauchy.Lions.Representative

/-! # Joint representatives of spatially mollified Lions fields -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace PDE.Parabolic.Lions

/-- The exponentially rescaled Lions value field has a strongly measurable representative on the
ambient space-time product. -/
theorem cauchyEnergyValue_stronglyMeasurable {d : ℕ} {s T : ℝ}
    (u : CauchyX d s T) : StronglyMeasurable (cauchyEnergyValue u) := by
  have hval : StronglyMeasurable (cauchyJointValue u) := by
    change StronglyMeasurable (fun z => (u z).fst)
    have hu : StronglyMeasurable (fun z : Vec d × ℝ => u z) :=
      Lp.stronglyMeasurable u
    exact (WithLp.fstL 2 ℝ ℝ (HilbertVec d)).continuous.comp_stronglyMeasurable
      hu
  have hw : StronglyMeasurable (cauchyWeight (s := s) : Vec d × ℝ → ℝ) :=
    Real.continuous_exp.comp_stronglyMeasurable
      (continuous_snd.sub continuous_const).stronglyMeasurable
  exact hw.mul hval

/-- Every spatial mollification of the Lions field has a jointly measurable representative whose
time sections are continuous at every spatial point. -/
theorem exists_cauchy_mollified_joint_representative
    {d : ℕ} {lam Lam s T a : ℝ} {A : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam A univ (Icc s T))
    (haε : 0 < a) (f : Vec d → ℝ) (hf : MemLp f 2 (volume : Measure (Vec d)))
    (u : CauchyX d s T)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u) :
    ∃ w : Vec d × ℝ → ℝ, Measurable w ∧
      (∀ x, ContinuousOn (fun t => w (x, t)) (Icc s T)) ∧
      (∀ x, (fun t => PDE.Parabolic.Energy.mollT a univ
        (cauchyEnergyValue u) (x, t)) =ᵐ[volume.restrict (Icc s T)]
          (fun t => w (x, t))) ∧
      (∀ᵐ z ∂(slabMeasure d s T),
        w z = PDE.Parabolic.Energy.mollT a univ (cauchyEnergyValue u) z) := by
  let raw : Vec d × ℝ → ℝ := cauchyEnergyValue u
  have hraw : StronglyMeasurable raw := by
    dsimp [raw]
    exact cauchyEnergyValue_stronglyMeasurable u
  let g : Vec d × ℝ → ℝ := PDE.Parabolic.Energy.mollT a univ raw
  have hg : StronglyMeasurable g := by
    dsimp [g]
    exact PDE.Parabolic.Energy.stronglyMeasurable_mollT MeasurableSet.univ hraw.measurable a
  have hpoint : ∀ x : Vec d, ∃ v : ℝ → ℝ,
      ContinuousOn v (Icc s T) ∧
      (fun t => g (x, t)) =ᵐ[
        volume.restrict (Icc s T)] v := by
    intro x
    obtain ⟨v, hv, hae, _h0, _hinc⟩ :=
      exists_cauchy_mollified_time_representative hsT ha haε f hf u hrep x
    refine ⟨v, hv, ?_⟩
    simpa [g, raw] using hae
  obtain ⟨w, hwm, hwcont, hwsec⟩ :=
    exists_measurable_continuousOn_timeRepresentative hsT hg hpoint
  have hprod : ∀ᵐ z ∂((volume : Measure (Vec d)).prod
      (volume.restrict (Icc s T))), w z = g z := by
    have hmeasEq : MeasurableSet {z : Vec d × ℝ | w z = g z} :=
      measurableSet_eq_fun hwm hg.measurable
    apply (Measure.ae_prod_iff_ae_ae hmeasEq).2
    filter_upwards [ae_of_all (volume : Measure (Vec d)) fun x => (hwsec x).symm] with x hx
    exact hx
  have hrestrict : (volume : Measure (Vec d)).prod
      (volume.restrict (Icc s T)) = slabMeasure d s T := by
    rw [slabMeasure, PDE.Parabolic.Energy.volume_restrict_prod]
    simp
  refine ⟨w, hwm, hwcont, ?_, ?_⟩
  · intro x
    simpa [g, raw] using hwsec x
  ·
    rw [← hrestrict]
    simpa [g, raw] using hprod

end PDE.Parabolic.Lions
