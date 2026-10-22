module

public import EllipticRegularity.Parabolic.Cauchy.Lions.ClosureData
public import EllipticRegularity.Parabolic.Cauchy.Lions.MollifiedLocalBound
public import EllipticRegularity.Parabolic.Energy.Mollifier

/-! # Local slice integrability of the continuous mollified representatives -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace PDE.Parabolic.Lions

/-- Each fixed spatial mollification has an `L²_loc` slice at every time in the closed horizon.
The bound here may depend on the mollification scale; obtaining a scale independent global slice
bound is the remaining energy step. -/
theorem exists_cauchy_mollified_alltime_sliceL2loc
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
        w z = PDE.Parabolic.Energy.mollT a univ (cauchyEnergyValue u) z) ∧
      (∀ t ∈ Icc s T, ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun x => w (x, t)) 2 (volume.restrict K)) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ x : Vec d, ∀ t ∈ Icc s T, |w (x, t)| ≤ B := by
  obtain ⟨w, hwm, hwcont, hwsec, hwae, B, hB0, hB⟩ :=
    exists_cauchy_mollified_global_pointwise_bound hsT ha haε f hf u hrep
  refine ⟨w, hwm, hwcont, hwsec, hwae, ?_, ⟨B, hB0, hB⟩⟩
  intro t ht K hK
  let μK : Measure (Vec d) := volume.restrict K
  let : IsFiniteMeasure μK := ⟨by
    change (volume.restrict K) univ < ⊤
    rw [Measure.restrict_apply_univ]
    exact hK.measure_lt_top⟩
  have hsection : Measurable (fun x : Vec d => w (x, t)) :=
    hwm.comp (measurable_id.prodMk measurable_const)
  have hbound : ∀ᵐ x ∂μK, ‖w (x, t)‖ ≤ B := by
    filter_upwards [] with x
    rw [Real.norm_eq_abs]
    exact hB x t ht
  exact MemLp.of_bound hsection.aestronglyMeasurable B hbound

end PDE.Parabolic.Lions
