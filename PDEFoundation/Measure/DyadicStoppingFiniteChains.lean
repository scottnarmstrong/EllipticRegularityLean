module

public import PDEFoundation.Measure.DyadicStoppingGenerationVolume

/-! # Almost every recursive dyadic stopping chain is finite -/

@[expose] public section

namespace PDE

open BoxIntegral MeasureTheory Set Filter Topology
open scoped ENNReal

/-- Recursive stopping regions decrease with the generation. -/
theorem antitone_dyadicStoppingRegion {d m : ℕ} (I : Box (Fin d))
    (g : Vec d → Vec m) : Antitone (dyadicStoppingRegion I g) :=
  antitone_nat_of_succ_le (dyadicStoppingRegion_succ_subset I g)

theorem measurableSet_iInter_dyadicStoppingRegion {d m : ℕ}
    (I : Box (Fin d)) (g : Vec d → Vec m) :
    MeasurableSet (⋂ n, dyadicStoppingRegion I g n) :=
  MeasurableSet.iInter (measurableSet_dyadicStoppingRegion I g)

/-- The set of points lying in every stopping generation has zero volume. -/
theorem volume_iInter_dyadicStoppingRegion_eq_zero {d m : ℕ}
    (I : Box (Fin d)) (g : Vec d → Vec m)
    (hg : ∀ i : Fin m, MemLp (fun x => g x i) 2 (volumeOn (I : Set (Vec d)))) :
    volume (⋂ n, dyadicStoppingRegion I g n) = 0 := by
  let V := volume (⋂ n, dyadicStoppingRegion I g n)
  let R := volume (I : Set (Vec d))
  have hbound (n : ℕ) : V ≤ ((4 : ℝ≥0∞)⁻¹) ^ n * R := by
    exact (measure_mono (iInter_subset (fun n => dyadicStoppingRegion I g n) n)).trans
      (volume_dyadicStoppingRegion_le I g hg n)
  have hquarter : (4 : ℝ≥0∞)⁻¹ < 1 := by norm_num
  have hlim : Tendsto (fun n : ℕ => ((4 : ℝ≥0∞)⁻¹) ^ n * R)
      atTop (𝓝 0) := by
    have hRtop : R ≠ ⊤ := (I.measure_coe_lt_top volume).ne
    have hp := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hquarter
    have hmul := (ENNReal.continuous_mul_const hRtop).continuousAt.tendsto.comp hp
    simpa only [zero_mul] using! hmul
  have hV0 : V ≤ 0 := ge_of_tendsto hlim (Filter.Eventually.of_forall hbound)
  exact le_zero_iff.mp hV0

/-- Almost every point exits the recursive stopping regions at a finite
generation. -/
theorem ae_exists_not_mem_dyadicStoppingRegion {d m : ℕ}
    (I : Box (Fin d)) (g : Vec d → Vec m)
    (hg : ∀ i : Fin m, MemLp (fun x => g x i) 2 (volumeOn (I : Set (Vec d)))) :
    ∀ᵐ x ∂volume, ∃ n, x ∉ dyadicStoppingRegion I g n := by
  have h := (measure_eq_zero_iff_ae_notMem.mp
    (volume_iInter_dyadicStoppingRegion_eq_zero I g hg))
  filter_upwards [h] with x hx
  simpa only [Set.mem_iInter, not_forall] using hx

end PDE
