module

public import PDEFoundation.Measure.DyadicBoxMaximalWeak
public import PDEFoundation.Measure.LocalizedDistributionStrongNorm

/-! # Sharp strong maximal inequality on a dyadic root box -/

@[expose] public section

namespace PDE

open BoxIntegral MeasureTheory
open scoped ENNReal

/-- The actual dyadic maximal function on a root box has the sharp norm
bound `q/(q-1)`. The localized distribution premise is derived from the
literal first stopping cubes, not assumed. -/
theorem eLpNorm_dyadicBoxMaximal_le
    {d : ℕ} (I : Box (Fin d)) (b : Vec d → ℝ) {q : ℝ} (hq : 1 < q)
    (hb : MemLp b (ENNReal.ofReal q) (volume.restrict (I : Set (Vec d)))) :
    eLpNorm (dyadicBoxMaximal I b) (ENNReal.ofReal q)
        (volume.restrict (I : Set (Vec d))) ≤
      ENNReal.ofReal (q / (q - 1)) *
        eLpNorm b (ENNReal.ofReal q) (volume.restrict (I : Set (Vec d))) := by
  let μ := volume.restrict (I : Set (Vec d))
  let : IsFiniteMeasure μ := ⟨by
    simpa only [μ, Measure.restrict_apply_univ] using I.measure_coe_lt_top volume⟩
  apply eLpNorm_le_of_localized_distribution μ b hq hb
    (dyadicBoxMaximal I b) (measurable_dyadicBoxMaximal I b)
  intro t ht
  let A : Set (Vec d) := {x | ENNReal.ofReal t < dyadicBoxMaximal I b x}
  have hA : MeasurableSet A :=
    measurableSet_lt measurable_const (measurable_dyadicBoxMaximal I b)
  have hsub : A ⊆ (I : Set (Vec d)) := by
    intro x hx
    by_contra hnot
    have hz := dyadicBoxMaximal_eq_zero_of_notMem I b hnot
    change ENNReal.ofReal t < dyadicBoxMaximal I b x at hx
    rw [hz] at hx
    exact (not_lt_of_ge (zero_le)) hx
  have hmeasure : μ A = volume A := by
    rw [Measure.restrict_apply hA, Set.inter_eq_left.mpr hsub]
  have hintegral :
      (∫⁻ x in A, ENNReal.ofReal |b x| ∂μ) =
        ∫⁻ x in A, ENNReal.ofReal |b x| := by
    rw [Measure.restrict_restrict_of_subset hsub]
  change ENNReal.ofReal t * μ A ≤ ∫⁻ x in A, ENNReal.ofReal |b x| ∂μ
  rw [hmeasure, hintegral]
  exact ofReal_mul_volume_set_lt_dyadicBoxMaximal_le_lintegral I b t

end PDE
