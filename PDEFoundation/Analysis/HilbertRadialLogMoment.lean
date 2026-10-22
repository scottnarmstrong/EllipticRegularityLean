module

public import PDEFoundation.Analysis.HilbertPolar
public import PDEFoundation.Analysis.HilbertBallAverage
public import PDEFoundation.Analysis.RadialLogMomentOneDimensional

/-! # Internal Hilbert radial logarithmic moments -/

@[expose] public section

open scoped Real
open MeasureTheory Metric Set

namespace PDE.Internal

noncomputable section

variable {d : ℕ}

private theorem finrank_hilbertVec : Module.finrank ℝ (HilbertVec d) = d := by
  calc
    Module.finrank ℝ (HilbertVec d) = Module.finrank ℝ (Fin d → ℝ) :=
      (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).finrank_eq
    _ = d := by simp

private def radialLogProfile (R p : ℝ) (r : ℝ) : ℝ :=
  (Ioo (0 : ℝ) R).indicator (fun s => (-Real.log (s / R)) ^ p) r

private theorem radialLogProfile_norm {R p : ℝ} (hR : 0 < R) (hp : 0 < p)
    (x : HilbertVec d) :
    radialLogProfile R p ‖x‖ =
      (ball (0 : HilbertVec d) R).indicator
        (fun y => (-Real.log (‖y‖ / R)) ^ p) x := by
  by_cases hx : x = 0
  · subst x
    simp [radialLogProfile, hR, Real.zero_rpow hp.ne']
  · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    by_cases hb : x ∈ ball (0 : HilbertVec d) R
    · have hr : ‖x‖ ∈ Ioo (0 : ℝ) R := by
        exact ⟨hn, by simpa only [mem_ball_zero_iff] using hb⟩
      rw [radialLogProfile, indicator_of_mem hr, indicator_of_mem hb]
    · have hr : ‖x‖ ∉ Ioo (0 : ℝ) R := by
        simpa only [mem_Ioo, mem_ball_zero_iff, hn, true_and] using hb
      rw [radialLogProfile, indicator_of_notMem hr, indicator_of_notMem hb]

private theorem integrable_radialLogProfile [NeZero d]
    {R p : ℝ} (hR : 0 < R) (hp : 0 < p) :
    Integrable (fun x : HilbertVec d => radialLogProfile R p ‖x‖) := by
  rw [integrable_fun_norm_addHaar (volume : Measure (HilbertVec d))]
  rw [finrank_hilbertVec]
  have hdNat : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hdNat
  have ht := integrableOn_radial_log_moment hdR hR (by linarith : -1 < p)
  rw [← integrable_indicator_iff measurableSet_Ioo] at ht
  rw [← integrable_indicator_iff measurableSet_Ioi]
  apply ht.congr
  filter_upwards with r
  by_cases hr : r ∈ Ioo (0 : ℝ) R
  · have hr0 : r ∈ Ioi (0 : ℝ) := hr.1
    simp only [indicator_of_mem hr, indicator_of_mem hr0, radialLogProfile, smul_eq_mul]
    rw [← Real.rpow_natCast, Nat.cast_sub hdNat]
    norm_num
  · by_cases hr0 : r ∈ Ioi (0 : ℝ)
    · simp [indicator_of_notMem hr, indicator_of_mem hr0, radialLogProfile]
    · simp [indicator_of_notMem hr, indicator_of_notMem hr0, radialLogProfile]

/-- The singular logarithmic radial power is genuinely integrable on an
internal Hilbert ball. -/
theorem integrableOn_radialLogMoment_hilbert [NeZero d]
    {R p : ℝ} (hR : 0 < R) (hp : 0 < p) :
    IntegrableOn
      (fun x : HilbertVec d => (-Real.log (‖x‖ / R)) ^ p)
      (ball 0 R) := by
  rw [← integrable_indicator_iff measurableSet_ball]
  exact (integrable_radialLogProfile hR hp).congr
    (Filter.Eventually.of_forall (fun x => radialLogProfile_norm hR hp x))

/-- Raw internal Hilbert-ball logarithmic moment, with the unit-ball volume
factor left explicit for later normalization. -/
theorem integral_radialLogMoment_hilbert [NeZero d]
    {R p : ℝ} (hR : 0 < R) (hp : 0 < p) :
    (∫ x in ball (0 : HilbertVec d) R, (-Real.log (‖x‖ / R)) ^ p) =
      (d : ℝ) * (volume (ball (0 : HilbertVec d) 1)).toReal *
        (R ^ (d : ℝ) * Real.Gamma (p + 1) / (d : ℝ) ^ (p + 1)) := by
  have hint := integral_fun_norm_addHaar
    (volume : Measure (HilbertVec d)) (radialLogProfile R p)
  rw [finrank_hilbertVec] at hint
  have hleft : (∫ x : HilbertVec d, radialLogProfile R p ‖x‖) =
      ∫ x in ball (0 : HilbertVec d) R, (-Real.log (‖x‖ / R)) ^ p := by
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => radialLogProfile_norm hR hp x)
  have hdNat : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hright : (∫ r in Ioi (0 : ℝ), r ^ (d - 1) • radialLogProfile R p r) =
      ∫ r in Ioo (0 : ℝ) R,
        r ^ ((d : ℝ) - 1) * (-Real.log (r / R)) ^ p := by
    rw [← integral_indicator measurableSet_Ioo,
      ← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards with r
    by_cases hr : r ∈ Ioo (0 : ℝ) R
    · have hr0 : r ∈ Ioi (0 : ℝ) := hr.1
      simp only [indicator_of_mem hr, indicator_of_mem hr0, radialLogProfile,
        smul_eq_mul]
      rw [← Real.rpow_natCast, Nat.cast_sub hdNat]
      norm_num
    · by_cases hr0 : r ∈ Ioi (0 : ℝ)
      · simp [indicator_of_notMem hr, indicator_of_mem hr0, radialLogProfile]
      · simp [indicator_of_notMem hr, indicator_of_notMem hr0, radialLogProfile]
  rw [hleft, hright] at hint
  rw [hint]
  rw [integral_radial_log_moment
    (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)) hR (by linarith : -1 < p)]
  simp only [Measure.real, nsmul_eq_mul, smul_eq_mul]
  ring

end

end PDE.Internal
