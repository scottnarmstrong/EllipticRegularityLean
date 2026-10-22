module

public import EllipticRegularity.Parabolic.WeakHarnack.MeasuresCylinders
public import EllipticRegularity.Parabolic.WeakHarnack.LogTail
public import EllipticRegularity.Parabolic.WeakHarnack.WeightedPoincareCutoff

/-!
# Log-tail transfer: from the weighted spatial measure to Lebesgue measure on the cylinders

Let `ζ = radialCutoff d` and `ν = ζ² dx / ∫_{B₁} ζ²` (`cutoffMeasure`).  Since `ζ = 1` on `B_{3/4}`,
`vol(A ∩ B_{3/4}) ≤ (∫ζ²) ν(A)` (`volume_inter_le_cutoffMass_mul`).  Tonelli on the product turns
the time-integrated `ν`-measures of `logTail_integrated` into Lebesgue measure bounds on the
cylinders `posCyl d 1 ⊆ B_{3/4} × (-7/8,t₀]` and `negCyl d 1 ⊆ B_{3/4} × (t₀,0]`
(`posNegCyl_log_tail`), and then into the `hlog` hypothesis of `PDE.Bombieri.bombieri_giusti`
(`hlog_pos`, `hlog_neg`).

**Level time.**  With the revised geometry (`negCyl d 1 = B_{3/4} × (-11/32,0]`) any
`t₀ ∈ (-3/8,-11/32)` separates the time ranges of `posCyl d 1` and `negCyl d 1`; see
`posNegCyl_log_tail_at` and the packaged `posNegCyl_log_tail`, which chooses `t₀ ∉ N`
itself.  `volume_slab_inter_le` is valid for any time set.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Parabolic.WeakHarnack

variable {d : ℕ}

/-! ### The weighted spatial probability measure -/

/-- `∫_{B₁} ζ²` as an extended real. -/
noncomputable def cutoffMass (d : ℕ) : ℝ≥0∞ :=
  ∫⁻ x in euclideanBall (0 : Vec d) 1, ENNReal.ofReal (radialCutoff d x ^ 2)

/-- `ν = ζ² dx / ∫_{B₁} ζ²`. -/
noncomputable def cutoffMeasure (d : ℕ) : Measure (Vec d) :=
  (cutoffMass d)⁻¹ • (volume.restrict (euclideanBall (0 : Vec d) 1)).withDensity
    (fun x => ENNReal.ofReal (radialCutoff d x ^ 2))

theorem measurable_radialCutoff (d : ℕ) : Measurable (radialCutoff d) :=
  (radialCutoff_contDiff d).continuous.measurable

private theorem ball_three_quarter_subset : euclideanBall (0 : Vec d) (3 / 4) ⊆
    euclideanBall (0 : Vec d) 1 := euclideanBall_mono (by norm_num) (by norm_num)

theorem cutoffMass_pos (d : ℕ) : cutoffMass d ≠ 0 := by
  have h : volume (euclideanBall (0 : Vec d) (3 / 4)) ≤ cutoffMass d := by
    calc volume (euclideanBall (0 : Vec d) (3 / 4))
        = ∫⁻ x in euclideanBall (0 : Vec d) (3 / 4), 1 := by simp
      _ = ∫⁻ x in euclideanBall (0 : Vec d) (3 / 4),
            ENNReal.ofReal (radialCutoff d x ^ 2) := by
          refine setLIntegral_congr_fun (measurableSet_euclideanBall _ _) ?_
          intro x hx
          beta_reduce; rw [radialCutoff_eq_one hx]; simp
      _ ≤ cutoffMass d := lintegral_mono_set ball_three_quarter_subset
  exact (lt_of_lt_of_le (volume_euclideanBall_pos _ (by norm_num)) h).ne'

theorem cutoffMass_ne_top (d : ℕ) : cutoffMass d ≠ ⊤ := by
  refine ne_top_of_le_ne_top (volume_euclideanBall_ne_top (0 : Vec d) (zero_le_one)) ?_
  calc cutoffMass d ≤ ∫⁻ x in euclideanBall (0 : Vec d) 1, 1 := by
        refine lintegral_mono fun x => ?_
        have h0 := radialCutoff_nonneg (d := d) x
        have h1 := radialCutoff_le_one (d := d) x
        calc ENNReal.ofReal (radialCutoff d x ^ 2) ≤ ENNReal.ofReal 1 :=
              ENNReal.ofReal_le_ofReal (by nlinarith)
          _ = 1 := by simp
    _ = _ := by simp

instance cutoffMeasure_isProbabilityMeasure (d : ℕ) : IsProbabilityMeasure (cutoffMeasure d) :=
  ⟨by
    rw [cutoffMeasure, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
    exact ENNReal.inv_mul_cancel (cutoffMass_pos d) (cutoffMass_ne_top d) |>.trans rfl⟩

/-- `vol(A ∩ B_{3/4}) ≤ (∫ζ²) · ν(A)`. -/
theorem volume_inter_le_cutoffMass_mul {A : Set (Vec d)} (hA : MeasurableSet A) :
    volume (A ∩ euclideanBall (0 : Vec d) (3 / 4)) ≤ cutoffMass d * cutoffMeasure d A := by
  have hζ : Measurable fun x => ENNReal.ofReal (radialCutoff d x ^ 2) :=
    ENNReal.measurable_ofReal.comp ((measurable_radialCutoff d).pow_const 2)
  rw [cutoffMeasure, Measure.smul_apply, withDensity_apply _ hA, smul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (cutoffMass_pos d) (cutoffMass_ne_top d), one_mul]
  have hB : MeasurableSet (euclideanBall (0 : Vec d) (3 / 4)) := measurableSet_euclideanBall _ _
  calc volume (A ∩ euclideanBall (0 : Vec d) (3 / 4))
      = (volume.restrict (euclideanBall (0 : Vec d) 1)) (A ∩ euclideanBall (0 : Vec d) (3 / 4)) := by
        rw [Measure.restrict_apply (hA.inter hB),
          inter_eq_left.2 ((inter_subset_right).trans ball_three_quarter_subset)]
    _ = ∫⁻ x in A ∩ euclideanBall (0 : Vec d) (3 / 4), 1 ∂(volume.restrict (euclideanBall (0 : Vec d) 1)) := by
        simp
    _ = ∫⁻ x in A ∩ euclideanBall (0 : Vec d) (3 / 4), ENNReal.ofReal (radialCutoff d x ^ 2)
          ∂(volume.restrict (euclideanBall (0 : Vec d) 1)) := by
        refine setLIntegral_congr_fun (hA.inter hB) ?_
        intro x hx
        beta_reduce; rw [radialCutoff_eq_one hx.2]; simp
    _ ≤ _ := lintegral_mono_set inter_subset_left

/-! ### Tonelli on the product -/

/-- Generic Tonelli transfer: for a measurable `E ⊆ Vec d × ℝ` and a measurable time set `I`,
`vol((B_{3/4} × I) ∩ E) ≤ M ∫⁻_I ν{x | (x,t) ∈ E} dt`. -/
theorem volume_slab_inter_le {M : ℝ≥0∞} (hM : M ≠ ⊤) (ν : Measure (Vec d))
    (hν : ∀ A : Set (Vec d), MeasurableSet A →
      volume (A ∩ euclideanBall (0 : Vec d) (3 / 4)) ≤ M * ν A)
    {E : Set (Vec d × ℝ)} (hE : MeasurableSet E) {I : Set ℝ} (hI : MeasurableSet I) :
    volume ((euclideanBall (0 : Vec d) (3 / 4) ×ˢ I) ∩ E) ≤
      M * ∫⁻ t in I, ν {x | (x, t) ∈ E} := by
  have hB : MeasurableSet (euclideanBall (0 : Vec d) (3 / 4)) := measurableSet_euclideanBall _ _
  have hS : MeasurableSet ((euclideanBall (0 : Vec d) (3 / 4) ×ˢ I) ∩ E) :=
    (hB.prod hI).inter hE
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hS, ← lintegral_const_mul' _ _ hM,
    ← lintegral_indicator hI]
  refine lintegral_mono fun t => ?_
  by_cases ht : t ∈ I
  · rw [indicator_of_mem ht]
    have hslice : (fun x => (x, t)) ⁻¹' ((euclideanBall (0 : Vec d) (3 / 4) ×ˢ I) ∩ E) =
        {x | (x, t) ∈ E} ∩ euclideanBall (0 : Vec d) (3 / 4) := by
      ext x; simp [ht, and_comm]
    rw [hslice]
    exact hν _ (measurable_prodMk_right hE)
  · rw [indicator_of_notMem ht]
    have : (fun x => (x, t)) ⁻¹' ((euclideanBall (0 : Vec d) (3 / 4) ×ˢ I) ∩ E) = ∅ := by
      ext x; simp [ht]
    simp [this]

end PDE.Parabolic.WeakHarnack
