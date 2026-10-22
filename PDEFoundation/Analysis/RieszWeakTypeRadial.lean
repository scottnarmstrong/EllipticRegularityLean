module

public import PDEFoundation.Analysis.HilbertRadialIntegrability
public import PDEFoundation.Measure.BallVolume

/-! # Radial integral of the Riesz kernel

The Riesz kernel `|z| ^ (1 - d)` has integral `d * |B₁| * R` over the round ball
of radius `R` centered at the origin of `Vec d`. The computation is done through the
internal Hilbert realization and transferred to the native carrier by the
volume-preserving coordinate identification.
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory Metric Set

namespace PDE

noncomputable section

variable {d : ℕ}

namespace Internal

private theorem finrank_hilbertVec' : Module.finrank ℝ (HilbertVec d) = d := by
  calc
    Module.finrank ℝ (HilbertVec d) = Module.finrank ℝ (Fin d → ℝ) :=
      (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).finrank_eq
    _ = d := by simp

/-- The raw radial integral of the Riesz kernel on an internal Hilbert ball. -/
theorem integral_norm_rpow_one_sub_hilbert [NeZero d] {R : ℝ} (hR : 0 < R) :
    (∫ x in ball (0 : HilbertVec d) R, ‖x‖ ^ ((1 : ℝ) - d)) =
      (d : ℝ) * (volume (ball (0 : HilbertVec d) 1)).toReal * R := by
  let f : ℝ → ℝ := fun r => (Ioo (0 : ℝ) R).indicator (fun r => r ^ ((1 : ℝ) - d)) r
  have hint := integral_fun_norm_addHaar (volume : Measure (HilbertVec d)) f
  rw [finrank_hilbertVec'] at hint
  have hleft : (∫ x : HilbertVec d, f ‖x‖) =
      ∫ x in ball (0 : HilbertVec d) R, ‖x‖ ^ ((1 : ℝ) - d) := by
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards [(countable_singleton (0 : HilbertVec d)).ae_notMem volume] with x hx
    have hx0 : x ≠ 0 := by simpa only [mem_singleton_iff] using hx
    by_cases hxb : x ∈ ball (0 : HilbertVec d) R
    · have hnorm : ‖x‖ ∈ Ioo (0 : ℝ) R := by
        simpa only [mem_Ioo, norm_pos_iff, mem_ball_zero_iff] using And.intro hx0 hxb
      simp only [f, Set.indicator_of_mem hnorm, Set.indicator_of_mem hxb]
    · have hnorm : ‖x‖ ∉ Ioo (0 : ℝ) R := by
        intro hn
        apply hxb
        simpa only [mem_ball_zero_iff] using hn.2
      simp only [f, Set.indicator_of_notMem hnorm, Set.indicator_of_notMem hxb]
  have hdNat : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hright : (∫ r in Ioi (0 : ℝ), r ^ (d - 1) • f r) = R := by
    have : (∫ r in Ioi (0 : ℝ), r ^ (d - 1) • f r) = ∫ r in Ioo (0 : ℝ) R, (1 : ℝ) := by
      rw [← integral_indicator measurableSet_Ioo,
        ← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards with r
      by_cases hr : r ∈ Ioo (0 : ℝ) R
      · have hr0 : r ∈ Ioi (0 : ℝ) := hr.1
        simp only [f, indicator_of_mem hr, indicator_of_mem hr0, smul_eq_mul]
        rw [← Real.rpow_natCast, ← Real.rpow_add hr.1, Nat.cast_sub hdNat]
        simp
      · by_cases hr0 : r ∈ Ioi (0 : ℝ)
        · simp [f, indicator_of_notMem hr, indicator_of_mem hr0]
        · simp [f, indicator_of_notMem hr, indicator_of_notMem hr0]
    rw [this]
    simp [hR.le]
  rw [hleft, hright] at hint
  rw [hint]
  simp only [Measure.real, nsmul_eq_mul, smul_eq_mul]
  ring

end Internal

/-- Every Euclidean ball is a preimage of the internal Hilbert ball under coordinates. -/
theorem preimage_ofLp_ball_eq_euclideanBall {R : ℝ} (hR : 0 < R) :
    (WithLp.ofLp : HilbertVec d → Vec d) ⁻¹' euclideanBall (0 : Vec d) R =
      ball (0 : HilbertVec d) R := by
  ext x
  rw [mem_preimage, mem_euclideanBall_iff_vecEuclideanNorm_lt hR, mem_ball_zero_iff,
    HilbertVec.norm_eq_vecEuclideanNorm]
  simp [HilbertVec.toVec]

theorem measurableEmbedding_ofLp_hilbert :
    MeasurableEmbedding (WithLp.ofLp : HilbertVec d → Vec d) :=
  (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding

/-- The unit-ball volume of the internal Hilbert realization agrees with the native one. -/
theorem volume_ball_hilbert_eq_euclideanBall :
    volume (ball (0 : HilbertVec d) 1) = volume (euclideanBall (0 : Vec d) 1) := by
  rw [← preimage_ofLp_ball_eq_euclideanBall (d := d) one_pos]
  exact (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
    (isOpen_euclideanBall _ _).measurableSet.nullMeasurableSet

/-- **Radial integral of the Riesz kernel.**  For `R > 0`,
`∫_{B_R} |z|^{1-d} dz = d |B₁| R`. -/
theorem lintegral_euclideanBall_rieszKernel [NeZero d] {R : ℝ} (hR : 0 < R) :
    ∫⁻ z in euclideanBall (0 : Vec d) R, ENNReal.ofReal (vecEuclideanNorm z ^ ((1 : ℝ) - d)) =
      ENNReal.ofReal ((d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal * R) := by
  have hpres := PiLp.volume_preserving_ofLp (Fin d)
  have h1 := hpres.setLIntegral_comp_preimage_emb (measurableEmbedding_ofLp_hilbert (d := d))
    (fun z : Vec d => ENNReal.ofReal (vecEuclideanNorm z ^ ((1 : ℝ) - d)))
    (euclideanBall (0 : Vec d) R)
  rw [← h1, preimage_ofLp_ball_eq_euclideanBall hR]
  have hnorm : ∀ x : HilbertVec d, vecEuclideanNorm (WithLp.ofLp x) = ‖x‖ := fun x => by
    rw [HilbertVec.norm_eq_vecEuclideanNorm]; rfl
  simp only [hnorm]
  have hI : IntegrableOn (fun x : HilbertVec d => ‖x‖ ^ ((1 : ℝ) - d)) (ball 0 R) := by
    rw [Internal.integrableOn_norm_rpow_euclideanBall_iff hR]
    have : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
    linarith
  rw [← ofReal_integral_eq_lintegral_ofReal hI
    (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg x) _),
    Internal.integral_norm_rpow_one_sub_hilbert hR, volume_ball_hilbert_eq_euclideanBall]

end

end PDE
