module

public import PDEFoundation.Analysis.RieszWeakTypeRadial
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Radial integral of the Hörmander tail

The tail `|z| ^ (-(d + 1))` is integrable outside a round ball of radius `R` on `Vec d`,
with integral `d |B₁| / R`. The computation goes through the internal Hilbert realization
and the polar-coordinate formula, then transfers to the native carrier.
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory Metric Set

namespace PDE.NewtonWeakType

noncomputable section

variable {d : ℕ}

private theorem finrank_hilbertVec_eq : Module.finrank ℝ (HilbertVec d) = d := by
  calc
    Module.finrank ℝ (HilbertVec d) = Module.finrank ℝ (Fin d → ℝ) :=
      (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).finrank_eq
    _ = d := by simp

/-- The radial profile of the tail, supported outside radius `R`. -/
private def tailProfile (d : ℕ) (R : ℝ) (r : ℝ) : ℝ :=
  (Ici R).indicator (fun r => r ^ (-((d : ℝ) + 1))) r

private theorem tailProfile_mul (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) {R : ℝ} :
    r ^ (d - 1) • tailProfile d R r = (Ici R).indicator (fun r => r ^ (-2 : ℝ)) r := by
  by_cases hrR : r ∈ Ici R
  · simp only [tailProfile, Set.indicator_of_mem hrR, smul_eq_mul]
    rw [← Real.rpow_natCast, ← Real.rpow_add hr, Nat.cast_sub hd]
    congr 1
    push_cast
    ring
  · simp [tailProfile, Set.indicator_of_notMem hrR]

private theorem integrableOn_tail_one_dim (hd : 1 ≤ d) {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun r : ℝ => r ^ (d - 1) • tailProfile d R r) (Ioi 0) := by
  have h1 : IntegrableOn (fun r : ℝ => r ^ (-2 : ℝ)) (Ici R) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_Ioi_rpow_of_lt (by norm_num) hR
  have h2 : IntegrableOn ((Ici R).indicator (fun r : ℝ => r ^ (-2 : ℝ))) (Ioi 0) :=
    (h1.integrable_indicator measurableSet_Ici).integrableOn
  refine h2.congr_fun (fun r hr => ?_) measurableSet_Ioi
  exact (tailProfile_mul hd hr).symm

private theorem integral_tail_one_dim (hd : 1 ≤ d) {R : ℝ} (hR : 0 < R) :
    ∫ r in Ioi (0 : ℝ), r ^ (d - 1) • tailProfile d R r = R⁻¹ := by
  have h1 : ∫ r in Ioi (0 : ℝ), r ^ (d - 1) • tailProfile d R r =
      ∫ r in Ioi (0 : ℝ), (Ici R).indicator (fun r : ℝ => r ^ (-2 : ℝ)) r :=
    setIntegral_congr_fun measurableSet_Ioi (fun r hr => tailProfile_mul hd hr)
  rw [h1, setIntegral_indicator measurableSet_Ici]
  have h2 : Ioi (0 : ℝ) ∩ Ici R = Ici R := by
    ext r
    simp only [mem_inter_iff, mem_Ioi, mem_Ici, and_iff_right_iff_imp]
    intro h
    exact hR.trans_le h
  rw [h2, integral_Ici_eq_integral_Ioi, integral_Ioi_rpow_of_lt (by norm_num) hR]
  rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
  field_simp

/-- Pointwise identification of the radial profile with the tail on the Hilbert exterior. -/
private theorem tailProfile_norm (R : ℝ) (x : HilbertVec d) :
    tailProfile d R ‖x‖ =
      (ball (0 : HilbertVec d) R)ᶜ.indicator (fun x => ‖x‖ ^ (-((d : ℝ) + 1))) x := by
  by_cases hx : x ∈ (ball (0 : HilbertVec d) R)ᶜ
  · have hn : ‖x‖ ∈ Ici R := by
      simpa only [mem_compl_iff, mem_ball_zero_iff, not_lt, mem_Ici] using hx
    simp only [tailProfile, Set.indicator_of_mem hn, Set.indicator_of_mem hx]
  · have hn : ‖x‖ ∉ Ici R := by
      simpa only [mem_compl_iff, mem_ball_zero_iff, not_not, mem_Ici, not_le] using hx
    simp only [tailProfile, Set.indicator_of_notMem hn, Set.indicator_of_notMem hx]

/-- Raw Hilbert exterior integral. -/
private theorem integral_norm_rpow_tail_hilbert [NeZero d] {R : ℝ} (hR : 0 < R) :
    (∫ x in (ball (0 : HilbertVec d) R)ᶜ, ‖x‖ ^ (-((d : ℝ) + 1))) =
      (d : ℝ) * (volume (ball (0 : HilbertVec d) 1)).toReal * R⁻¹ := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hint := integral_fun_norm_addHaar (volume : Measure (HilbertVec d)) (tailProfile d R)
  rw [finrank_hilbertVec_eq, integral_tail_one_dim hd hR] at hint
  have hleft : (∫ x : HilbertVec d, tailProfile d R ‖x‖) =
      ∫ x in (ball (0 : HilbertVec d) R)ᶜ, ‖x‖ ^ (-((d : ℝ) + 1)) := by
    rw [← integral_indicator (isOpen_ball.measurableSet.compl)]
    exact integral_congr_ae (Filter.Eventually.of_forall (tailProfile_norm R))
  rw [hleft] at hint
  rw [hint]
  simp only [Measure.real, nsmul_eq_mul, smul_eq_mul]
  ring

private theorem integrable_norm_rpow_tail_hilbert [NeZero d] {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun x : HilbertVec d => ‖x‖ ^ (-((d : ℝ) + 1)))
      (ball (0 : HilbertVec d) R)ᶜ := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hpolar := (integrable_fun_norm_addHaar (μ := (volume : Measure (HilbertVec d)))
    (f := tailProfile d R)).mpr (by rw [finrank_hilbertVec_eq]; exact integrableOn_tail_one_dim hd hR)
  rw [← integrable_indicator_iff (isOpen_ball.measurableSet.compl)]
  exact hpolar.congr (Filter.Eventually.of_forall (tailProfile_norm R))

/-- **Radial integral of the Hörmander tail.** For `R > 0`,
`∫_{|z| ≥ R} |z|^{-(d+1)} dz = d |B₁| / R`. -/
theorem lintegral_compl_euclideanBall_tail [NeZero d] {R : ℝ} (hR : 0 < R) :
    ∫⁻ z in (euclideanBall (0 : Vec d) R)ᶜ,
        ENNReal.ofReal (vecEuclideanNorm z ^ (-((d : ℝ) + 1))) =
      ENNReal.ofReal ((d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal * R⁻¹) := by
  have hpres := PiLp.volume_preserving_ofLp (Fin d)
  have h1 := hpres.setLIntegral_comp_preimage_emb (measurableEmbedding_ofLp_hilbert (d := d))
    (fun z : Vec d => ENNReal.ofReal (vecEuclideanNorm z ^ (-((d : ℝ) + 1))))
    (euclideanBall (0 : Vec d) R)ᶜ
  rw [← h1, Set.preimage_compl, preimage_ofLp_ball_eq_euclideanBall hR]
  have hnorm : ∀ x : HilbertVec d, vecEuclideanNorm (WithLp.ofLp x) = ‖x‖ := fun x => by
    rw [HilbertVec.norm_eq_vecEuclideanNorm]; rfl
  simp only [hnorm]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_norm_rpow_tail_hilbert hR)
    (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg x) _),
    integral_norm_rpow_tail_hilbert hR, volume_ball_hilbert_eq_euclideanBall]

end

end PDE.NewtonWeakType
