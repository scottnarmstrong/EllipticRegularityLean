module

public import PDEFoundation.Analysis.DyadicRadius
public import PDEFoundation.Sobolev.H1.DyadicVectorMeans

/-!
# Reading dyadic vector estimates at arbitrary radii
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The exact root-volume loss between a Euclidean ball and its concentric
half-radius ball. -/
def dyadicBallReadoutCoefficient (d : ℕ) : ℝ :=
  (2 : ℝ) ^ ((d : ℝ) / 2)

theorem dyadicBallReadoutCoefficient_nonneg (d : ℕ) :
    0 ≤ dyadicBallReadoutCoefficient d := by
  unfold dyadicBallReadoutCoefficient
  positivity

private theorem sqrt_volume_ratio_le_dyadicBallReadoutCoefficient
    {z : Vec d} {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (hhalf : r / 2 < t) :
    Real.sqrt (volume (euclideanBall z r)).toReal /
        Real.sqrt (volume (euclideanBall z t)).toReal ≤
      dyadicBallReadoutCoefficient d := by
  have hsubHalf : euclideanBall z (r / 2) ⊆ euclideanBall z t :=
    euclideanBall_mono (by positivity) hhalf.le
  have hvol : (volume (euclideanBall z (r / 2))).toReal ≤
      (volume (euclideanBall z t)).toReal :=
    ENNReal.toReal_mono (volume_euclideanBall_ne_top z ht.le)
      (measure_mono hsubHalf)
  have hsqrt : Real.sqrt (volume (euclideanBall z (r / 2))).toReal ≤
      Real.sqrt (volume (euclideanBall z t)).toReal :=
    Real.sqrt_le_sqrt hvol
  have hhalfPos : 0 < Real.sqrt (volume (euclideanBall z (r / 2))).toReal :=
    Real.sqrt_pos.mpr (volume_euclideanBall_toReal_pos z (by positivity))
  have htPos : 0 < Real.sqrt (volume (euclideanBall z t)).toReal :=
    Real.sqrt_pos.mpr (volume_euclideanBall_toReal_pos z ht)
  calc
    Real.sqrt (volume (euclideanBall z r)).toReal /
        Real.sqrt (volume (euclideanBall z t)).toReal ≤
      Real.sqrt (volume (euclideanBall z r)).toReal /
        Real.sqrt (volume (euclideanBall z (r / 2))).toReal :=
      div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hhalfPos hsqrt
    _ = dyadicBallReadoutCoefficient d := by
      exact sqrt_volume_euclideanBall_div_half z hr

private theorem radius_weight_le_two_mul_dyadic_weight
    {R r t alpha : ℝ} (hR : 0 < R) (hr : 0 < r) (ht : 0 < t)
    (hrt : r / 2 < t) (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    (R / t) ^ alpha ≤ 2 * (R / r) ^ alpha := by
  have hratio : R / t < 2 * (R / r) := by
    calc
      R / t < R / (r / 2) :=
        div_lt_div_of_pos_left hR (by positivity) hrt
      _ = 2 * (R / r) := by field_simp
  have hpow := Real.rpow_le_rpow (div_nonneg hR.le ht.le)
    hratio.le halpha0.le
  have htwo : (2 : ℝ) ^ alpha ≤ 2 := by
    calc
      (2 : ℝ) ^ alpha ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) halpha1.le
      _ = 2 := by norm_num
  calc
    (R / t) ^ alpha ≤ (2 * (R / r)) ^ alpha := hpow
    _ = (2 : ℝ) ^ alpha * (R / r) ^ alpha := by
      rw [Real.mul_rpow (by norm_num) (div_nonneg hR.le hr.le)]
    _ ≤ 2 * (R / r) ^ alpha :=
      mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg (div_nonneg hR.le hr.le) alpha)

/-- Uniform dyadic root mean energy and weighted centered oscillation bounds
extend to every intermediate positive radius with the exact half-ball volume
loss. -/
theorem dyadic_vector_bounds_readout
    {z : Vec d} {R alpha A B : ℝ}
    (hR : 0 < R) (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (_hA : 0 ≤ A) (_hB : 0 ≤ B) {g : Vec d → Vec d}
    (hg : MemVectorL2On (euclideanBall z R) g)
    (hosc : ∀ n : ℕ,
      (R / dyadicRadius R n) ^ alpha *
          centeredVectorMeanL2 (euclideanBall z (dyadicRadius R n)) g ≤ A)
    (henergy : ∀ n : ℕ,
      Real.sqrt (integralAverage (euclideanBall z (dyadicRadius R n))
        (fun x => vecNormSq (g x))) ≤ B) :
    ∀ r : ℝ, 0 < r → r ≤ R →
      Real.sqrt (integralAverage (euclideanBall z r)
          (fun x => vecNormSq (g x))) ≤
          dyadicBallReadoutCoefficient d * B ∧
      (R / r) ^ alpha * centeredVectorMeanL2 (euclideanBall z r) g ≤
          2 * dyadicBallReadoutCoefficient d * A := by
  intro r hr hrR
  obtain ⟨n, hhalf, houter⟩ := exists_dyadicRadius_bracket hR hr hrR
  let rn := dyadicRadius R n
  have hrn : 0 < rn := dyadicRadius_pos hR n
  have hrnR : rn ≤ R := dyadicRadius_le hR.le n
  have hsubOuter : euclideanBall z rn ⊆ euclideanBall z R :=
    euclideanBall_mono hrn.le hrnR
  have hsub : euclideanBall z r ⊆ euclideanBall z rn :=
    euclideanBall_mono hr.le houter
  have hgOuter : MemVectorL2On (euclideanBall z rn) g := fun i =>
    (hg i).mono_measure (Measure.restrict_mono hsubOuter le_rfl)
  have hratio : Real.sqrt (volume (euclideanBall z rn)).toReal /
      Real.sqrt (volume (euclideanBall z r)).toReal ≤
        dyadicBallReadoutCoefficient d := by
    apply sqrt_volume_ratio_le_dyadicBallReadoutCoefficient hrn hr
    simpa only [rn, dyadicRadius_succ] using hhalf
  have hfull := sqrt_integralAverage_vecNormSq_mono_set hsub
    (volume_euclideanBall_toReal_pos z hrn) hgOuter
  have hcenter := centeredVectorMeanL2_mono_set hsub hgOuter
    (volume_euclideanBall_pos z hr)
    (lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top z hr.le))
    (volume_euclideanBall_pos z hrn)
    (lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top z hrn.le))
  rw [Real.sqrt_div ENNReal.toReal_nonneg] at hcenter
  have hfullBound := hfull.trans
    (mul_le_mul hratio (henergy n) (Real.sqrt_nonneg _) (dyadicBallReadoutCoefficient_nonneg d))
  have hcenterBound : centeredVectorMeanL2 (euclideanBall z r) g ≤
      dyadicBallReadoutCoefficient d *
        centeredVectorMeanL2 (euclideanBall z rn) g :=
    hcenter.trans (mul_le_mul_of_nonneg_right hratio (Real.sqrt_nonneg _))
  have hhalf' : rn / 2 < r := by
    simpa only [rn, dyadicRadius_succ] using hhalf
  have hweight := radius_weight_le_two_mul_dyadic_weight
    hR hrn hr hhalf' halpha0 halpha1
  refine ⟨?_, ?_⟩
  · simpa only [rn] using hfullBound
  · calc
      (R / r) ^ alpha * centeredVectorMeanL2 (euclideanBall z r) g ≤
          (R / r) ^ alpha *
            (dyadicBallReadoutCoefficient d *
              centeredVectorMeanL2 (euclideanBall z rn) g) :=
        mul_le_mul_of_nonneg_left hcenterBound
          (Real.rpow_nonneg (div_nonneg hR.le hr.le) alpha)
      _ ≤ (2 * (R / rn) ^ alpha) *
            (dyadicBallReadoutCoefficient d *
              centeredVectorMeanL2 (euclideanBall z rn) g) :=
        mul_le_mul_of_nonneg_right hweight
          (mul_nonneg (dyadicBallReadoutCoefficient_nonneg d) (Real.sqrt_nonneg _))
      _ = 2 * dyadicBallReadoutCoefficient d *
            ((R / rn) ^ alpha *
              centeredVectorMeanL2 (euclideanBall z rn) g) := by ring
      _ ≤ 2 * dyadicBallReadoutCoefficient d * A :=
        mul_le_mul_of_nonneg_left (by simpa only [rn] using hosc n)
          (mul_nonneg (by norm_num) (dyadicBallReadoutCoefficient_nonneg d))

end

end PDE
