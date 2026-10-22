module

public import PDEFoundation.Analysis.DyadicRadius
public import PDEFoundation.Sobolev.H1.MeanEnergyDecomposition

/-!
# Dyadic vector means on Euclidean balls

This module records the elementary mean and oscillation recurrences on the
dyadic concentric balls used by later finite scale iterations.
-/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The Euclidean magnitude of the vector mean on the next dyadic ball is at
most the current mean magnitude plus the exact half-ball volume loss times
the current centered mean `L²` oscillation. -/
theorem vecEuclideanNorm_vectorIntegralAverage_dyadic_succ_le
    {z : Vec d} {R : ℝ} (hR : 0 < R) {g : Vec d → Vec d}
    (hg : MemVectorL2On (euclideanBall z R) g) (n : ℕ) :
    vecEuclideanNorm
        (vectorIntegralAverage (euclideanBall z (dyadicRadius R (n + 1))) g) ≤
      vecEuclideanNorm
          (vectorIntegralAverage (euclideanBall z (dyadicRadius R n)) g) +
        (2 : ℝ) ^ ((d : ℝ) / 2) *
          centeredVectorMeanL2 (euclideanBall z (dyadicRadius R n)) g := by
  let r := dyadicRadius R n
  have hr : 0 < r := dyadicRadius_pos hR n
  have hrR : r ≤ R := dyadicRadius_le hR.le n
  have houter : euclideanBall z r ⊆ euclideanBall z R :=
    euclideanBall_mono hr.le hrR
  have hgOuter : MemVectorL2On (euclideanBall z r) g := fun i =>
    (hg i).mono_measure (Measure.restrict_mono houter le_rfl)
  have hhalf : euclideanBall z (r / 2) ⊆ euclideanBall z r :=
    euclideanBall_mono (by positivity) (by linarith)
  have hdiff := vecEuclideanNorm_vectorIntegralAverage_sub_le hhalf hgOuter
    (volume_euclideanBall_pos z (by positivity))
    (lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top z (by positivity)))
    (volume_euclideanBall_pos z hr)
    (lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top z hr.le))
  rw [Real.sqrt_div ENNReal.toReal_nonneg,
    sqrt_volume_euclideanBall_div_half z hr] at hdiff
  have hdecomp :
      vectorIntegralAverage (euclideanBall z (r / 2)) g =
        (vectorIntegralAverage (euclideanBall z (r / 2)) g -
          vectorIntegralAverage (euclideanBall z r) g) +
          vectorIntegralAverage (euclideanBall z r) g := by
    abel
  rw [dyadicRadius_succ]
  change vecEuclideanNorm (vectorIntegralAverage (euclideanBall z (r / 2)) g) ≤ _
  rw [hdecomp]
  apply (vecEuclideanNorm_add_le _ _).trans
  have hadd := add_le_add_right hdiff
    (vecEuclideanNorm (vectorIntegralAverage (euclideanBall z r) g))
  simpa only [r, add_comm] using hadd

/-- On every dyadic ball, full root mean-square energy is at most vector mean
magnitude plus centered vector mean `L²` oscillation. -/
theorem sqrt_integralAverage_vecNormSq_dyadic_le_mean_add_centered
    {z : Vec d} {R : ℝ} (hR : 0 < R) {g : Vec d → Vec d}
    (hg : MemVectorL2On (euclideanBall z R) g) (n : ℕ) :
    Real.sqrt (integralAverage (euclideanBall z (dyadicRadius R n))
        (fun x => vecNormSq (g x))) ≤
      vecEuclideanNorm
          (vectorIntegralAverage (euclideanBall z (dyadicRadius R n)) g) +
        centeredVectorMeanL2 (euclideanBall z (dyadicRadius R n)) g := by
  have hr : 0 < dyadicRadius R n := dyadicRadius_pos hR n
  have hrR : dyadicRadius R n ≤ R := dyadicRadius_le hR.le n
  have hsub : euclideanBall z (dyadicRadius R n) ⊆ euclideanBall z R :=
    euclideanBall_mono hr.le hrR
  have hg' : MemVectorL2On (euclideanBall z (dyadicRadius R n)) g := fun i =>
    (hg i).mono_measure (Measure.restrict_mono hsub le_rfl)
  exact sqrt_integralAverage_vecNormSq_le_mean_add_centered hg'
    (volume_euclideanBall_pos z hr)
    (lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top z hr.le))

/-- At the initial radius, centered oscillation is bounded by full root
mean-square energy. -/
theorem centeredVectorMeanL2_le_sqrt_integralAverage_vecNormSq_ball
    {z : Vec d} {R : ℝ} (hR : 0 < R) {g : Vec d → Vec d}
    (hg : MemVectorL2On (euclideanBall z R) g) :
    centeredVectorMeanL2 (euclideanBall z R) g ≤
      Real.sqrt (integralAverage (euclideanBall z R)
        (fun x => vecNormSq (g x))) :=
  centeredVectorMeanL2_le_sqrt_integralAverage_vecNormSq hg
    (volume_euclideanBall_pos z hR)
    (lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top z hR.le))

/-- At the initial radius, vector mean magnitude is bounded by full root
mean-square energy. -/
theorem vecEuclideanNorm_vectorIntegralAverage_le_sqrt_integralAverage_vecNormSq_ball
    {z : Vec d} {R : ℝ} (hR : 0 < R) {g : Vec d → Vec d}
    (hg : MemVectorL2On (euclideanBall z R) g) :
    vecEuclideanNorm (vectorIntegralAverage (euclideanBall z R) g) ≤
      Real.sqrt (integralAverage (euclideanBall z R)
        (fun x => vecNormSq (g x))) :=
  vecEuclideanNorm_vectorIntegralAverage_le_sqrt_integralAverage_vecNormSq
    hg (volume_euclideanBall_pos z hR)
    (lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top z hR.le))

end

end PDE
