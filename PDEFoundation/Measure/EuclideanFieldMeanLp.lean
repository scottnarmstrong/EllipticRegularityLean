module

public import PDEFoundation.Measure.EuclideanFieldLpTriangle
public import PDEFoundation.Measure.EuclideanFieldMeasurability
public import PDEFoundation.Measure.NormalizedLp
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! # Normalized `Lᵖ` bounds for native vector fields -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

/-- The guarded real normalized `Lᵖ` norm of the sum of two native vector
fields satisfies the triangle inequality.  Membership of the sum is derived
from coordinate measurability and the two input memberships. -/
theorem exists_memLp_vecEuclideanNorm_add_and_lpMeanNorm_le
    {d : ℕ} {U : Set (Vec d)} {p : ENNReal} (hp : 1 ≤ p)
    (hUPos : 0 < volume U)
    (F G : Vec d → Vec d)
    (hFcoord : ∀ i, AEStronglyMeasurable (fun x => F x i) (volumeOn U))
    (hGcoord : ∀ i, AEStronglyMeasurable (fun x => G x i) (volumeOn U))
    (hF : MemLp (fun x => vecEuclideanNorm (F x)) p (volumeOn U))
    (hG : MemLp (fun x => vecEuclideanNorm (G x)) p (volumeOn U)) :
    ∃ hSum : MemLp (fun x => vecEuclideanNorm (F x + G x)) p
        (normalizedVolumeOn U),
      euclideanFieldLpMeanNormOn U p (fun x => F x + G x) hSum ≤
        euclideanFieldLpMeanNormOn U p F
          (memLp_normalizedVolumeOn_of_memLpOn hF hUPos) +
        euclideanFieldLpMeanNormOn U p G
          (memLp_normalizedVolumeOn_of_memLpOn hG hUPos) := by
  have hSumMeas : AEStronglyMeasurable
      (fun x => vecEuclideanNorm (F x + G x)) (volumeOn U) :=
    aestronglyMeasurable_vecEuclideanNorm_of_coord fun i =>
      (hFcoord i).add (hGcoord i)
  have hScalarSum : MemLp
      ((fun x => vecEuclideanNorm (F x)) + fun x => vecEuclideanNorm (G x))
      p (volumeOn U) := hF.add hG
  have hSumRaw : MemLp (fun x => vecEuclideanNorm (F x + G x)) p
      (volumeOn U) := by
    apply hScalarSum.of_le hSumMeas
    filter_upwards with x
    simp only [Pi.add_apply, Real.norm_eq_abs,
      abs_of_nonneg (vecEuclideanNorm_nonneg _),
      abs_of_nonneg (add_nonneg (vecEuclideanNorm_nonneg _) (vecEuclideanNorm_nonneg _))]
    exact vecEuclideanNorm_add_le (F x) (G x)
  let hFMean := memLp_normalizedVolumeOn_of_memLpOn hF hUPos
  let hGMean := memLp_normalizedVolumeOn_of_memLpOn hG hUPos
  let hSumMean := memLp_normalizedVolumeOn_of_memLpOn hSumRaw hUPos
  refine ⟨hSumMean, ?_⟩
  change (eLpNorm (fun x => vecEuclideanNorm (F x + G x)) p
      (normalizedVolumeOn U)).toReal ≤
    (eLpNorm (fun x => vecEuclideanNorm (F x)) p
      (normalizedVolumeOn U)).toReal +
    (eLpNorm (fun x => vecEuclideanNorm (G x)) p
      (normalizedVolumeOn U)).toReal
  rw [← ENNReal.toReal_add hFMean.eLpNorm_ne_top hGMean.eLpNorm_ne_top]
  apply ENNReal.toReal_mono
  · exact ENNReal.add_ne_top.2 ⟨hFMean.eLpNorm_ne_top, hGMean.eLpNorm_ne_top⟩
  exact eLpNorm_vecEuclideanNorm_add_le hp F G
    hFMean.aestronglyMeasurable hGMean.aestronglyMeasurable hSumMean.aestronglyMeasurable

/-- On a positive finite-volume set, the guarded normalized Euclidean-field
`Lᵠ` norm is at most its `Lᵖ` norm whenever `q ≤ p`.  The lower-exponent raw
membership is produced by the theorem. -/
theorem exists_memLp_vecEuclideanNorm_of_exponent_le_and_lpMeanNorm_le
    {d : ℕ} {U : Set (Vec d)} {q p : ENNReal} (hqp : q ≤ p)
    (hUPos : 0 < volume U) (hUTop : volume U < ∞)
    (F : Vec d → Vec d)
    (hF : MemLp (fun x => vecEuclideanNorm (F x)) p (volumeOn U)) :
    ∃ hQ : MemLp (fun x => vecEuclideanNorm (F x)) q (volumeOn U),
      euclideanFieldLpMeanNormOn U q F
          (memLp_normalizedVolumeOn_of_memLpOn hQ hUPos) ≤
        euclideanFieldLpMeanNormOn U p F
          (memLp_normalizedVolumeOn_of_memLpOn hF hUPos) := by
  let : IsFiniteMeasure (volumeOn U) :=
    ⟨by simpa only [volumeOn, Measure.restrict_apply_univ] using hUTop⟩
  have hQ : MemLp (fun x => vecEuclideanNorm (F x)) q (volumeOn U) :=
    hF.mono_exponent hqp
  let hQMean := memLp_normalizedVolumeOn_of_memLpOn hQ hUPos
  let hPMean := memLp_normalizedVolumeOn_of_memLpOn hF hUPos
  let : IsProbabilityMeasure (normalizedVolumeOn U) :=
    isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top hUPos hUTop
  refine ⟨hQ, ?_⟩
  change (eLpNorm (fun x => vecEuclideanNorm (F x)) q
      (normalizedVolumeOn U)).toReal ≤
    (eLpNorm (fun x => vecEuclideanNorm (F x)) p
      (normalizedVolumeOn U)).toReal
  apply ENNReal.toReal_mono hPMean.eLpNorm_ne_top
  exact eLpNorm_le_eLpNorm_of_exponent_le hqp

end PDE
