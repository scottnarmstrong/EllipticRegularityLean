module

public import PDEFoundation.Measure.BallVolume
public import PDEFoundation.Measure.LpPower
public import PDEFoundation.Measure.NormalizedLp
public import PDEFoundation.Sobolev.H1.Pairing
public import PDEFoundation.Sobolev.Mean
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Local forcing bounds from finite-exponent data

On a positive finite-measure set, normalized `L²` is controlled by normalized
`Lᵖ` for `p ≥ 2`.  The round-ball estimate below converts the normalized
`Lᵖ` norm back to the exact raw norm with its explicit volume factor.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

variable {d : ℕ}

/-- Guarded normalized vector-field `Lᵖ` norm in terms of the guarded raw norm,
with the exact real volume scaling. -/
private theorem euclideanFieldLpMeanNormOn_eq_volume_toReal_neg_rpow_mul
    {U : Set (Vec d)} {F : Vec d → Vec d} {q : ℝ≥0∞}
    {hRaw : MemLp (fun x => vecEuclideanNorm (F x)) q (volumeOn U)}
    {hMean : MemLp (fun x => vecEuclideanNorm (F x)) q
      (normalizedVolumeOn U)}
    (hUTop : volume U < ∞) :
    euclideanFieldLpMeanNormOn U q F hMean =
      (volume U).toReal ^ (-(1 / q).toReal) *
        euclideanFieldLpNormOn U q F hRaw := by
  rw [euclideanFieldLpMeanNormOn, lpMeanNormOn_eq_toReal,
    euclideanFieldLpNormOn, lpNormOn_eq_toReal]
  rw [eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn hUTop q
    (fun x => vecEuclideanNorm (F x))]
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_inv, ← Real.rpow_neg_eq_inv_rpow]

/-- The square root of the mean Euclidean energy equals the guarded normalized
Euclidean vector-field `L²` norm. -/
theorem sqrt_integralAverage_vecNormSq_eq_euclideanFieldLpMeanNormOn_two
    {U : Set (Vec d)} {F : Vec d → Vec d}
    (hF : MemLp (fun x => vecEuclideanNorm (F x))
      (2 : ℝ≥0∞) (normalizedVolumeOn U)) :
    Real.sqrt (integralAverage U (fun x => vecNormSq (F x))) =
      euclideanFieldLpMeanNormOn U (2 : ℝ≥0∞) F hF := by
  have hPower :
      euclideanFieldLpMeanNormOn U (2 : ℝ≥0∞) F hF ^ 2 =
        integralAverage U (fun x => vecNormSq (F x)) := by
    rw [euclideanFieldLpMeanNormOn, lpMeanNormOn_eq_toReal]
    rw [← integral_normalizedVolumeOn_eq_integralAverage U
      (fun x => vecNormSq (F x))]
    simpa only [eLpMeanNormOn, euclideanFieldELpMeanNormOn,
      vecEuclideanNorm_sq] using
      toReal_eLpNorm_two_sq_eq_integral_sq hF
  have hAvgNonneg :
      0 ≤ integralAverage U (fun x => vecNormSq (F x)) := by
    rw [← hPower]
    positivity
  have hNormNonneg :
      0 ≤ euclideanFieldLpMeanNormOn U (2 : ℝ≥0∞) F hF := by
    rw [euclideanFieldLpMeanNormOn, lpMeanNormOn_eq_toReal]
    exact ENNReal.toReal_nonneg
  exact (Real.sqrt_eq_iff_eq_sq hAvgNonneg hNormNonneg).2 hPower.symm

/-- The normalized `L²` energy on a round ball is controlled by the raw
`Lᵖ` norm on any containing domain, with the exact ball-volume factor. -/
theorem sqrt_integralAverage_vecNormSq_euclideanBall_le_euclideanFieldLpNormOn
    {F : Vec d → Vec d} {p : ℝ} (hp : 2 ≤ p)
    (z : Vec d) {R : ℝ} (hR : 0 < R)
    {V : Set (Vec d)} (hBV : euclideanBall z R ⊆ V)
    (hF : MemLp (fun x => vecEuclideanNorm (F x))
      (ENNReal.ofReal p) (volumeOn V)) :
    Real.sqrt (integralAverage (euclideanBall z R)
        (fun x => vecNormSq (F x))) ≤
      (volume (euclideanBall z R)).toReal ^ (-1 / p) *
        euclideanFieldLpNormOn V (ENNReal.ofReal p) F hF := by
  let B := euclideanBall z R
  let f : Vec d → ℝ := fun x => vecEuclideanNorm (F x)
  have hBPos : 0 < volume B := by
    dsimp [B]
    exact volume_euclideanBall_pos z hR
  have hBTop : volume B < ∞ := by
    dsimp [B]
    exact lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top z hR.le)
  have hBmem : MemLp f (ENNReal.ofReal p) (volumeOn B) := by
    dsimp only [f, B]
    exact hF.mono_measure (Measure.restrict_mono hBV le_rfl)
  have hBmean : MemLp f (ENNReal.ofReal p) (normalizedVolumeOn B) :=
    memLp_normalizedVolumeOn_of_memLpOn hBmem hBPos
  let : IsProbabilityMeasure (normalizedVolumeOn B) :=
    isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top hBPos hBTop
  have hExp : ENNReal.ofReal (2 : ℝ) ≤ ENNReal.ofReal p :=
    ENNReal.ofReal_le_ofReal hp
  have hCompare :
      eLpNorm f (ENNReal.ofReal (2 : ℝ)) (normalizedVolumeOn B) ≤
        eLpNorm f (ENNReal.ofReal p) (normalizedVolumeOn B) :=
    eLpNorm_le_eLpNorm_of_exponent_le hExp
  let : IsFiniteMeasure (volumeOn B) :=
    isFiniteMeasure_volumeOn_euclideanBall z hR.le
  have hBtwo : MemLp f (ENNReal.ofReal (2 : ℝ)) (volumeOn B) :=
    hBmem.mono_exponent hExp
  have hBtwoMean : MemLp f (2 : ℝ≥0∞) (normalizedVolumeOn B) := by
    simpa only [ENNReal.ofReal_ofNat] using
      memLp_normalizedVolumeOn_of_memLpOn hBtwo hBPos
  have hCompareReal :
      euclideanFieldLpMeanNormOn B (2 : ℝ≥0∞) F hBtwoMean ≤
        euclideanFieldLpMeanNormOn B (ENNReal.ofReal p) F hBmean := by
    change (eLpNorm f (2 : ℝ≥0∞)
        (normalizedVolumeOn B)).toReal ≤
      (eLpNorm f (ENNReal.ofReal p) (normalizedVolumeOn B)).toReal
    simpa only [ENNReal.ofReal_ofNat] using ENNReal.toReal_mono
      (ne_of_lt (by simpa only [f, eLpMeanNormOn] using hBmean.eLpNorm_lt_top))
      hCompare
  have hRawMono :
      euclideanFieldLpNormOn B (ENNReal.ofReal p) F hBmem ≤
        euclideanFieldLpNormOn V (ENNReal.ofReal p) F hF := by
    change (eLpNorm f (ENNReal.ofReal p) (volumeOn B)).toReal ≤
      (eLpNorm f (ENNReal.ofReal p) (volumeOn V)).toReal
    apply ENNReal.toReal_mono (ne_of_lt hF.eLpNorm_lt_top)
    exact eLpNorm_mono_measure f
      (Measure.restrict_mono hBV le_rfl)
  have hMeanRaw := euclideanFieldLpMeanNormOn_eq_volume_toReal_neg_rpow_mul
    (U := B) (F := F) (q := ENNReal.ofReal p)
    (hRaw := by simpa only [f] using hBmem)
    (hMean := by simpa only [f] using hBmean) hBTop
  have hq : (1 / ENNReal.ofReal p).toReal = 1 / p := by
    rw [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofReal (by linarith)]
    ring
  calc
    Real.sqrt (integralAverage B (fun x => vecNormSq (F x))) =
        euclideanFieldLpMeanNormOn B (2 : ℝ≥0∞) F hBtwoMean := by
      exact sqrt_integralAverage_vecNormSq_eq_euclideanFieldLpMeanNormOn_two
        hBtwoMean
    _ ≤ euclideanFieldLpMeanNormOn B (ENNReal.ofReal p) F hBmean :=
      hCompareReal
    _ = (volume B).toReal ^ (-1 / p) *
          euclideanFieldLpNormOn B (ENNReal.ofReal p) F hBmem := by
      rw [hMeanRaw, hq]
      congr 1
      congr 1
      ring
    _ ≤ (volume B).toReal ^ (-1 / p) *
          euclideanFieldLpNormOn V (ENNReal.ofReal p) F hF :=
      mul_le_mul_of_nonneg_left hRawMono
        (Real.rpow_nonneg ENNReal.toReal_nonneg _)

/-- A Euclidean magnitude `Lᵖ` bound on a containing domain gives the
coordinatewise native-vector `L²` membership needed on the round ball,
provided the vector representatives are measurable coordinatewise. -/
theorem memVectorL2On_euclideanBall_of_memLp_vecEuclideanNorm
    {F : Vec d → Vec d} {p : ℝ} (hp : 2 ≤ p)
    (z : Vec d) {R : ℝ} (hR : 0 < R)
    {V : Set (Vec d)} (hBV : euclideanBall z R ⊆ V)
    (hF : MemLp (fun x => vecEuclideanNorm (F x))
      (ENNReal.ofReal p) (volumeOn V))
    (hFcoord : ∀ i : Fin d,
      AEStronglyMeasurable (fun x => F x i) (volumeOn V)) :
    MemVectorL2On (euclideanBall z R) F := by
  let B := euclideanBall z R
  let f : Vec d → ℝ := fun x => vecEuclideanNorm (F x)
  have hBmem : MemLp f (ENNReal.ofReal p) (volumeOn B) := by
    dsimp only [f, B]
    exact hF.mono_measure (Measure.restrict_mono hBV le_rfl)
  let : IsFiniteMeasure (volumeOn B) :=
    isFiniteMeasure_volumeOn_euclideanBall z hR.le
  have hBtwo : MemLp f (ENNReal.ofReal (2 : ℝ)) (volumeOn B) :=
    hBmem.mono_exponent (ENNReal.ofReal_le_ofReal hp)
  intro i
  have hCoord : AEStronglyMeasurable (fun x => F x i) (volumeOn B) :=
    (hFcoord i).mono_measure (Measure.restrict_mono hBV le_rfl)
  simpa only [ENNReal.ofReal_ofNat] using hBtwo.of_le hCoord (by
    filter_upwards with x
    simpa only [f, Real.norm_eq_abs,
      abs_of_nonneg (vecEuclideanNorm_nonneg (F x))] using
      abs_apply_le_vecEuclideanNorm (F x) i)

end PDE
