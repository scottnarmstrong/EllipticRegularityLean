module

public import PDEFoundation.Ambient.QuadraticMatrixConjugation
public import PDEFoundation.Measure.EuclideanFieldMeasurability
public import PDEFoundation.Measure.LinearNormalizedVolume
public import PDEFoundation.Sobolev.W1p.EuclideanGradient

/-! # Forcing transport under quadratic elliptic normalization -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The quadratically normalized forcing retains actual raw `Lᵖ` membership
and its normalized Euclidean `Lᵖ` norm does not increase. -/
theorem quadraticEllipticNormalizer_forcing_memLp_and_mean_le
    {d : ℕ} {U : Set (Vec d)} (hUPos : 0 < volume U)
    (hUTop : volume U < ∞) {p : ENNReal}
    {A0 : Mat d}
    (hLower : ∀ xi : Vec d,
      vecNormSq xi ≤ vecDot xi (matVecMul A0 xi))
    (F : Vec d → Vec d)
    (hFcoord : ∀ i, AEStronglyMeasurable (fun x => F x i) (volumeOn U))
    (hF : MemLp (fun x => vecEuclideanNorm (F x)) p (volumeOn U)) :
    let e := quadraticEllipticNormalizerContinuousLinearEquiv hLower
    let T := ellipticNormalizer A0
    let X := e '' U
    let F' : Vec d → Vec d := fun y => matVecMul T (F (e.symm y))
    (∀ i, AEStronglyMeasurable (fun y => F' y i) (volumeOn X)) ∧
      ∃ hF' : MemLp (fun y => vecEuclideanNorm (F' y)) p (volumeOn X),
        euclideanFieldLpMeanNormOn X p F'
            (memLp_normalizedVolumeOn_of_memLpOn hF'
              (volume_image_linearEquiv_pos e hUPos)) ≤
          euclideanFieldLpMeanNormOn U p F
            (memLp_normalizedVolumeOn_of_memLpOn hF hUPos) := by
  classical
  dsimp only
  let e := quadraticEllipticNormalizerContinuousLinearEquiv hLower
  let T := ellipticNormalizer A0
  let X := e '' U
  let F' : Vec d → Vec d := fun y => matVecMul T (F (e.symm y))
  have hXPos : 0 < volume X := volume_image_linearEquiv_pos e hUPos
  have hXTop : volume X < ∞ := volume_image_linearEquiv_lt_top e hUTop
  have hFMean := memLp_normalizedVolumeOn_of_memLpOn hF hUPos
  have hsymm := measurePreserving_linearEquiv_symm_normalizedVolumeOn e U
  have hFcoordRaw (i : Fin d) : MemLp (fun x => F x i) p (volumeOn U) := by
    apply hF.of_le (hFcoord i)
    filter_upwards with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (vecEuclideanNorm_nonneg (F x))]
      using abs_apply_le_vecEuclideanNorm (F x) i
  have hFcoordMean (i : Fin d) : MemLp (fun x => F x i) p
      (normalizedVolumeOn U) :=
    memLp_normalizedVolumeOn_of_memLpOn (hFcoordRaw i) hUPos
  have hpullCoord (i : Fin d) : MemLp (fun y => F (e.symm y) i) p
      (normalizedVolumeOn X) := by
    simpa only [Function.comp_apply] using!
      (hFcoordMean i).comp_measurePreserving hsymm
  have hF'coordMean (i : Fin d) : MemLp (fun y => F' y i) p
      (normalizedVolumeOn X) := by
    let s : Finset (Fin d) := Finset.univ
    change MemLp (fun y => ∑ j ∈ s, T i j * F (e.symm y) j) p
      (normalizedVolumeOn X)
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hjs ih =>
        simpa only [Finset.sum_insert hjs] using!
          ((hpullCoord j).const_mul (T i j)).add ih
  have hF'Meas : AEStronglyMeasurable (fun y => vecEuclideanNorm (F' y))
      (normalizedVolumeOn X) :=
    aestronglyMeasurable_vecEuclideanNorm_of_coord fun i =>
      (hF'coordMean i).aestronglyMeasurable
  have hpullMag : MemLp (fun y => vecEuclideanNorm (F (e.symm y))) p
      (normalizedVolumeOn X) := by
    simpa only [Function.comp_apply] using! hFMean.comp_measurePreserving hsymm
  have hpoint : ∀ y, vecEuclideanNorm (F' y) ≤
      vecEuclideanNorm (F (e.symm y)) := by
    intro y
    exact vecEuclideanNorm_ellipticNormalizer_mulVec_le hLower _
  have hF'Mean : MemLp (fun y => vecEuclideanNorm (F' y)) p
      (normalizedVolumeOn X) := by
    apply hpullMag.of_le hF'Meas
    filter_upwards with y
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (vecEuclideanNorm_nonneg (F' y)),
      abs_of_nonneg (vecEuclideanNorm_nonneg (F (e.symm y)))] using hpoint y
  have hF'Raw : MemLp (fun y => vecEuclideanNorm (F' y)) p (volumeOn X) := by
    rw [← volume_smul_normalizedVolumeOn_eq_volumeOn hXPos hXTop]
    exact hF'Mean.smul_measure hXTop.ne
  have hCoordRaw (i : Fin d) :
      AEStronglyMeasurable (fun y => F' y i) (volumeOn X) := by
    rw [← volume_smul_normalizedVolumeOn_eq_volumeOn hXPos hXTop]
    exact (hF'coordMean i).aestronglyMeasurable.smul_measure (volume X)
  have hnorm : eLpNorm (fun y => vecEuclideanNorm (F' y)) p
      (normalizedVolumeOn X) ≤
      eLpNorm (fun y => vecEuclideanNorm (F (e.symm y))) p
        (normalizedVolumeOn X) := by
    apply eLpNorm_mono_ae hF'Meas
    filter_upwards with y
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (vecEuclideanNorm_nonneg (F' y)),
      abs_of_nonneg (vecEuclideanNorm_nonneg (F (e.symm y)))] using hpoint y
  have hpullNorm : eLpNorm (fun y => vecEuclideanNorm (F (e.symm y))) p
      (normalizedVolumeOn X) =
      eLpNorm (fun x => vecEuclideanNorm (F x)) p (normalizedVolumeOn U) := by
    simpa only [Function.comp_apply] using!
      eLpNorm_comp_measurePreserving hFMean.aestronglyMeasurable hsymm
  refine ⟨hCoordRaw, hF'Raw, ?_⟩
  change (eLpNorm (fun y => vecEuclideanNorm (F' y)) p
      (normalizedVolumeOn X)).toReal ≤
    (eLpNorm (fun x => vecEuclideanNorm (F x)) p
      (normalizedVolumeOn U)).toReal
  apply ENNReal.toReal_mono hFMean.eLpNorm_ne_top
  exact hnorm.trans_eq hpullNorm

end

end PDE
