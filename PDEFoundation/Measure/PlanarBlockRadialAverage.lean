module

public import PDEFoundation.Measure.PlanarBlockOddAverage
public import PDEFoundation.Measure.BallVolume
public import PDEFoundation.Ambient.PlanarBlockRadialMeasurability
public import PDEFoundation.Analysis.PlanarQuarterTurnRadialReflection
public import PDEFoundation.Ambient.MatAppendEllipticity
public import PDEFoundation.Ambient.MatAppendPerturbation
public import PDEFoundation.Ambient.RadialPerturbationSize
public import PDEFoundation.Sobolev.Mean

/-! # Averages of radial coefficients extended in unused coordinates -/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

private theorem integrable_planarBlock_radialReflectionMatrix
    (n : ℕ) {R : ℝ} (hR : 0 < R) (i j : Fin 2) :
    Integrable
      (fun z : Vec (2 + n) => radialReflectionMatrix ((vecAppendEquiv 2 n z).1) i j)
      (normalizedVolumeOn (euclideanBall (0 : Vec (2 + n)) R)) := by
  let μ := normalizedVolumeOn (euclideanBall (0 : Vec (2 + n)) R)
  let : IsProbabilityMeasure μ :=
    isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top
      (volume_euclideanBall_pos _ hR)
      (lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top _ hR.le))
  apply Integrable.mono' (integrable_const (1 : ℝ))
  · exact (measurable_planarBlock_radialReflectionMatrix_apply n i j).aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_eq_abs]
    let x := (vecAppendEquiv 2 n z).1
    have hentry : matVecMul (radialReflectionMatrix x) (basisVec j) i =
        radialReflectionMatrix x i j := by
      fin_cases j <;> simp [matVecMul, basisVec_apply]
    rw [← hentry]
    exact (abs_apply_le_vecEuclideanNorm _ i).trans (by
      rw [vecEuclideanNorm_matVecMul_radialReflectionMatrix,
        vecEuclideanNorm_basisVec])

/-- The planar reflection has zero average on a round ball in every ambient
dimension. Its bounded entries are integrated before quarter-turn cancellation
is used; the set on which the first block vanishes has measure zero. -/
theorem integral_planarBlock_radialReflectionMatrix_normalizedVolumeOn_ball
    (n : ℕ) {R : ℝ} (hR : 0 < R) (i j : Fin 2) :
    ∫ z : Vec (2 + n), radialReflectionMatrix (vecAppendEquiv 2 n z).1 i j
      ∂normalizedVolumeOn (euclideanBall (0 : Vec (2 + n)) R) = 0 := by
  apply integral_planarBlockOdd_normalizedVolumeOn_ball_eq_zero n hR
    (fun x => radialReflectionMatrix x i j)
    (integrable_planarBlock_radialReflectionMatrix n hR i j)
  intro x hx
  rw [radialReflectionMatrix_planarQuarterTurn x hx]
  rfl

/-- Extending the planar radial coefficient by the identity preserves its
exact average, including after multiplying the planar block by any scalar.
The unused coordinates carry the identity coefficient. -/
theorem integralAverage_matAppend_smul_one_add_planarRadialReflectionMatrix
    (n : ℕ) {R : ℝ} (hR : 0 < R) (c δ : ℝ) :
    (fun i j => integralAverage (euclideanBall (0 : Vec (2 + n)) R)
      (fun z => matAppend
        (c • ((1 : Mat 2) + δ • radialReflectionMatrix (vecAppendEquiv 2 n z).1))
        (1 : Mat n) i j)) = matAppend (c • (1 : Mat 2)) (1 : Mat n) := by
  let μ := normalizedVolumeOn (euclideanBall (0 : Vec (2 + n)) R)
  let : IsProbabilityMeasure μ :=
    isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top
      (volume_euclideanBall_pos _ hR)
      (lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top _ hR.le))
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [matAppend_apply_castAdd_castAdd]
      rw [← integral_normalizedVolumeOn_eq_integralAverage]
      simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
      have hq := integrable_planarBlock_radialReflectionMatrix n hR i j
      rw [integral_const_mul, integral_add (integrable_const _) (hq.const_mul δ),
        integral_const_mul,
        integral_planarBlock_radialReflectionMatrix_normalizedVolumeOn_ball n hR i j]
      simp
    · simp only [matAppend_apply_castAdd_natAdd]
      rw [← integral_normalizedVolumeOn_eq_integralAverage]
      simp
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [matAppend_apply_natAdd_castAdd]
      rw [← integral_normalizedVolumeOn_eq_integralAverage]
      simp
    · simp only [matAppend_apply_natAdd_natAdd]
      rw [← integral_normalizedVolumeOn_eq_integralAverage]
      simp

/-- The unscaled coefficient of the higher dimensional oscillation example
has average exactly equal to the identity on every centered round ball. -/
theorem integralAverage_matAppend_one_add_planarRadialReflectionMatrix
    (n : ℕ) {R : ℝ} (hR : 0 < R) (δ : ℝ) :
    (fun i j => integralAverage (euclideanBall (0 : Vec (2 + n)) R)
      (fun z => matAppend
        ((1 : Mat 2) + δ • radialReflectionMatrix (vecAppendEquiv 2 n z).1)
        (1 : Mat n) i j)) = (1 : Mat (2 + n)) := by
  simpa only [one_smul, matAppend_one_one] using
    integralAverage_matAppend_smul_one_add_planarRadialReflectionMatrix n hR 1 δ

/-- The unused identity block preserves the exact perturbation threshold. -/
theorem isMatrixPerturbationLE_matAppend_one_add_radialReflectionMatrix_iff
    (n : ℕ) (δ ε : ℝ) (hε : 0 ≤ ε) (x : Vec 2) :
    IsMatrixPerturbationLE ε
      (matAppend ((1 : Mat 2) + δ • radialReflectionMatrix x) (1 : Mat n))
      (1 : Mat (2 + n)) ↔ |δ| ≤ ε := by
  rw [← matAppend_one_one 2 n]
  exact (isMatrixPerturbationLE_matAppend_same_iff hε _ _ _).trans
    (isMatrixPerturbationLE_one_add_radialReflectionMatrix_iff (by norm_num) δ ε x)

end

end PDE
