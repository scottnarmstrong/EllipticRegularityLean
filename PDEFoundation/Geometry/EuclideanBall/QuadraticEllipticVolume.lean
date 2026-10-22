module

public import PDEFoundation.Geometry.EuclideanBall.QuadraticEllipticImage
public import PDEFoundation.Measure.BallVolume
public import PDEFoundation.Measure.LinearAverage

/-! # Volume bounds for quadratic elliptic images of round balls -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The inverse image of a round ball under the quadratic elliptic normalizer
is open, has positive finite volume, and contains a native ball of the same
radius. -/
theorem quadraticEllipticNormalizer_symm_image_volume_geometry
    {A0 : Mat d}
    (hLower : ∀ xi : Vec d,
      vecNormSq xi ≤ vecDot xi (matVecMul A0 xi))
    (z : Vec d) {R : ℝ} (hR : 0 < R) :
    let e := quadraticEllipticNormalizerContinuousLinearEquiv hLower
    let E := e.symm '' euclideanBall (e z) R
    IsOpen E ∧ MeasurableSet E ∧
      0 < volume E ∧ volume E < ∞ ∧
      e '' E = euclideanBall (e z) R ∧
      volume (euclideanBall (0 : Vec d) R) ≤ volume E := by
  let e := quadraticEllipticNormalizerContinuousLinearEquiv hLower
  let E := e.symm '' euclideanBall (e z) R
  have hOpen : IsOpen E :=
    e.symm.isOpenMap _ (isOpen_euclideanBall (e z) R)
  have hPos : 0 < volume E := by
    exact volume_image_linearEquiv_pos e.symm
      (volume_euclideanBall_pos (e z) hR)
  have hFinite : volume E < ∞ := by
    exact volume_image_linearEquiv_lt_top e.symm
      (lt_top_iff_ne_top.2 (volume_euclideanBall_ne_top (e z) hR.le))
  have hNative : euclideanBall z R ⊆ E :=
    euclideanBall_subset_quadraticEllipticNormalizer_symm_image
      hLower hR z
  have hCenter :
      volume (euclideanBall (0 : Vec d) R) =
        volume (euclideanBall z R) := by
    rw [volume_euclideanBall_eq_unit_mul_of_pos (0 : Vec d) hR,
      volume_euclideanBall_eq_unit_mul_of_pos z hR]
  refine ⟨hOpen, hOpen.measurableSet, hPos, hFinite, ?_, ?_⟩
  · exact quadraticEllipticNormalizer_image_symm_image_euclideanBall
      hLower z
  · rw [hCenter]
    exact measure_mono hNative

/-- At the canonical quarter scale, the normalized elliptipsoid and its
half-radius subellipsoid are measurable positive finite sets inside the unit
ball.  Their volume lower bounds are uniform in the matrix and center. -/
theorem quadraticEllipticNormalizer_quarter_volume_geometry
    {A0 : Mat d} {Lam : ℝ} (hLam : 1 ≤ Lam)
    (hLower : ∀ xi : Vec d,
      vecNormSq xi ≤ vecDot xi (matVecMul A0 xi))
    (hUpper : ∀ xi : Vec d,
      vecDot xi (matVecMul (symmPart A0) xi) ≤ Lam * vecNormSq xi)
    {z : Vec d} (hz : z ∈ euclideanClosedBall (0 : Vec d) (1 / 2)) :
    let e := quadraticEllipticNormalizerContinuousLinearEquiv hLower
    let rho := 1 / (4 * Real.sqrt Lam)
    let E := e.symm '' euclideanBall (e z) rho
    let Ehalf := e.symm '' euclideanBall (e z) (rho / 2)
    IsOpen E ∧ MeasurableSet E ∧ 0 < volume E ∧ volume E < ∞ ∧
      IsOpen Ehalf ∧ MeasurableSet Ehalf ∧
      0 < volume Ehalf ∧ volume Ehalf < ∞ ∧
      e '' E = euclideanBall (e z) rho ∧
      e '' Ehalf = euclideanBall (e z) (rho / 2) ∧
      Ehalf ⊆ E ∧
      volume (euclideanBall (0 : Vec d) rho) ≤ volume E ∧
      volume (euclideanBall (0 : Vec d) (rho / 2)) ≤ volume Ehalf ∧
      volume E ≤ volume (euclideanBall (0 : Vec d) 1) ∧
      volume Ehalf ≤ volume (euclideanBall (0 : Vec d) 1) := by
  let e := quadraticEllipticNormalizerContinuousLinearEquiv hLower
  let rho := 1 / (4 * Real.sqrt Lam)
  let E := e.symm '' euclideanBall (e z) rho
  let Ehalf := e.symm '' euclideanBall (e z) (rho / 2)
  have hsqrt : 0 < Real.sqrt Lam :=
    Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one hLam)
  have hrho : 0 < rho := by
    dsimp [rho]
    positivity
  have hrhoHalf : 0 < rho / 2 := by positivity
  have hE := quadraticEllipticNormalizer_symm_image_volume_geometry
    hLower z hrho
  have hEhalf := quadraticEllipticNormalizer_symm_image_volume_geometry
    hLower z hrhoHalf
  have hHalfSubset : Ehalf ⊆ E := by
    exact Set.image_mono (euclideanBall_mono hrhoHalf.le (by linarith))
  have hEUnit : E ⊆ euclideanBall (0 : Vec d) 1 :=
    quadraticEllipticNormalizer_symm_image_quarter_subset_unitBall
      hLam hLower hUpper hz
  have hEhalfUnit : Ehalf ⊆ euclideanBall (0 : Vec d) 1 :=
    hHalfSubset.trans hEUnit
  exact ⟨hE.1, hE.2.1, hE.2.2.1, hE.2.2.2.1,
    hEhalf.1, hEhalf.2.1, hEhalf.2.2.1, hEhalf.2.2.2.1,
    hE.2.2.2.2.1, hEhalf.2.2.2.2.1, hHalfSubset,
    hE.2.2.2.2.2, hEhalf.2.2.2.2.2,
    measure_mono hEUnit, measure_mono hEhalfUnit⟩

end

end PDE
