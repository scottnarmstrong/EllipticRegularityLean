module

public import PDEFoundation.Ambient.QuadraticMatrixConjugation
public import PDEFoundation.Geometry.EuclideanBall.Basic

/-! # Round balls under quadratic elliptic normalization -/

@[expose] public section

namespace PDE

noncomputable section

variable {d : ℕ}

/-- The quadratic elliptic normalizer contracts native round balls. -/
theorem quadraticEllipticNormalizer_image_euclideanBall_subset
    {A0 : Mat d} {R : ℝ}
    (hLower : ∀ xi : Vec d,
      vecNormSq xi ≤ vecDot xi (matVecMul A0 xi))
    (hR : 0 < R) (z : Vec d) :
    quadraticEllipticNormalizerContinuousLinearEquiv hLower ''
        euclideanBall z R ⊆
      euclideanBall
        (quadraticEllipticNormalizerContinuousLinearEquiv hLower z) R := by
  let e := quadraticEllipticNormalizerContinuousLinearEquiv hLower
  rintro _ ⟨x, hx, rfl⟩
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hR).2
  have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt hR).1 hx
  calc
    vecEuclideanNorm (e x - e z) = vecEuclideanNorm (e (x - z)) := by
      rw [e.map_sub]
    _ ≤ vecEuclideanNorm (x - z) :=
      vecEuclideanNorm_quadraticEllipticNormalizerContinuousLinearEquiv_le
        hLower (x - z)
    _ < R := hx'

/-- The inverse image of a normalized round ball contains the round ball of
the same radius. -/
theorem euclideanBall_subset_quadraticEllipticNormalizer_symm_image
    {A0 : Mat d} {R : ℝ}
    (hLower : ∀ xi : Vec d,
      vecNormSq xi ≤ vecDot xi (matVecMul A0 xi))
    (hR : 0 < R) (z : Vec d) :
    euclideanBall z R ⊆
      (quadraticEllipticNormalizerContinuousLinearEquiv hLower).symm ''
        euclideanBall
          (quadraticEllipticNormalizerContinuousLinearEquiv hLower z) R := by
  let e := quadraticEllipticNormalizerContinuousLinearEquiv hLower
  intro x hx
  refine ⟨e x, quadraticEllipticNormalizer_image_euclideanBall_subset
    hLower hR z ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩

/-- The inverse image of a normalized round ball lies in the round ball whose
radius is enlarged by the square root of the upper quadratic constant. -/
theorem quadraticEllipticNormalizer_symm_image_subset_euclideanBall
    {A0 : Mat d} {Lam R : ℝ} (hLam : 1 ≤ Lam)
    (hLower : ∀ xi : Vec d,
      vecNormSq xi ≤ vecDot xi (matVecMul A0 xi))
    (hUpper : ∀ xi : Vec d,
      vecDot xi (matVecMul (symmPart A0) xi) ≤ Lam * vecNormSq xi)
    (hR : 0 < R) (z : Vec d) :
    (quadraticEllipticNormalizerContinuousLinearEquiv hLower).symm ''
        euclideanBall
          (quadraticEllipticNormalizerContinuousLinearEquiv hLower z) R ⊆
      euclideanBall z (Real.sqrt Lam * R) := by
  let e := quadraticEllipticNormalizerContinuousLinearEquiv hLower
  have hsqrt : 0 < Real.sqrt Lam :=
    Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one hLam)
  have hRadius : 0 < Real.sqrt Lam * R := mul_pos hsqrt hR
  rintro _ ⟨y, hy, rfl⟩
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hRadius).2
  have hy' := (mem_euclideanBall_iff_vecEuclideanNorm_lt hR).1 hy
  calc
    vecEuclideanNorm (e.symm y - z) =
        vecEuclideanNorm (e.symm (y - e z)) := by
      rw [e.symm.map_sub, e.symm_apply_apply]
    _ ≤ Real.sqrt Lam * vecEuclideanNorm (y - e z) :=
      vecEuclideanNorm_quadraticEllipticNormalizerContinuousLinearEquiv_symm_le
        (hLam.trans' zero_le_one) hLower hUpper (y - e z)
    _ < Real.sqrt Lam * R := mul_lt_mul_of_pos_left hy' hsqrt

/-- Applying the forward normalizer to its inverse image of a round ball
recovers that ball exactly. -/
theorem quadraticEllipticNormalizer_image_symm_image_euclideanBall
    {A0 : Mat d} {R : ℝ}
    (hLower : ∀ xi : Vec d,
      vecNormSq xi ≤ vecDot xi (matVecMul A0 xi))
    (z : Vec d) :
    quadraticEllipticNormalizerContinuousLinearEquiv hLower ''
        ((quadraticEllipticNormalizerContinuousLinearEquiv hLower).symm ''
          euclideanBall
            (quadraticEllipticNormalizerContinuousLinearEquiv hLower z) R) =
      euclideanBall
        (quadraticEllipticNormalizerContinuousLinearEquiv hLower z) R := by
  let e := quadraticEllipticNormalizerContinuousLinearEquiv hLower
  ext y
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    change e (e.symm w) ∈ euclideanBall (e z) R
    rw [e.apply_symm_apply]
    exact hw
  · intro hy
    exact ⟨e.symm y, ⟨y, hy, rfl⟩, e.apply_symm_apply y⟩

/-- At the canonical quarter scale, every inverse normalized ball centered in
the closed half ball remains inside the unit ball. -/
theorem quadraticEllipticNormalizer_symm_image_quarter_subset_unitBall
    {A0 : Mat d} {Lam : ℝ} (hLam : 1 ≤ Lam)
    (hLower : ∀ xi : Vec d,
      vecNormSq xi ≤ vecDot xi (matVecMul A0 xi))
    (hUpper : ∀ xi : Vec d,
      vecDot xi (matVecMul (symmPart A0) xi) ≤ Lam * vecNormSq xi)
    {z : Vec d} (hz : z ∈ euclideanClosedBall (0 : Vec d) (1 / 2)) :
    (quadraticEllipticNormalizerContinuousLinearEquiv hLower).symm ''
        euclideanBall
          (quadraticEllipticNormalizerContinuousLinearEquiv hLower z)
          (1 / (4 * Real.sqrt Lam)) ⊆
      euclideanBall (0 : Vec d) 1 := by
  have hsqrt : 0 < Real.sqrt Lam := Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one hLam)
  have hrho : 0 < 1 / (4 * Real.sqrt Lam) := by positivity
  have hEllipsoid := quadraticEllipticNormalizer_symm_image_subset_euclideanBall
    hLam hLower hUpper hrho z
  intro x hx
  have hxBall := hEllipsoid hx
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).2
  have hxz := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hxBall
  have hz0 :=
    (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by norm_num)).1 hz
  have htri : vecEuclideanNorm (x - 0) ≤
      vecEuclideanNorm (x - z) + vecEuclideanNorm (z - 0) := by
    calc
      vecEuclideanNorm (x - 0) =
          vecEuclideanNorm ((x - z) + (z - 0)) := by
        congr 1
        ext i
        simp
      _ ≤ _ := vecEuclideanNorm_add_le _ _
  have hcancel : Real.sqrt Lam * (1 / (4 * Real.sqrt Lam)) = 1 / 4 := by
    field_simp [hsqrt.ne']
  rw [hcancel] at hxz
  linarith

/-- At half the canonical quarter scale, the inverse normalized ball contains
the native round ball with the same radius. -/
theorem euclideanBall_half_quarter_subset_quadraticEllipticNormalizer_symm_image
    {A0 : Mat d} {Lam : ℝ} (hLam : 1 ≤ Lam)
    (hLower : ∀ xi : Vec d,
      vecNormSq xi ≤ vecDot xi (matVecMul A0 xi))
    (z : Vec d) :
    euclideanBall z ((1 / (4 * Real.sqrt Lam)) / 2) ⊆
      (quadraticEllipticNormalizerContinuousLinearEquiv hLower).symm ''
        euclideanBall
          (quadraticEllipticNormalizerContinuousLinearEquiv hLower z)
          ((1 / (4 * Real.sqrt Lam)) / 2) := by
  apply euclideanBall_subset_quadraticEllipticNormalizer_symm_image hLower
  have hsqrt : 0 < Real.sqrt Lam := Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one hLam)
  positivity

end

end PDE
