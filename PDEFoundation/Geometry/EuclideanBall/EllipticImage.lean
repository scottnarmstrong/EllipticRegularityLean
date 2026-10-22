module

public import PDEFoundation.Ambient.MatrixConjugation
public import PDEFoundation.Geometry.EuclideanBall.Basic

/-!
# Euclidean balls under elliptic normalization

The canonical normalizer sends a Euclidean ball into the ball of the same
radius and contains a concentric ball whose radius loses `Real.sqrt Lam`.
-/

@[expose] public section

namespace PDE

noncomputable section

variable {d : ℕ}

/-- The canonical elliptic normalizer contracts Euclidean balls. -/
theorem ellipticNormalizer_image_euclideanBall_subset
    {A : Mat d} {Lam R : ℝ} (hA : IsEllipticMatrix 1 Lam A) (hR : 0 < R)
    (z : Vec d) :
    ellipticNormalizerContinuousLinearEquiv hA '' euclideanBall z R ⊆
      euclideanBall (ellipticNormalizerContinuousLinearEquiv hA z) R := by
  let e := ellipticNormalizerContinuousLinearEquiv hA
  rintro _ ⟨x, hx, rfl⟩
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hR).2
  have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt hR).1 hx
  calc
    vecEuclideanNorm (e x - e z) = vecEuclideanNorm (e (x - z)) := by
      rw [e.map_sub]
    _ ≤ vecEuclideanNorm (x - z) :=
      vecEuclideanNorm_ellipticNormalizerContinuousLinearEquiv_le hA (x - z)
    _ < R := hx'

/-- The image under the canonical elliptic normalizer contains the ball with
radius reduced by `Real.sqrt Lam`. -/
theorem euclideanBall_subset_ellipticNormalizer_image
    {A : Mat d} {Lam R : ℝ} (hA : IsEllipticMatrix 1 Lam A) (hR : 0 < R)
    (z : Vec d) :
    euclideanBall (ellipticNormalizerContinuousLinearEquiv hA z)
        (R / Real.sqrt Lam) ⊆
      ellipticNormalizerContinuousLinearEquiv hA '' euclideanBall z R := by
  let e := ellipticNormalizerContinuousLinearEquiv hA
  have hsqrt : 0 < Real.sqrt Lam := Real.sqrt_pos.mpr hA.Lam_pos
  have hradius : 0 < R / Real.sqrt Lam := div_pos hR hsqrt
  intro y hy
  have hy' := (mem_euclideanBall_iff_vecEuclideanNorm_lt hradius).1 hy
  refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hR).2
  have hinv :
      vecEuclideanNorm (e.symm (y - e z)) ≤
        Real.sqrt Lam * vecEuclideanNorm (y - e z) :=
    vecEuclideanNorm_ellipticNormalizerContinuousLinearEquiv_symm_le hA (y - e z)
  calc
    vecEuclideanNorm (e.symm y - z) =
        vecEuclideanNorm (e.symm (y - e z)) := by
      rw [e.symm.map_sub, e.symm_apply_apply]
    _ ≤ Real.sqrt Lam * vecEuclideanNorm (y - e z) := hinv
    _ < Real.sqrt Lam * (R / Real.sqrt Lam) :=
      mul_lt_mul_of_pos_left hy' hsqrt
    _ = R := by field_simp [hsqrt.ne']

/-- The forward ball containment at half radius. -/
theorem ellipticNormalizer_image_euclideanBall_half_subset
    {A : Mat d} {Lam R : ℝ} (hA : IsEllipticMatrix 1 Lam A) (hR : 0 < R)
    (z : Vec d) :
    ellipticNormalizerContinuousLinearEquiv hA '' euclideanBall z (R / 2) ⊆
      euclideanBall (ellipticNormalizerContinuousLinearEquiv hA z) (R / 2) := by
  exact ellipticNormalizer_image_euclideanBall_subset hA (div_pos hR (by norm_num)) z

/-- The reverse ball containment at half radius. -/
theorem euclideanBall_half_subset_ellipticNormalizer_image
    {A : Mat d} {Lam R : ℝ} (hA : IsEllipticMatrix 1 Lam A) (hR : 0 < R)
    (z : Vec d) :
    euclideanBall (ellipticNormalizerContinuousLinearEquiv hA z)
        ((R / 2) / Real.sqrt Lam) ⊆
      ellipticNormalizerContinuousLinearEquiv hA '' euclideanBall z (R / 2) := by
  exact euclideanBall_subset_ellipticNormalizer_image hA (div_pos hR (by norm_num)) z

end

end PDE
