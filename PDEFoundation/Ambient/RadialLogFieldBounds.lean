module

public import PDEFoundation.Measure.RadialLogModeLp
public import PDEFoundation.Analysis.RadialForcingDivergence

@[expose] public section

namespace PDE

/-- The logarithmic gradient differs from its axial logarithmic term by a
vector of Euclidean magnitude at most one. -/
theorem vecEuclideanNorm_radialLogGradientField_bounds
    {d : ℕ} (k : Fin d) (x : Vec d) :
    |Real.log (vecEuclideanNorm x)| - 1 ≤
        vecEuclideanNorm (radialLogGradientField k x) ∧
      vecEuclideanNorm (radialLogGradientField k x) ≤
        |Real.log (vecEuclideanNorm x)| + 1 := by
  have hdecomp : radialLogGradientField k x =
      Real.log (vecEuclideanNorm x) • basisVec k +
        (-1 / 2 : ℝ) • radialForcing k x := by
    ext i
    simp only [radialLogGradientField, radialForcing, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  have hF : vecEuclideanNorm ((1 / 2 : ℝ) • radialForcing k x) ≤ 1 := by
    rw [vecEuclideanNorm_smul]
    norm_num
    linarith only [vecEuclideanNorm_radialForcing_le_two k x]
  have hnegF : vecEuclideanNorm ((-1 / 2 : ℝ) • radialForcing k x) ≤ 1 := by
    rw [vecEuclideanNorm_smul] at hF ⊢
    norm_num at hF ⊢
    exact hF
  have haxial : vecEuclideanNorm (Real.log (vecEuclideanNorm x) • basisVec k) =
      |Real.log (vecEuclideanNorm x)| := by
    rw [vecEuclideanNorm_smul, vecEuclideanNorm_basisVec, mul_one]
  constructor
  · have hrev : Real.log (vecEuclideanNorm x) • basisVec k =
        radialLogGradientField k x + (1 / 2 : ℝ) • radialForcing k x := by
      rw [hdecomp]
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have h := vecEuclideanNorm_add_le (radialLogGradientField k x)
      ((1 / 2 : ℝ) • radialForcing k x)
    rw [← hrev, haxial] at h
    linarith only [h, hF]
  · rw [hdecomp]
    exact (vecEuclideanNorm_add_le _ _).trans
      (by rw [haxial]; exact add_le_add le_rfl hnegF)

end PDE
