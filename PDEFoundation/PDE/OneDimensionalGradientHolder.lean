module

public import PDEFoundation.Regularity.FieldHolder

/-!
# One-dimensional Hölder control from constant flux
-/

@[expose] public section

namespace PDE

noncomputable section

private theorem oneDimensional_diag_lower'
    {Lam : ℝ} {A : Mat 1} (hA : IsEllipticMatrix 1 Lam A) :
    1 ≤ A 0 0 := by
  have h := hA.coercive (basisVec 0)
  norm_num [vecNormSq, vecDot, matVecMul, basisVec] at h ⊢
  exact h

private theorem vecEuclideanNorm_fin_one (v : Vec 1) :
    vecEuclideanNorm v = |v 0| := by
  unfold vecEuclideanNorm vecNormSq vecDot
  simp only [Fin.sum_univ_one]
  rw [← pow_two, Real.sqrt_sq_eq_abs]

/-- In one dimension, a pointwise constant-flux identity, Hölder coefficient
and forcing fields, and a pointwise gradient bound imply the sharp algebraic
Hölder estimate for the gradient. -/
theorem oneDimensional_gradient_holder_of_constantFlux
    {U : Set (Vec 1)} {alpha Ka KF B Lam c : ℝ}
    (hKa : 0 ≤ Ka) (_hKF : 0 ≤ KF) (_hB : 0 ≤ B)
    {a : CoeffField 1} {F G : Vec 1 → Vec 1}
    (ha : EuclideanMatrixHolderSeminormLE U a alpha Ka)
    (hF : EuclideanFieldHolderSeminormLE U F alpha KF)
    (hell : ∀ x ∈ U, IsEllipticMatrix 1 Lam (a x))
    (hflux : ∀ x ∈ U, a x 0 0 * G x 0 + F x 0 = c)
    (hGbound : ∀ x ∈ U, vecEuclideanNorm (G x) ≤ B) :
    EuclideanFieldHolderSeminormLE U G alpha (KF + Ka * B) := by
  intro x hx y hy
  have hax : 1 ≤ a x 0 0 := oneDimensional_diag_lower' (hell x hx)
  have hidentity :
      a x 0 0 * (G x 0 - G y 0) =
        (F y 0 - F x 0) + (a y 0 0 - a x 0 0) * G y 0 := by
    calc
      a x 0 0 * (G x 0 - G y 0) =
          (a x 0 0 * G x 0 + F x 0) - F x 0 - a x 0 0 * G y 0 := by ring
      _ = c - F x 0 - a x 0 0 * G y 0 := by rw [hflux x hx]
      _ = (F y 0 - F x 0) + (a y 0 0 - a x 0 0) * G y 0 := by
        rw [← hflux y hy]
        ring
  have hFcoord := (hF.coordinate 0) x hx y hy
  have hacoord := (ha.coordinate 0 0) x hx y hy
  have hGy : |G y 0| ≤ B := by
    rw [← vecEuclideanNorm_fin_one]
    exact hGbound y hy
  have hscalar : |G x 0 - G y 0| ≤
      (KF + Ka * B) * vecEuclideanNorm (x - y) ^ alpha := by
    have hleft : |G x 0 - G y 0| ≤
        |a x 0 0 * (G x 0 - G y 0)| := by
      rw [abs_mul, abs_of_nonneg (le_trans (by norm_num) hax)]
      exact le_mul_of_one_le_left (abs_nonneg _) hax
    calc
      |G x 0 - G y 0| ≤
          |a x 0 0 * (G x 0 - G y 0)| := hleft
      _ = |(F y 0 - F x 0) +
          (a y 0 0 - a x 0 0) * G y 0| := by rw [hidentity]
      _ ≤ |F y 0 - F x 0| +
          |a y 0 0 - a x 0 0| * |G y 0| := by
        calc
          _ ≤ |F y 0 - F x 0| +
              |(a y 0 0 - a x 0 0) * G y 0| := abs_add_le _ _
          _ = _ := by rw [abs_mul]
      _ ≤ KF * vecEuclideanNorm (x - y) ^ alpha +
          (Ka * vecEuclideanNorm (x - y) ^ alpha) * B := by
        apply add_le_add
        · simpa only [abs_sub_comm] using hFcoord
        · exact mul_le_mul (by simpa only [abs_sub_comm] using hacoord) hGy
            (abs_nonneg _)
            (mul_nonneg hKa (Real.rpow_nonneg (vecEuclideanNorm_nonneg _) alpha))
      _ = (KF + Ka * B) * vecEuclideanNorm (x - y) ^ alpha := by ring
  rw [vecEuclideanNorm_fin_one]
  simpa only [Pi.sub_apply] using hscalar

end

end PDE
