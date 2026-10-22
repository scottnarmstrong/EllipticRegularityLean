module

public import PDEFoundation.Analysis.RadialModeGradient
public import PDEFoundation.Geometry.EuclideanBall.Topology

/-!
# Smoothness of coordinate radial modes away from the origin
-/

@[expose] public section

namespace PDE

noncomputable section

private theorem vecEuclideanNorm_rpow_eq_vecNormSq_rpow_half
    {d : ℕ} (x : Vec d) (a : ℝ) :
    Real.rpow (vecEuclideanNorm x) a =
      Real.rpow (vecNormSq x) (a / 2) := by
  have hn : 0 ≤ vecEuclideanNorm x := vecEuclideanNorm_nonneg x
  rw [← vecEuclideanNorm_sq]
  change (vecEuclideanNorm x) ^ a =
    ((vecEuclideanNorm x) ^ 2) ^ (a / 2)
  rw [← Real.rpow_natCast_mul hn 2 (a / 2)]
  congr 1
  ring

private theorem log_vecEuclideanNorm_eq_half_log_vecNormSq
    {d : ℕ} (x : Vec d) :
    Real.log (vecEuclideanNorm x) =
      (1 / 2 : ℝ) * Real.log (vecNormSq x) := by
  rw [← vecEuclideanNorm_sq, Real.log_pow]
  ring

private theorem vecNormSq_ne_zero_on_compl_singleton {d : ℕ} :
    ∀ x ∈ ({0} : Set (Vec d))ᶜ, vecNormSq x ≠ 0 := by
  intro x hx hzero
  exact hx (vecNormSq_eq_zero hzero)

/-- A coordinate homogeneous radial mode is smooth away from the origin. -/
theorem contDiffOn_coordinate_mul_vecEuclideanNorm_rpow
    {d : ℕ} (k : Fin d) (beta : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : Vec d => y k * Real.rpow (vecEuclideanNorm y) (beta - 1))
      ({0} : Set (Vec d))ᶜ := by
  have hpow : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : Vec d => Real.rpow (vecNormSq y) ((beta - 1) / 2))
      ({0} : Set (Vec d))ᶜ :=
    contDiff_vecNormSq.contDiffOn.rpow_const_of_ne
      vecNormSq_ne_zero_on_compl_singleton
  have hcoord : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Vec d => y k)
      ({0} : Set (Vec d))ᶜ := by fun_prop
  apply (hcoord.mul hpow).congr
  intro y hy
  rw [vecEuclideanNorm_rpow_eq_vecNormSq_rpow_half]

/-- A logarithmic coordinate radial mode is smooth away from the origin. -/
theorem contDiffOn_coordinate_mul_log_vecEuclideanNorm
    {d : ℕ} (k : Fin d) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : Vec d => y k * Real.log (vecEuclideanNorm y))
      ({0} : Set (Vec d))ᶜ := by
  have hlog : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : Vec d => Real.log (vecNormSq y))
      ({0} : Set (Vec d))ᶜ :=
    contDiff_vecNormSq.contDiffOn.log vecNormSq_ne_zero_on_compl_singleton
  have hcoord : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Vec d => y k)
      ({0} : Set (Vec d))ᶜ := by fun_prop
  have hsmooth := hcoord.mul ((contDiffOn_const (c := (1 / 2 : ℝ))).mul hlog)
  apply hsmooth.congr
  intro y hy
  rw [log_vecEuclideanNorm_eq_half_log_vecNormSq]

/-- Every coordinate of the homogeneous radial power field is smooth away
from the origin. -/
theorem contDiffOn_radialModePowerField_apply
    {d : ℕ} (k i : Fin d) (beta : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Vec d => radialModePowerField k beta y i)
      ({0} : Set (Vec d))ᶜ := by
  have hpow : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : Vec d => Real.rpow (vecNormSq y) ((beta - 1) / 2))
      ({0} : Set (Vec d))ᶜ :=
    contDiff_vecNormSq.contDiffOn.rpow_const_of_ne
      vecNormSq_ne_zero_on_compl_singleton
  have hquot : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : Vec d => y k / vecNormSq y) ({0} : Set (Vec d))ᶜ := by
    apply ContDiffOn.div (by fun_prop) contDiff_vecNormSq.contDiffOn
      vecNormSq_ne_zero_on_compl_singleton
  have hbody : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : Vec d => basisVec k i +
        (beta - 1) * (y k / vecNormSq y) * y i)
      ({0} : Set (Vec d))ᶜ := by fun_prop
  apply (hpow.mul hbody).congr
  intro y hy
  simp only [radialModePowerField, radialModeVector, Pi.smul_apply,
    smul_eq_mul, Pi.add_apply]
  rw [vecEuclideanNorm_rpow_eq_vecNormSq_rpow_half]

end

end PDE
