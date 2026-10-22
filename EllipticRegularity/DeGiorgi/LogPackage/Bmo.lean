module

public import EllipticRegularity.DeGiorgi.LogPackage.Defs
public import EllipticRegularity.DeGiorgi.LogPackage.Geom
public import EllipticRegularity.DeGiorgi.LogPackage.Average
public import PDEFoundation.Sobolev.Inequalities.ConvexPoincareL2

/-!
# The logarithm has bounded mean oscillation on interior balls

From the ball logarithmic energy estimate and the centered Poincare inequality we derive
`avg_{B_r(y)} |v - avg v| ≤ (K_d Λ)^{1/2}` for every ball `B_r(y) ⊆ B_{1/2}`.
-/

@[expose] public section

namespace PDE.DGNMLog

open MeasureTheory

/-- The dimensional constant in the BMO bound. -/
noncomputable def bmoConst (d : ℕ) : ℝ := (4 : ℝ) ^ (d + 1) * 16 * (3 / 2 : ℝ) ^ d

theorem bmoConst_pos (d : ℕ) : 0 < bmoConst d := by unfold bmoConst; positivity

/-- BMO bound on balls `B_r(y) ⊆ B_{1/2}` from the ball energy estimate. -/
theorem avg_abs_sub_avg_le_of_energy {d : ℕ} (i0 : Fin d) {Λ : ℝ} (hΛ : 0 < Λ)
    (v : H1Function (euclideanBall (0 : Vec d) 1))
    (hE : ∀ (y : Vec d) (r s : ℝ), 0 < r → r < s → vecEuclideanNorm y + s < 1 →
      ∫ x in euclideanBall y r, vecNormSq (v.grad x) ≤
        4 * Λ * (volume (euclideanBall y s)).toReal / (s - r) ^ 2)
    (y : Vec d) {r : ℝ} (hr : 0 < r)
    (hsub : euclideanBall y r ⊆ euclideanBall (0 : Vec d) (1 / 2)) :
    integralAverage (euclideanBall y r)
        (fun z => |v.toFun z - integralAverage (euclideanBall y r) v.toFun|) ≤
      Real.sqrt (bmoConst d * Λ) := by
  have hgeom := norm_add_le_of_ball_subset i0 hr (by norm_num) hsub
  have hy0 := vecEuclideanNorm_nonneg y
  have hr2 : r ≤ 1 / 2 := by linarith
  set V := euclideanBall y r with hV
  have hVconv : IsOpenBoundedConvexDomain V := isOpenBoundedConvexDomain_euclideanBall y hr
  have hVsub : V ⊆ euclideanBall (0 : Vec d) 1 :=
    hsub.trans (euclideanBall_mono (by norm_num) (by norm_num))
  set v' : H1Function V := v.restrict (isOpen_euclideanBall y r) hVsub with hv'
  have hP := centeredPoincare_sq_on_boundedConvexDomain hVconv
    (hasEuclideanDiameterLE_euclideanBall y hr) (by positivity)
    (euclideanBall_nonempty y hr) v'
  have hs : vecEuclideanNorm y + 3 * r / 2 < 1 := by linarith
  have hEn := hE y r (3 * r / 2) hr (by linarith) hs
  have hvolratio : (volume (euclideanBall y (3 * r / 2))).toReal =
      (3 / 2 : ℝ) ^ d * (volume V).toReal := by
    have := volume_euclideanBall_toReal_div_eq_div_pow y y hr (show 0 < 3 * r / 2 by linarith)
    have hVpos := volume_euclideanBall_toReal_pos y hr
    rw [div_eq_iff hVpos.ne'] at this
    rw [this, show 3 * r / 2 / r = 3 / 2 by field_simp]
  have hVpos := volume_euclideanBall_toReal_pos y hr
  have hsq : ∫ x in V, (v'.toFun x - integralAverage V v'.toFun) ^ 2 ≤
      (Real.sqrt (bmoConst d * Λ)) ^ 2 * (volume V).toReal := by
    rw [Real.sq_sqrt (by have := bmoConst_pos d; positivity)]
    refine hP.trans ?_
    have hEn' : ∫ x in V, vecNormSq (v'.grad x) ≤
        16 * Λ * ((3 / 2 : ℝ) ^ d * (volume V).toReal) / r ^ 2 := by
      have : (3 * r / 2 - r) ^ 2 = r ^ 2 / 4 := by ring
      rw [this, hvolratio] at hEn
      refine hEn.trans (le_of_eq ?_)
      ring
    calc ((2 : ℝ) ^ d * (2 * r)) ^ 2 * ∫ x in V, vecNormSq (v'.grad x)
        ≤ ((2 : ℝ) ^ d * (2 * r)) ^ 2 *
            (16 * Λ * ((3 / 2 : ℝ) ^ d * (volume V).toReal) / r ^ 2) :=
          mul_le_mul_of_nonneg_left hEn' (by positivity)
      _ = bmoConst d * Λ * (volume V).toReal := by
          have h4 : (4 : ℝ) ^ d = ((2 : ℝ) ^ d) ^ 2 := by
            rw [← pow_mul, mul_comm, pow_mul]; norm_num
          unfold bmoConst
          rw [show (4 : ℝ) ^ (d + 1) = ((2 : ℝ) ^ d) ^ 2 * 4 by rw [pow_succ, h4]]
          field_simp
          ring
  have : IsFiniteMeasure (volumeOn V) := hVconv.isFiniteMeasure_volumeOn
  have hmem : MemLp (fun x => v'.toFun x - integralAverage V v'.toFun) 2 (volume.restrict V) :=
    v'.memL2.sub (memLp_const _)
  exact integralAverage_abs_le_of_sq_le
    (ENNReal.toReal_pos_iff.mp hVpos |>.1 |> fun h => h) 
    (ENNReal.toReal_pos_iff.mp hVpos |>.2) hmem (Real.sqrt_nonneg _) hsq

end PDE.DGNMLog
