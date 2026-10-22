module

public import PDEFoundation.Sobolev.Inequalities.SobolevPoincare
public import PDEFoundation.Sobolev.Inequalities.ConvexPoincareL2
public import PDEFoundation.Measure.BallVolume
public import SobolevStatements.ConvexSobolevPoincare
public import EllipticRegularity.DeGiorgi.LogPackage.SmallSupport

/-!
# Unnormalized Sobolev-Poincare inequality on balls with exponent `p = 2`
-/

@[expose] public section

namespace PDE.DGNMLog

open MeasureTheory

/-- Centered Sobolev-Poincare on `B_ρ ⊆ B_1`, `p = 2`, unnormalized, from the proved
convex Sobolev-Poincare inequality (Theorem 1.9). -/
theorem sobolevPoincare_two_ball {d : ℕ} (hd : 3 ≤ d) :
    ∃ K : ℝ, 0 < K ∧ ∀ {ρ : ℝ}, 0 < ρ → ρ ≤ 1 →
      ∀ w : H1Function (euclideanBall (0 : Vec d) 1),
        eLpNormOn (euclideanBall (0 : Vec d) ρ) (ENNReal.ofReal (sobolevConjugate d 2))
            (fun x => w.toFun x - integralAverage (euclideanBall (0 : Vec d) ρ) w.toFun) ≤
          ENNReal.ofReal K * volume (euclideanBall (0 : Vec d) ρ) ^ (-(1 / (d : ℝ))) *
            euclideanFieldELpNormOn (euclideanBall (0 : Vec d) ρ) 2 w.grad := by
  have hd2 : 2 ≤ d := by omega
  obtain ⟨C, hC, hSP⟩ := PDE.exists_convexSobolevPoincare_constant d hd2
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨C * (2 * ((d : ℝ) - 1) / ((d : ℝ) - 2)) * 2, by
    have : 0 < (d : ℝ) - 2 := by linarith
    have : 0 < (d : ℝ) - 1 := by linarith
    positivity, ?_⟩
  intro ρ hρ hρ1 w
  set V := euclideanBall (0 : Vec d) ρ with hV
  have hVsub : V ⊆ euclideanBall (0 : Vec d) 1 := euclideanBall_mono hρ.le hρ1
  have hVpos : 0 < volume V := volume_euclideanBall_pos _ hρ
  have hVfin : volume V < ⊤ := (volume_euclideanBall_ne_top _ hρ.le).lt_top
  set wr : H1Function V := w.restrict (isOpen_euclideanBall 0 ρ) hVsub with hwr
  set u : W1pFunction V (ENNReal.ofReal 2) :=
    { toFun := w.toFun
      grad := w.grad
      memLp := by
        have h := wr.memL2
        rw [ENNReal.ofReal_ofNat]
        exact h
      gradMemLp := by
        intro i
        have h := wr.gradMemL2 i
        rw [ENNReal.ofReal_ofNat]
        exact h
      hasWeakGradient := wr.hasWeakGradient } with hu
  have hN := hSP 2 (by norm_num) (by exact_mod_cast (by omega : 2 < d)) V (2 * ρ)
    (isOpenBoundedConvexDomain_euclideanBall 0 hρ)
    ⟨0, center_mem_euclideanBall 0 hρ⟩ (hasEuclideanDiameterLE_euclideanBall 0 hρ) u
  have hp : (0 : ℝ) < 2 := by norm_num
  have hpd : (2 : ℝ) < d := by linarith
  rw [eLpNormOn_eq_volume_rpow_mul_eLpMeanNormOn hVpos hVfin,
    euclideanFieldELpNormOn_eq_volume_rpow_mul hVpos hVfin]
  have hexp := toReal_one_div_ofReal_sobolevConjugate hp hpd
  have hle : ENNReal.ofReal (C * (2 * ((d : ℝ) - 1) / ((d : ℝ) - 2)) * (2 * ρ)) ≤
      ENNReal.ofReal (C * (2 * ((d : ℝ) - 1) / ((d : ℝ) - 2)) * 2) := by
    apply ENNReal.ofReal_le_ofReal
    have : 0 < C * (2 * ((d : ℝ) - 1) / ((d : ℝ) - 2)) := by
      have : 0 < (d : ℝ) - 2 := by linarith
      have : 0 < (d : ℝ) - 1 := by linarith
      positivity
    nlinarith
  calc volume V ^ (1 / ENNReal.ofReal (sobolevConjugate d 2)).toReal *
        eLpMeanNormOn V (ENNReal.ofReal (sobolevConjugate d 2))
          (fun x => w.toFun x - integralAverage V w.toFun)
      ≤ volume V ^ (1 / ENNReal.ofReal (sobolevConjugate d 2)).toReal *
          (ENNReal.ofReal (C * (2 * ((d : ℝ) - 1) / ((d : ℝ) - 2)) * 2) *
            euclideanFieldELpMeanNormOn V (ENNReal.ofReal 2) w.grad) := by
        gcongr
        refine hN.trans ?_
        gcongr
    _ = ENNReal.ofReal (C * (2 * ((d : ℝ) - 1) / ((d : ℝ) - 2)) * 2) *
          volume V ^ (-(1 / (d : ℝ))) *
          (volume V ^ (1 / (2 : ENNReal)).toReal *
            euclideanFieldELpMeanNormOn V 2 w.grad) := by
        rw [hexp, ENNReal.rpow_add _ _ hVpos.ne' hVfin.ne]
        simp only [ENNReal.ofReal_ofNat, one_div]
        ac_rfl

end PDE.DGNMLog
