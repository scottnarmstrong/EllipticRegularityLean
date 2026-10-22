module

public import PDEFoundation.Analysis.RadialModeSmooth
public import PDEFoundation.Measure.EuclideanRadialPowerLp

/-! # Integrability of coordinate radial mode values -/

@[expose] public section

namespace PDE

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- A coordinate radial mode with positive homogeneity belongs to every finite
positive real `Lᵖ` on a positive-radius native round ball. -/
theorem memLp_coordinate_mul_vecEuclideanNorm_rpow_euclideanBall
    {d : ℕ} (hd : 0 < d) (k : Fin d) {beta R p : ℝ}
    (hbeta : 0 < beta) (hR : 0 < R) (hp : 0 < p) :
    MemLp
      (fun x : Vec d => x k * Real.rpow (vecEuclideanNorm x) (beta - 1))
      (ENNReal.ofReal p) (volume.restrict (euclideanBall 0 R)) := by
  let mu := volume.restrict (euclideanBall (0 : Vec d) R)
  let f : Vec d → ℝ := fun x =>
    x k * Real.rpow (vecEuclideanNorm x) (beta - 1)
  let g : Vec d → ℝ := fun x => Real.rpow (vecEuclideanNorm x) beta
  have hfMeas : Measurable f := by
    apply measurable_of_continuousOn_compl_singleton 0
    exact (contDiffOn_coordinate_mul_vecEuclideanNorm_rpow k beta).continuousOn
  have hg : MemLp g (ENNReal.ofReal p) mu :=
    (memLp_vecEuclideanNorm_rpow_euclideanBall_iff hd hR hp).2 (by
      have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
      have hbp : 0 < beta * p := mul_pos hbeta hp
      linarith)
  apply hg.mono hfMeas.aestronglyMeasurable
  filter_upwards [] with x
  change ‖x k * Real.rpow (vecEuclideanNorm x) (beta - 1)‖ ≤
    ‖Real.rpow (vecEuclideanNorm x) beta‖
  simp only [Real.rpow_eq_pow]
  rw [norm_mul]
  simp only [Real.norm_eq_abs]
  have hpowNonneg : 0 ≤ vecEuclideanNorm x ^ (beta - 1) :=
    Real.rpow_nonneg (vecEuclideanNorm_nonneg x) (beta - 1)
  have hbetaNonneg : 0 ≤ vecEuclideanNorm x ^ beta :=
    Real.rpow_nonneg (vecEuclideanNorm_nonneg x) beta
  rw [abs_of_nonneg hpowNonneg, abs_of_nonneg hbetaNonneg]
  by_cases hx : x = 0
  · subst x
    simpa using hbetaNonneg
  · have hr : 0 < vecEuclideanNorm x := vecEuclideanNorm_pos_iff.mpr hx
    calc
      |x k| * (vecEuclideanNorm x ^ (beta - 1)) ≤
          vecEuclideanNorm x *
            (vecEuclideanNorm x ^ (beta - 1)) := by
        exact mul_le_mul_of_nonneg_right
          (abs_apply_le_vecEuclideanNorm x k)
          (Real.rpow_nonneg hr.le (beta - 1))
      _ = vecEuclideanNorm x ^ beta := by
        calc
          vecEuclideanNorm x * (vecEuclideanNorm x ^ (beta - 1)) =
              vecEuclideanNorm x ^ (1 : ℝ) *
                vecEuclideanNorm x ^ (beta - 1) := by
            rw [Real.rpow_one]
          _ = vecEuclideanNorm x ^ (1 + (beta - 1)) :=
            (Real.rpow_add hr 1 (beta - 1)).symm
          _ = vecEuclideanNorm x ^ beta := by ring_nf

end

end PDE
