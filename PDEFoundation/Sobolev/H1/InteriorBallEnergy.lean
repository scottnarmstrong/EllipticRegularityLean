module

public import PDEFoundation.Geometry.EuclideanBall.Interior
public import PDEFoundation.Sobolev.H1.MeanEnergy

/-! # Interior ball energy restriction

Exact volume scaling gives the dimensionally scaled loss when normalized
Euclidean vector energy is restricted from the unit ball to an interior ball.
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The square-root volume ratio between the unit ball and a radius `r` ball. -/
theorem sqrt_volume_unitBall_div_euclideanBall_eq_rpow_neg_half_dim
    {d : ℕ} (z : Vec d) {r : ℝ} (hr : 0 < r) :
    Real.sqrt (volume (euclideanBall (0 : Vec d) 1)).toReal /
        Real.sqrt (volume (euclideanBall z r)).toReal =
      r ^ (-(d : ℝ) / 2) := by
  rw [← Real.sqrt_div ENNReal.toReal_nonneg,
    volume_euclideanBall_toReal_div_eq_div_pow (0 : Vec d) z hr (by norm_num)]
  rw [Real.sqrt_eq_rpow]
  rw [one_div]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (inv_nonneg.mpr hr.le)]
  have hexp : -(d : ℝ) / 2 = -((d : ℝ) / 2) := by ring
  rw [hexp, Real.rpow_neg_eq_inv_rpow]
  congr 1
  ring

/-- Normalized Euclidean vector energy on an interior radius `r` ball is
controlled by unit-ball energy with the scaling factor `r⁻ᵈᐟ²`. -/
theorem sqrt_integralAverage_vecNormSq_interiorBall_le
    {d : ℕ} {z : Vec d} {r : ℝ}
    (hz : z ∈ euclideanBall (0 : Vec d) (1 / 2))
    (hr : 0 < r) (hrle : r ≤ 1 / 2)
    {g : Vec d → Vec d}
    (hg : MemVectorL2On (euclideanBall (0 : Vec d) 1) g) :
    Real.sqrt (integralAverage (euclideanBall z r)
        (fun x => vecNormSq (g x))) ≤
      r ^ (-(d : ℝ) / 2) *
        Real.sqrt (integralAverage (euclideanBall (0 : Vec d) 1)
          (fun x => vecNormSq (g x))) := by
  have hsub : euclideanBall z r ⊆ euclideanBall (0 : Vec d) 1 :=
    (euclideanBall_mono hr.le hrle).trans
      (euclideanBall_half_subset_unit_of_center_mem_half hz)
  have h := sqrt_integralAverage_vecNormSq_mono_set hsub
    (volume_euclideanBall_toReal_pos (0 : Vec d) (by norm_num)) hg
  rw [sqrt_volume_unitBall_div_euclideanBall_eq_rpow_neg_half_dim z hr] at h
  exact h

end

end PDE
