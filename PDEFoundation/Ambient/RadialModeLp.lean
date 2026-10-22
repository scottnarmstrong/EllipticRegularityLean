module

public import PDEFoundation.Ambient.RadialModeBounds
public import PDEFoundation.Measure.EuclideanRadialPowerLp
public import Mathlib.Tactic.FunProp

@[expose] public section

namespace PDE

open MeasureTheory Set
open scoped ENNReal Topology
noncomputable section

private theorem measurable_radialModePowerField {d : ℕ}
    (k : Fin d) (β : ℝ) : Measurable (radialModePowerField k β) := by
  apply measurable_of_continuousOn_compl_singleton 0
  intro x hx
  have hx0 : x ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hx
  have hnorm : 0 < vecEuclideanNorm x := vecEuclideanNorm_pos_iff.mpr hx0
  have hsq : vecNormSq x ≠ 0 := fun h => hx0 (vecNormSq_eq_zero h)
  apply ContinuousAt.continuousWithinAt
  have hr : ContinuousAt (fun y : Vec d =>
      Real.rpow (vecEuclideanNorm y) (β - 1)) x :=
    continuous_vecEuclideanNorm.continuousAt.rpow_const (Or.inl hnorm.ne')
  have hcoord : ContinuousAt (fun y : Vec d => y k) x :=
    (continuous_apply k).continuousAt
  have hden : ContinuousAt (fun y : Vec d => vecNormSq y) x := by
    unfold vecNormSq vecDot
    fun_prop
  have hdiv : ContinuousAt (fun y : Vec d => y k / vecNormSq y) x :=
    hcoord.div hden hsq
  have hcoef : ContinuousAt (fun y : Vec d =>
      (β - 1) * (y k / vecNormSq y)) x := continuousAt_const.mul hdiv
  have hV : ContinuousAt (fun y : Vec d =>
      basisVec k + ((β - 1) * (y k / vecNormSq y)) • y) x :=
    continuousAt_const.add (hcoef.smul continuousAt_id)
  exact hr.smul hV

private theorem measurable_norm_radialModePowerField {d : ℕ}
    (k : Fin d) (β : ℝ) :
    Measurable (fun x => vecEuclideanNorm (radialModePowerField k β x)) :=
  measurable_vecEuclideanNorm.comp (measurable_radialModePowerField k β)

/-- The coordinate radial power mode has exactly the radial-power `Lᵖ`
threshold on every positive-radius native round ball. -/
theorem memLp_vecEuclideanNorm_radialModePowerField_euclideanBall_iff
    {d : ℕ} (hd : 0 < d) (k : Fin d) {β R p : ℝ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hR : 0 < R) (hp : 0 < p) :
    MemLp (fun x : Vec d =>
        vecEuclideanNorm (radialModePowerField k β x))
      (ENNReal.ofReal p) (volume.restrict (euclideanBall 0 R)) ↔
      -(d : ℝ) < (β - 1) * p := by
  let μ := volume.restrict (euclideanBall (0 : Vec d) R)
  let g : Vec d → ℝ := fun x =>
    vecEuclideanNorm (radialModePowerField k β x)
  let h : Vec d → ℝ := fun x => vecEuclideanNorm x ^ (β - 1)
  have hgAES : AEStronglyMeasurable g μ :=
    (measurable_norm_radialModePowerField k β).aestronglyMeasurable
  have hhMeas : Measurable h := by
    apply measurable_of_continuousOn_compl_singleton 0
    intro x hx
    have hx0 : x ≠ 0 := by
      simpa only [mem_compl_iff, mem_singleton_iff] using hx
    have hnorm : 0 < vecEuclideanNorm x := vecEuclideanNorm_pos_iff.mpr hx0
    exact (continuous_vecEuclideanNorm.continuousAt.rpow_const
      (Or.inl hnorm.ne')).continuousWithinAt
  have hhAES : AEStronglyMeasurable h μ := hhMeas.aestronglyMeasurable
  have hbounds : ∀ x, β * h x ≤ g x ∧ g x ≤ h x := by
    intro x
    exact radialModePowerField_norm_bounds k hβ0 hβ1 x
  rw [← memLp_vecEuclideanNorm_rpow_euclideanBall_iff hd hR hp]
  constructor
  · intro hg
    have hscaled : MemLp (fun x => β⁻¹ * g x) (ENNReal.ofReal p) μ :=
      hg.const_mul β⁻¹
    apply hscaled.mono hhAES
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (vecEuclideanNorm_nonneg x) (β - 1)),
      Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr hβ0.le)
        (vecEuclideanNorm_nonneg _))]
    have hl := (hbounds x).1
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ hβ0).mpr (by simpa only [mul_comm] using hl)
  · intro hh
    apply hh.mono hgAES
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (vecEuclideanNorm_nonneg _),
      Real.norm_of_nonneg (Real.rpow_nonneg (vecEuclideanNorm_nonneg x) (β - 1))]
    exact (hbounds x).2

end

end PDE
