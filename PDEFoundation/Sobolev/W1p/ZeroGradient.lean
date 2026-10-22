module

public import PDEFoundation.Sobolev.Inequalities.ConvexPoincare
public import PDEFoundation.Sobolev.W1p.Mean

/-!
# Rigidity of a vanishing weak gradient

The finite-exponent convex Poincaré theorem includes `p = 1`. Consequently,
a representative with almost everywhere zero selected weak gradient is almost
everywhere equal to its integral average, without an `L²` hypothesis.
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

namespace W1pFunction

/-- Quantitative convex Poincaré implies rigidity at every finite real
exponent, including one. The gradient only needs to vanish almost everywhere. -/
theorem ae_eq_integralAverage_of_grad_ae_eq_zero_of_diameter
    {d : ℕ} {p : ℝ} (hp : 1 ≤ p) {U : Set (Vec d)} {D : ℝ}
    (hU : IsOpenBoundedConvexDomain U) (hUDiameter : HasEuclideanDiameterLE U D)
    (hD : 0 ≤ D) (hUPos : 0 < volume U) (hUTop : volume U < ∞)
    (u : W1pFunction U (ENNReal.ofReal p))
    (hgrad : u.grad =ᵐ[volumeOn U] 0) :
    u.toFun =ᵐ[volumeOn U] fun _ => integralAverage U u.toFun := by
  have hpENN : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp
  let : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal p) := ⟨hpENN⟩
  let : IsFiniteMeasure (volumeOn U) := hU.isFiniteMeasure_volumeOn
  have hP := meanZeroPoincare_on_boundedConvexDomain_unnormalized hp
    hU hUDiameter hD hUPos hUTop u.subAverage (u.meanZeroOn_subAverage hUPos hUTop)
  have hgradient : (fun x => vecEuclideanNorm (u.subAverage.grad x)) =ᵐ[volumeOn U] 0 := by
    filter_upwards [hgrad] with x hx
    simp [subAverage_grad, hx, vecEuclideanNorm, vecNormSq, vecDot]
  have hgnorm : euclideanFieldELpNormOn U (ENNReal.ofReal p) u.subAverage.grad = 0 := by
    unfold euclideanFieldELpNormOn eLpNormOn
    rw [eLpNorm_congr_ae hgradient, eLpNorm_zero]
  have hzero : eLpNorm u.subAverage.toFun (ENNReal.ofReal p) (volumeOn U) = 0 := by
    exact le_antisymm (by simpa only [hgnorm, mul_zero, eLpNormOn] using hP) bot_le
  have hcenter := (eLpNorm_eq_zero_iff
    (ne_of_gt (lt_of_lt_of_le zero_lt_one hpENN))).mp hzero
  filter_upwards [hcenter] with x hx
  simpa only [subAverage_apply, Pi.zero_apply, sub_eq_zero] using hx

/-- On a bounded open convex domain, a finite-exponent Sobolev representative
with almost everywhere zero weak gradient equals its integral average almost
everywhere. No diameter needs to be supplied to this qualitative conclusion. -/
theorem ae_eq_integralAverage_of_grad_ae_eq_zero
    {d : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (hUPos : 0 < volume U) (hUTop : volume U < ∞)
    (u : W1pFunction U p) (hgrad : u.grad =ᵐ[volumeOn U] 0) :
    u.toFun =ᵐ[volumeOn U] fun _ => integralAverage U u.toFun := by
  obtain ⟨M, hM, hbound⟩ := hU.isBoundedDomain
  have hdiam : HasEuclideanDiameterLE U (Real.sqrt d * (2 * M)) := by
    intro x hx y hy
    have hnorm : ‖x - y‖ ≤ 2 * M := by
      apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
      intro i
      simpa only [Pi.sub_apply, Real.norm_eq_abs, two_mul] using
        (abs_sub (x i) (y i)).trans (add_le_add (hbound x hx i) (hbound y hy i))
    exact (vecEuclideanNorm_le_sqrt_natCast_mul_norm (x - y)).trans
      (mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg _))
  have hpReal : 1 ≤ p.toReal := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_le_toReal (by norm_num : (1 : ℝ≥0∞) ≠ ∞) hpTop).mpr hp
  revert u
  rw [← ENNReal.ofReal_toReal hpTop]
  intro u hgrad
  exact ae_eq_integralAverage_of_grad_ae_eq_zero_of_diameter hpReal hU hdiam
    (by positivity) hUPos hUTop u hgrad

end W1pFunction

end PDE
