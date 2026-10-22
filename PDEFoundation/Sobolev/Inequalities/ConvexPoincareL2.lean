module

public import PDEFoundation.Sobolev.Inequalities.ConvexPoincare
public import PDEFoundation.Sobolev.H1.Mean
public import PDEFoundation.Sobolev.H1.Pairing

/-!
# Squared-integral `L²` Poincaré estimates

This module specializes the sharp-in-`p` convex-domain Poincaré theorem to
`H¹` and converts its extended `L²` norms into literal real integrals. The
resulting form is convenient for energy estimates and finite-cover gluing.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

/-- Squared-integral centered Poincaré on a bounded open convex domain. -/
theorem centeredPoincare_sq_on_boundedConvexDomain
    {d : ℕ} {V : Set (Vec d)} {D : ℝ}
    (hV : IsOpenBoundedConvexDomain V)
    (hVDiameter : HasEuclideanDiameterLE V D)
    (hD : 0 ≤ D) (hVNonempty : V.Nonempty)
    (v : H1Function V) :
    ∫ x in V, (v x - integralAverage V v) ^ 2 ≤
      ((2 : ℝ) ^ d * D) ^ 2 *
        ∫ x in V, vecNormSq (v.grad x) := by
  let : IsFiniteMeasure (volumeOn V) :=
    hV.isFiniteMeasure_volumeOn
  let w : H1Function V := v.subAverage
  have hwMean : MeanZeroOn V w.toFun :=
    v.meanZeroOn_subAverage
      (hV.volume_pos hVNonempty) hV.volume_lt_top
  let w' : W1pFunction V (ENNReal.ofReal (2 : ℝ)) := {
    toFun := w.toFun
    grad := w.grad
    memLp := by
      simpa only [ENNReal.ofReal_ofNat] using w.memL2
    gradMemLp := by
      intro i
      simpa only [ENNReal.ofReal_ofNat] using w.gradMemL2 i
    hasWeakGradient := w.hasWeakGradient }
  have hPoincareRaw :=
    meanZeroPoincare_on_boundedConvexDomain_unnormalized
      (p := (2 : ℝ)) (by norm_num) hV hVDiameter hD
      (hV.volume_pos hVNonempty) hV.volume_lt_top w'
      (show MeanZeroOn V w'.toFun from hwMean)
  have hPoincare :
      eLpNormOn V (2 : ℝ≥0∞) w.toFun ≤
        ENNReal.ofReal ((2 : ℝ) ^ d * D) *
          euclideanFieldELpNormOn V (2 : ℝ≥0∞) w.grad := by
    simpa only [w', ENNReal.ofReal_ofNat] using hPoincareRaw
  let C : ℝ := (2 : ℝ) ^ d * D
  have hC : 0 ≤ C :=
    mul_nonneg (by positivity) hD
  have hPoincareReal :
      (eLpNormOn V (2 : ℝ≥0∞) w.toFun).toReal ≤
        C * (euclideanFieldELpNormOn
          V (2 : ℝ≥0∞) w.grad).toReal := by
    have h :=
      ENNReal.toReal_mono
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          w.gradMemL2.memLp_vecEuclideanNorm.eLpNorm_ne_top)
        hPoincare
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] at h
    exact h
  have hSq :
      (eLpNormOn V (2 : ℝ≥0∞) w.toFun).toReal ^ 2 ≤
        (C * (euclideanFieldELpNormOn
          V (2 : ℝ≥0∞) w.grad).toReal) ^ 2 :=
    (sq_le_sq₀ ENNReal.toReal_nonneg
      (mul_nonneg hC ENNReal.toReal_nonneg)).2 hPoincareReal
  have hValue :
      (eLpNormOn V (2 : ℝ≥0∞) w.toFun).toReal ^ 2 =
        ∫ x in V, w x ^ 2 := by
    simpa only [eLpNormOn, volumeOn] using
      toReal_eLpNorm_two_sq_eq_integral_sq w.memL2
  have hGradient :
      (euclideanFieldELpNormOn
          V (2 : ℝ≥0∞) w.grad).toReal ^ 2 =
        ∫ x in V, vecNormSq (w.grad x) := by
    simpa only [euclideanFieldELpNormOn, eLpNormOn, volumeOn,
      vecEuclideanNorm_sq] using
      toReal_eLpNorm_two_sq_eq_integral_sq
        w.gradMemL2.memLp_vecEuclideanNorm
  rw [hValue, mul_pow, hGradient] at hSq
  simpa only [C, w, H1Function.subAverage_apply,
    H1Function.grad_subAverage] using hSq

/-- Squared-integral centered Poincaré after restricting an `H¹` function
to a bounded open convex subdomain. -/
theorem centeredPoincare_sq_on_boundedConvexSubdomain
    {d : ℕ} {U V : Set (Vec d)} {D : ℝ}
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V)
    (hVU : V ⊆ U)
    (hVDiameter : HasEuclideanDiameterLE V D)
    (hD : 0 ≤ D) (hVNonempty : V.Nonempty) :
    ∫ x in V, (u x - integralAverage V u) ^ 2 ≤
      ((2 : ℝ) ^ d * D) ^ 2 *
        ∫ x in V, vecNormSq (u.grad x) := by
  let v : H1Function V :=
    (u.toW1pFunction.restrict hV.isOpen hVU).toH1Function
  have hbase :=
    centeredPoincare_sq_on_boundedConvexDomain
      hV hVDiameter hD hVNonempty v
  simpa only [v, W1pFunction.toH1Function_apply,
    W1pFunction.toH1Function_grad] using! hbase

end PDE
