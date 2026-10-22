module

public import PDEFoundation.Sobolev.OneDimensional.ContinuousWeakIncrement
public import PDEFoundation.Sobolev.OneDimensional.PrimitiveWeakIdentity

/-!
# Zero extension of one-dimensional weak representatives

This module supplies the analytic integration-by-parts kernel for extending a
continuous one-dimensional weak representative by zero.  The endpoint values
are actual values of the continuous representative, not merely trace labels:
they cancel the boundary term exactly.

The conclusion is deliberately stated as the scalar distributional identity.
It is the exact representative-level statement needed before transporting the
construction through the native one-coordinate equivalence to a higher-
dimensional zero-extension theorem.
-/

@[expose] public section

namespace PDE

open MeasureTheory Set

noncomputable section

/-- Integration by parts for a left-based interval primitive whose total
increment vanishes.  Unlike the compact-test-function version, the test
function need not vanish at either endpoint: the zero total increment removes
the resulting boundary term. -/
theorem intervalPrimitive_scalar_weak_identity_Icc_of_zero_total
    {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ}
    (hg : IntegrableOn g (Icc a b) volume)
    (hzero : intervalPrimitive a g b = 0)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) :
    ∫ x in Icc a b, intervalPrimitive a g x * deriv φ x =
      -∫ x in Icc a b, g x * φ x := by
  have htail : ∀ y ∈ Icc a b,
      ∫ x in Icc y b, deriv φ x = φ b - φ y := by
    intro y hy
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hy.2,
      intervalIntegral.integral_deriv_of_contDiffOn_Icc hφ.contDiffOn hy.2]
  rw [show (∫ x in Icc a b, intervalPrimitive a g x * deriv φ x) =
      ∫ x in Icc a b, ∫ y in Icc a x, g y * deriv φ x by
        apply setIntegral_congr_fun measurableSet_Icc
        intro x hx
        change intervalPrimitive a g x * deriv φ x =
          (∫ y in Icc a x, g y * deriv φ x)
        rw [intervalPrimitive_eq_setIntegral_Icc hx.1]
        rw [integral_mul_const],
    setIntegral_setIntegral_Icc_swap hg
      (hφ.continuous_deriv (by simp)).continuousOn]
  rw [show (∫ y in Icc a b, ∫ x in Icc y b, g y * deriv φ x) =
      ∫ y in Icc a b, g y * (φ b - φ y) by
        apply setIntegral_congr_fun measurableSet_Icc
        intro y hy
        change (∫ x in Icc y b, g y * deriv φ x) =
          g y * (φ b - φ y)
        rw [integral_const_mul, htail y hy]]
  have hgφ : IntegrableOn (fun y => g y * φ y) (Icc a b) volume := by
    exact hg.mul_continuousOn hφ.continuous.continuousOn isCompact_Icc
  have hgConst : IntegrableOn (fun y => g y * φ b) (Icc a b) volume :=
    hg.mul_const _
  have htotal : ∫ y in Icc a b, g y = 0 := by
    rw [← intervalPrimitive_eq_setIntegral_Icc hab]
    exact hzero
  calc
    ∫ y in Icc a b, g y * (φ b - φ y) =
        ∫ y in Icc a b, (g y * φ b - g y * φ y) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro y _
      ring
    _ = (∫ y in Icc a b, g y * φ b) - ∫ y in Icc a b, g y * φ y := by
      rw [integral_sub hgConst hgφ]
    _ = (∫ y in Icc a b, g y) * φ b - ∫ y in Icc a b, g y * φ y := by
      rw [integral_mul_const]
    _ = -∫ y in Icc a b, g y * φ y := by
      rw [htotal, zero_mul, zero_sub]

/-- If a continuous `H¹` representative vanishes at both endpoints, its open
interval zero extension has the global scalar weak-derivative identity.  The
two displayed indicators are genuine zero extensions; no boundary measure is
hidden in the conclusion. -/
theorem indicator_zero_extension_scalar_weak_identity
    {a b : ℝ} (hab : a < b) {v g : ℝ → ℝ}
    (hv : ContinuousOn v (Icc a b))
    (hvLp : MemLp v 2 (volume.restrict (Ioo a b)))
    (hg : MemLp g 2 (volume.restrict (Icc a b)))
    (hweak : HasWeakDerivOnIoo a b v g)
    (hva : v a = 0) (hvb : v b = 0)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) :
    ∫ x, (Ioo a b).indicator v x * deriv φ x =
      -∫ x, (Ioo a b).indicator g x * φ x := by
  have hgIntegrable : IntegrableOn g (Icc a b) volume := by
    simpa only [IntegrableOn] using hg.integrable (by norm_num)
  have hzero : intervalPrimitive a g b = 0 := by
    have hIncrement :=
      ContinuousOn.increment_eq_intervalIntegral_of_hasWeakDerivOnIoo
        hab hv hvLp hg hweak (s := a) (t := b)
        ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩
    simpa only [hva, hvb, sub_self, intervalPrimitive] using hIncrement.symm
  have hvPrimitive : ∀ x ∈ Icc a b, v x = intervalPrimitive a g x := by
    intro x hx
    have hIncrement :=
      ContinuousOn.increment_eq_intervalIntegral_of_hasWeakDerivOnIoo
        hab hv hvLp hg hweak (s := a) (t := x)
        ⟨le_rfl, hab.le⟩ hx
    simpa only [hva, sub_zero, intervalPrimitive] using hIncrement
  have hIcc :
      ∫ x in Icc a b, v x * deriv φ x =
        -∫ x in Icc a b, g x * φ x := by
    calc
      ∫ x in Icc a b, v x * deriv φ x =
          ∫ x in Icc a b, intervalPrimitive a g x * deriv φ x := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro x hx
        change v x * deriv φ x = intervalPrimitive a g x * deriv φ x
        rw [hvPrimitive x hx]
      _ = -∫ x in Icc a b, g x * φ x :=
        intervalPrimitive_scalar_weak_identity_Icc_of_zero_total
          hab.le hgIntegrable hzero hφ
  have hIoo :
      ∫ x in Ioo a b, v x * deriv φ x =
        -∫ x in Ioo a b, g x * φ x := by
    simpa only [restrict_Ioo_eq_restrict_Icc] using hIcc
  have hleft :
      (fun x => (Ioo a b).indicator v x * deriv φ x) =
        (Ioo a b).indicator (fun x => v x * deriv φ x) := by
    funext x
    by_cases hx : x ∈ Ioo a b <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  have hright :
      (fun x => (Ioo a b).indicator g x * φ x) =
        (Ioo a b).indicator (fun x => g x * φ x) := by
    funext x
    by_cases hx : x ∈ Ioo a b <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  rw [hleft, hright, integral_indicator measurableSet_Ioo,
    integral_indicator measurableSet_Ioo]
  exact hIoo

end

end PDE
