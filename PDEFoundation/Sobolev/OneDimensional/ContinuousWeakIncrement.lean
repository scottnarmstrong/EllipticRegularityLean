module

public import PDEFoundation.Sobolev.OneDimensional.WeakPrimitiveRepresentation

/-!
# Increment formula for continuous one-dimensional weak representatives

An `H¹` function on an interval has a continuous representative.  This module
records the complementary uniqueness statement needed by the trace API: once
a continuous representative has already been supplied, its weak derivative
determines its actual pointwise increments, including both endpoints.

The endpoint conclusion is not an almost-everywhere convention.  It follows
by upgrading the primitive representation from `Ioo a b` to `Icc a b` using
continuity and the fact that the two endpoints are volume-null.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory Set

noncomputable section

/-- A continuous representative on a nondegenerate closed interval with weak
derivative `g` has the exact interval-integral increment formula. -/
theorem ContinuousOn.increment_eq_intervalIntegral_of_hasWeakDerivOnIoo
    {a b : ℝ} (hab : a < b) {v g : ℝ → ℝ}
    (hv : ContinuousOn v (Icc a b))
    (hvLp : MemLp v 2 (volume.restrict (Ioo a b)))
    (hg : MemLp g 2 (volume.restrict (Icc a b)))
    (hweak : HasWeakDerivOnIoo a b v g)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    v t - v s = ∫ x in s..t, g x := by
  rcases ae_eq_intervalPrimitive_add_const_of_hasWeakDerivOnIoo
      hab hvLp hg hweak with ⟨c, hvc⟩
  let p : ℝ → ℝ := fun x => intervalPrimitive a g x + c
  have hgIntegrable : IntegrableOn g (Icc a b) volume := by
    simpa only [IntegrableOn] using hg.integrable (by norm_num)
  have hp : ContinuousOn p (Icc a b) := by
    exact (continuousOn_intervalPrimitive hab.le hgIntegrable).add continuousOn_const
  have hvcIcc : v =ᵐ[volume.restrict (Icc a b)] p := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact hvc
  have hEq : EqOn v p (Icc a b) :=
    Measure.eqOn_Icc_of_ae_eq volume hab.ne hvcIcc hv hp
  calc
    v t - v s = p t - p s := by rw [hEq ht, hEq hs]
    _ = intervalPrimitive a g t - intervalPrimitive a g s := by
      dsimp only [p]
      ring
    _ = ∫ x in s..t, g x :=
      intervalPrimitive_sub_eq_intervalIntegral hgIntegrable hs ht

/-- The continuous representative increment estimate has constant one and
the exact `L²` scaling on every ordered subinterval. -/
theorem ContinuousOn.sq_abs_increment_le_of_hasWeakDerivOnIoo
    {a b : ℝ} (hab : a < b) {v g : ℝ → ℝ}
    (hv : ContinuousOn v (Icc a b))
    (hvLp : MemLp v 2 (volume.restrict (Ioo a b)))
    (hg : MemLp g 2 (volume.restrict (Icc a b)))
    (hweak : HasWeakDerivOnIoo a b v g)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    |v t - v s| ^ 2 ≤
      (t - s) * ∫ x in Icc s t, |g x| ^ (2 : ℝ) := by
  have hgIntegrable : IntegrableOn g (Icc a b) volume := by
    simpa only [IntegrableOn] using hg.integrable (by norm_num)
  have hgLocal : MemLp g 2 (volume.restrict (Icc s t)) :=
    hg.mono_measure
      (Measure.restrict_mono (Icc_subset_Icc hs.1 ht.2) le_rfl)
  rw [ContinuousOn.increment_eq_intervalIntegral_of_hasWeakDerivOnIoo
    hab hv hvLp hg hweak hs ht]
  simpa only [intervalPrimitive_sub_eq_intervalIntegral hgIntegrable hs ht] using
    sq_abs_intervalPrimitive_sub_le_l2 hgIntegrable hs ht hst hgLocal

end

end PDE
