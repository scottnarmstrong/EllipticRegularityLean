module

public import PDEFoundation.Sobolev.H1.ZeroGradient
public import PDEFoundation.Sobolev.OneDimensional.OneDimensionalCoordinate
public import PDEFoundation.Sobolev.OneDimensional.WeakPrimitive

/-!
# One-dimensional weak primitive representation

This module packages scalar interval data in the common native
representative-level `H¹` API.  It then applies bounded-convex Poincaré to
show that a function and the left-based primitive of its weak derivative
differ almost everywhere by one constant.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory Set

noncomputable section

/-- Package scalar `L²` data and its scalar weak derivative as a native
one-coordinate `H¹` representative. -/
def h1FunctionOfHasWeakDerivOnIoo
    {a b : ℝ} {u g : ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (Ioo a b)))
    (hg : MemLp g 2 (volume.restrict (Ioo a b)))
    (hweak : HasWeakDerivOnIoo a b u g) :
    H1Function (oneDimensionalAxisBox a b) where
  toFun := liftOneDimensional u
  grad := fun x _ => liftOneDimensional g x
  memL2 :=
    (memLp_two_liftOneDimensional_iff_memLp_two_Ioo a b).2 hu
  gradMemL2 := by
    intro i
    simpa only using
      (memLp_two_liftOneDimensional_iff_memLp_two_Ioo a b).2 hg
  hasWeakGradient := by
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact hweak

@[simp]
theorem h1FunctionOfHasWeakDerivOnIoo_apply
    {a b : ℝ} {u g : ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (Ioo a b)))
    (hg : MemLp g 2 (volume.restrict (Ioo a b)))
    (hweak : HasWeakDerivOnIoo a b u g) (x : Vec 1) :
    h1FunctionOfHasWeakDerivOnIoo hu hg hweak x =
      liftOneDimensional u x :=
  rfl

@[simp]
theorem h1FunctionOfHasWeakDerivOnIoo_grad
    {a b : ℝ} {u g : ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (Ioo a b)))
    (hg : MemLp g 2 (volume.restrict (Ioo a b)))
    (hweak : HasWeakDerivOnIoo a b u g) (x : Vec 1) :
    (h1FunctionOfHasWeakDerivOnIoo hu hg hweak).grad x =
      fun _ => liftOneDimensional g x :=
  rfl

/-- A scalar `H¹` function on a bounded open interval agrees almost
everywhere with the left-based primitive of its weak derivative plus one
constant. -/
theorem ae_eq_intervalPrimitive_add_const_of_hasWeakDerivOnIoo
    {a b : ℝ} (hab : a < b) {u g : ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (Ioo a b)))
    (hg : MemLp g 2 (volume.restrict (Icc a b)))
    (hweak : HasWeakDerivOnIoo a b u g) :
    ∃ c : ℝ,
      u =ᵐ[volume.restrict (Ioo a b)]
        fun t => intervalPrimitive a g t + c := by
  have hgIntegrable : IntegrableOn g (Icc a b) volume := by
    simpa only [IntegrableOn] using hg.integrable (by norm_num)
  have hgOpen : MemLp g 2 (volume.restrict (Ioo a b)) := by
    simpa only [restrict_Ioo_eq_restrict_Icc] using hg
  have hprimitiveClosed :
      MemLp (intervalPrimitive a g) 2
        (volume.restrict (Icc a b)) :=
    memLp_intervalPrimitive_two_on_Icc hab.le hg
  have hprimitiveOpen :
      MemLp (intervalPrimitive a g) 2
        (volume.restrict (Ioo a b)) := by
    simpa only [restrict_Ioo_eq_restrict_Icc] using hprimitiveClosed
  have hprimitiveWeak :
      HasWeakDerivOnIoo a b (intervalPrimitive a g) g :=
    intervalPrimitive_hasWeakDerivOnIoo_of_integrableOn_Icc hgIntegrable
  let uH : H1Function (oneDimensionalAxisBox a b) :=
    h1FunctionOfHasWeakDerivOnIoo hu hgOpen hweak
  let pH : H1Function (oneDimensionalAxisBox a b) :=
    h1FunctionOfHasWeakDerivOnIoo
      hprimitiveOpen hgOpen hprimitiveWeak
  have hU :
      IsOpenBoundedConvexDomain (oneDimensionalAxisBox a b) := by
    exact isOpenBoundedConvexDomain_axisBox
      (fun _ : Fin 1 => a) (fun _ => b)
  have hUNonempty : (oneDimensionalAxisBox a b).Nonempty := by
    exact axisBox_nonempty
      (fun _ : Fin 1 => a) (fun _ => b) (fun _ => hab)
  have hUDiameter :
      HasEuclideanDiameterLE (oneDimensionalAxisBox a b) (b - a) := by
    simpa only [oneDimensionalAxisBox, Nat.cast_one, Real.sqrt_one, one_mul] using
      hasEuclideanDiameterLE_axisBox_of_side_le
        (fun _ : Fin 1 => a) (fun _ => b)
        (sub_nonneg.mpr hab.le) (fun _ => le_rfl)
  have hgrad : uH.grad = pH.grad := by
    rfl
  have hnative :=
    H1Function.ae_eq_add_integralAverage_sub_of_grad_eq
      hU hUDiameter (sub_nonneg.mpr hab.le) hUNonempty uH pH hgrad
  let c : ℝ :=
    integralAverage (oneDimensionalAxisBox a b) (uH - pH).toFun
  refine ⟨c, (aeEq_liftOneDimensional_iff_aeEq_Ioo a b).1 ?_⟩
  filter_upwards [hnative] with x hx
  change u (vecOneCoordinate x) =
    intervalPrimitive a g (vecOneCoordinate x) + c
  simpa only [uH, pH, c,
    h1FunctionOfHasWeakDerivOnIoo_apply] using! hx

/-- The primitive-plus-constant theorem supplies an explicit representative
that is continuous on the closed interval and has the exact fundamental
theorem of calculus increment formula there. -/
theorem exists_continuousOn_representative_of_hasWeakDerivOnIoo
    {a b : ℝ} (hab : a < b) {u g : ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (Ioo a b)))
    (hg : MemLp g 2 (volume.restrict (Icc a b)))
    (hweak : HasWeakDerivOnIoo a b u g) :
    ∃ v : ℝ → ℝ,
      ContinuousOn v (Icc a b) ∧
      u =ᵐ[volume.restrict (Ioo a b)] v ∧
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        v t - v s = ∫ x in s..t, g x := by
  rcases ae_eq_intervalPrimitive_add_const_of_hasWeakDerivOnIoo
      hab hu hg hweak with ⟨c, huc⟩
  have hgIntegrable : IntegrableOn g (Icc a b) volume := by
    simpa only [IntegrableOn] using hg.integrable (by norm_num)
  let v : ℝ → ℝ := fun t => intervalPrimitive a g t + c
  refine ⟨v, ?_, huc, ?_⟩
  · exact
      (continuousOn_intervalPrimitive hab.le hgIntegrable).add
        continuousOn_const
  · intro s hs t ht
    dsimp only [v]
    calc
      intervalPrimitive a g t + c -
          (intervalPrimitive a g s + c) =
          intervalPrimitive a g t - intervalPrimitive a g s := by ring
      _ = ∫ x in s..t, g x :=
        intervalPrimitive_sub_eq_intervalIntegral
          hgIntegrable hs ht

/-- The continuous representative furnished by the one-dimensional Sobolev
theorem satisfies the scale-sharp squared increment estimate with constant
one. -/
theorem exists_continuousOn_representative_with_sq_increment_le
    {a b : ℝ} (hab : a < b) {u g : ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (Ioo a b)))
    (hg : MemLp g 2 (volume.restrict (Icc a b)))
    (hweak : HasWeakDerivOnIoo a b u g) :
    ∃ v : ℝ → ℝ,
      ContinuousOn v (Icc a b) ∧
      u =ᵐ[volume.restrict (Ioo a b)] v ∧
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
        |v t - v s| ^ 2 ≤
          (t - s) * ∫ x in Icc s t, |g x| ^ (2 : ℝ) := by
  rcases exists_continuousOn_representative_of_hasWeakDerivOnIoo
      hab hu hg hweak with ⟨v, hvContinuous, huv, hvIncrement⟩
  have hgIntegrable : IntegrableOn g (Icc a b) volume := by
    simpa only [IntegrableOn] using hg.integrable (by norm_num)
  refine ⟨v, hvContinuous, huv, ?_⟩
  intro s hs t ht hst
  have hgLocal : MemLp g 2 (volume.restrict (Icc s t)) :=
    hg.mono_measure
      (Measure.restrict_mono (Icc_subset_Icc hs.1 ht.2) le_rfl)
  rw [hvIncrement s hs t ht]
  simpa only [intervalPrimitive_sub_eq_intervalIntegral
    hgIntegrable hs ht] using
      sq_abs_intervalPrimitive_sub_le_l2
        hgIntegrable hs ht hst hgLocal

end

end PDE
