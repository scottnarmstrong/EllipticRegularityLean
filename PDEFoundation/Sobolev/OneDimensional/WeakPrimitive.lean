module

public import PDEFoundation.Measure.OneDimensionalCoordinate
public import PDEFoundation.Sobolev.OneDimensional.Primitive
public import PDEFoundation.Sobolev.OneDimensional.PrimitiveWeakIdentity
public import PDEFoundation.Sobolev.OneDimensional.SmoothTransport
public import PDEFoundation.Sobolev.WeakDerivative

/-!
# One-dimensional weak primitives

This file gives the one-dimensional notation used by the Sobolev foundation
without introducing a second weak-derivative predicate.  A scalar function is
realized on the native one-coordinate vector space, and the statement below is
definitionally an instance of `HasWeakPartialDerivOn` on the corresponding
axis box.

Exact scalar/native measure and integrability transport is supplied by
`OneDimensionalCoordinate`.  This file proves both the smooth-data sanity
bridge and the bounded `L¹` primitive bridge; the primitive-plus-constant
representation theorem remains a separate analytic step.
-/

@[expose] public section

namespace PDE

noncomputable section

/-- Scalar one-dimensional weak differentiation, expressed directly through
the shared native weak-partial-derivative predicate. -/
def HasWeakDerivOnIoo (a b : ℝ) (u g : ℝ → ℝ) : Prop :=
  HasWeakPartialDerivOn (oneDimensionalAxisBox a b) 0
    (liftOneDimensional u) (liftOneDimensional g)

/-- A `C¹` scalar function has its classical derivative as weak derivative on
every open interval.  This is the general smooth-data bridge from the scalar
one-dimensional notation to the shared native weak-derivative API. -/
theorem HasWeakDerivOnIoo.of_contDiff
    {a b : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    HasWeakDerivOnIoo a b f (deriv f) := by
  unfold HasWeakDerivOnIoo
  let F : Vec 1 → ℝ := liftOneDimensional f
  have hF : ContDiff ℝ 1 F := by
    change ContDiff ℝ 1 (fun x : Vec 1 => f (x 0))
    let π : Vec 1 →L[ℝ] ℝ := ContinuousLinearMap.proj 0
    simpa only [π] using! hf.comp π.contDiff
  have hWeak := HasWeakPartialDerivOn.of_contDiff
    (U := oneDimensionalAxisBox a b) (i := (0 : Fin 1)) hF
  have hDerivative :
      (fun x => (fderiv ℝ F x) (basisVec (0 : Fin 1))) =
        liftOneDimensional (deriv f) := by
    funext x
    rw [← scalarToVecOne_vecOneCoordinate x]
    simpa only [F, liftOneDimensional, scalarPullbackOne,
      vecOneCoordinate_scalarToVecOne] using!
      (deriv_scalarPullbackOne_eq_native_directional hF
        (vecOneCoordinate x)).symm
  rw [hDerivative] at hWeak
  exact hWeak

/-- The interval primitive of a continuous scalar function has the expected
classical derivative everywhere.  This separate form keeps the base point
explicit for later localization. -/
theorem hasDerivAt_intervalPrimitive_of_continuous
    {g : ℝ → ℝ} (hg : Continuous g) (c x : ℝ) :
    HasDerivAt (intervalPrimitive c g) (g x) x := by
  simpa only [intervalPrimitive] using!
    (hg.integral_hasStrictDerivAt c x).hasDerivAt

/-- The native lift of a continuous scalar interval primitive is `C¹`. -/
theorem contDiff_one_lift_intervalPrimitive_of_continuous
    {c : ℝ} {g : ℝ → ℝ} (hg : Continuous g) :
    ContDiff ℝ 1 (liftOneDimensional (intervalPrimitive c g)) := by
  rw [contDiff_one_iff_hasFDerivAt]
  let π : Vec 1 →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  refine ⟨fun x => (g (x 0)) • π, ?_, ?_⟩
  · exact (hg.comp (continuous_apply 0)).smul continuous_const
  · intro x
    have hπ : HasFDerivAt (fun y : Vec 1 => y 0) π x := by
      simpa [π] using! π.hasFDerivAt
    simpa [liftOneDimensional, Function.comp_apply, π] using!
      (hasDerivAt_intervalPrimitive_of_continuous hg c (x 0)).comp_hasFDerivAt x hπ

/-- Smooth-data weak derivative bridge for the interval primitive, stated in
the shared native weak-derivative API. -/
theorem intervalPrimitive_hasWeakDerivOnIoo_of_continuous
    {a b c : ℝ} {g : ℝ → ℝ} (hg : Continuous g) :
    HasWeakDerivOnIoo a b (intervalPrimitive c g) g := by
  unfold HasWeakDerivOnIoo
  let P : Vec 1 → ℝ := liftOneDimensional (intervalPrimitive c g)
  have hnative := HasWeakPartialDerivOn.of_contDiff
    (U := oneDimensionalAxisBox a b) (i := (0 : Fin 1))
    (f := P)
    (contDiff_one_lift_intervalPrimitive_of_continuous (c := c) hg)
  have hderiv :
      (fun x => (fderiv ℝ P x) (basisVec (0 : Fin 1))) =
        liftOneDimensional g := by
    funext x
    let π : Vec 1 →L[ℝ] ℝ := ContinuousLinearMap.proj 0
    have hπ : HasFDerivAt (fun y : Vec 1 => y 0) π x := by
      simpa [π] using! π.hasFDerivAt
    have hP : HasFDerivAt P ((g (x 0)) • π) x := by
      simpa [P, liftOneDimensional, Function.comp_apply, π] using!
        (hasDerivAt_intervalPrimitive_of_continuous hg c (x 0)).comp_hasFDerivAt x hπ
    rw [hP.fderiv]
    simp [π, basisVec, liftOneDimensional, vecOneCoordinate]
  rw [hderiv] at hnative
  exact hnative

/-- An interval primitive has its integrand as weak derivative on the
corresponding open interval whenever the integrand is integrable on the closed
interval.  The proof transports the scalar triangular-Fubini identity through
the native one-coordinate measure equivalence. -/
theorem intervalPrimitive_hasWeakDerivOnIoo_of_integrableOn_Icc
    {a b : ℝ} {g : ℝ → ℝ}
    (hg : MeasureTheory.IntegrableOn g (Set.Icc a b) MeasureTheory.volume) :
    HasWeakDerivOnIoo a b (intervalPrimitive a g) g := by
  unfold HasWeakDerivOnIoo
  intro φ hφSmooth _hφCompact hφSupport
  let φs : ℝ → ℝ := scalarPullbackOne φ
  have hφOne : ContDiff ℝ 1 φ := hφSmooth.of_le (by simp)
  have hφsOne : ContDiff ℝ 1 φs := by
    exact PDE.ContDiff.scalarPullbackOne hφOne
  have hφsSupport : tsupport φs ⊆ Set.Ioo a b := by
    exact tsupport_scalarPullbackOne_subset_Ioo hφSupport
  have hscalar := intervalPrimitive_scalar_weak_identity_Ioo hg hφsOne hφsSupport
  have hleft :
      (fun x => liftOneDimensional (intervalPrimitive a g) x *
        (fderiv ℝ φ x) (basisVec (0 : Fin 1))) =
        liftOneDimensional (fun t => intervalPrimitive a g t * deriv φs t) := by
    funext x
    simp only [liftOneDimensional]
    rw [show deriv φs (vecOneCoordinate x) =
      (fderiv ℝ φ (scalarToVecOne (vecOneCoordinate x))) (basisVec (0 : Fin 1)) by
        exact deriv_scalarPullbackOne_eq_native_directional hφOne _]
    rw [scalarToVecOne_vecOneCoordinate]
  have hright :
      (fun x => liftOneDimensional g x * φ x) =
        liftOneDimensional (fun t => g t * φs t) := by
    funext x
    simp only [liftOneDimensional, φs, scalarPullbackOne]
    rw [scalarToVecOne_vecOneCoordinate]
  rw [hleft, hright]
  calc
    (∫ x in oneDimensionalAxisBox a b,
        liftOneDimensional (fun t => intervalPrimitive a g t * deriv φs t) x) =
        ∫ t in Set.Ioo a b, intervalPrimitive a g t * deriv φs t :=
      setIntegral_axisBox_one_eq_setIntegral_Ioo a b
    _ = -∫ t in Set.Ioo a b, g t * φs t := hscalar
    _ = -(∫ x in oneDimensionalAxisBox a b,
        liftOneDimensional (fun t => g t * φs t) x) := by
      rw [setIntegral_axisBox_one_eq_setIntegral_Ioo]

end

end PDE
