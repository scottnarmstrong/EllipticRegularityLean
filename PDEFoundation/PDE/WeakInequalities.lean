module

public import PDEFoundation.PDE.WeakDivergenceForm
public import PDEFoundation.Sobolev.H1.PositiveDensity

/-!
# Safe weak divergence-form inequalities

This module gives separate smooth-test and all-`H¹₀` formulations of weak
subsolutions and supersolutions for
`-div (a ∇u) = f + div F`.

For a nonnegative test `φ`, the sign conventions are

* subsolution: `∫ a∇u · ∇φ ≤ ∫ fφ - ∫ F · ∇φ`;
* supersolution: `∫ fφ - ∫ F · ∇φ ≤ ∫ a∇u · ∇φ`.

The two test classes remain deliberately separate. For the explicit `L²`
data tier, this file uses the positivity-preserving density theorem to prove
the extension from smooth inequalities to all nonnegative `H¹₀` tests.
A bare smooth-test predicate without pairing-continuity data is not silently
extended.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open MeasureTheory

namespace WeakTestFunction

/-- A smooth compactly supported weak test is pointwise nonnegative. -/
def Nonnegative {d : ℕ} {U : Set (Vec d)}
    (φ : WeakTestFunction U) : Prop :=
  ∀ x, 0 ≤ φ x

end WeakTestFunction

namespace H10Function

/-- A representative-level `H¹₀` test is nonnegative almost everywhere on
its domain. This is invariant under changes of Sobolev representative. -/
def AENonnegative {d : ℕ} {U : Set (Vec d)}
    (φ : H10Function U) : Prop :=
  ∀ᵐ x ∂volumeOn U, 0 ≤ φ.toH1Function x

/-- Pointwise nonnegativity implies the representative-invariant
almost-everywhere sign condition. -/
theorem aeNonnegative_of_forall {d : ℕ} {U : Set (Vec d)}
    {φ : H10Function U}
    (hφ : ∀ x, 0 ≤ φ.toH1Function x) :
    φ.AENonnegative :=
  Filter.Eventually.of_forall hφ

end H10Function

/-- Safe smooth-test weak subsolution formulation of
`-div (a ∇u) ≤ f + div F`. -/
def IsWeakDivergenceFormSubsolutionOn {d : ℕ} (a : CoeffField d)
    (U : Set (Vec d)) (u : H1Function U) (f : Vec d → ℝ)
    (F : Vec d → Vec d) : Prop :=
  ∀ φ : WeakTestFunction U, φ.Nonnegative →
    WeakDivergenceFormTestableOn a U u f F φ ∧
      ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (φ.grad x) ≤
        (∫ x in U, f x * φ x) -
          ∫ x in U, vecDot (F x) (φ.grad x)

/-- Safe smooth-test weak supersolution formulation of
`f + div F ≤ -div (a ∇u)`. -/
def IsWeakDivergenceFormSupersolutionOn {d : ℕ} (a : CoeffField d)
    (U : Set (Vec d)) (u : H1Function U) (f : Vec d → ℝ)
    (F : Vec d → Vec d) : Prop :=
  ∀ φ : WeakTestFunction U, φ.Nonnegative →
    WeakDivergenceFormTestableOn a U u f F φ ∧
      (∫ x in U, f x * φ x) -
          ∫ x in U, vecDot (F x) (φ.grad x) ≤
        ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (φ.grad x)

/-- A homogeneous smooth-test weak subsolution. -/
abbrev IsWeakDivergenceFormSubharmonicOn {d : ℕ}
    (a : CoeffField d) (U : Set (Vec d)) (u : H1Function U) : Prop :=
  IsWeakDivergenceFormSubsolutionOn a U u 0 0

/-- A homogeneous smooth-test weak supersolution. -/
abbrev IsWeakDivergenceFormSuperharmonicOn {d : ℕ}
    (a : CoeffField d) (U : Set (Vec d)) (u : H1Function U) : Prop :=
  IsWeakDivergenceFormSupersolutionOn a U u 0 0

/-- Safe all-`H¹₀` weak subsolution formulation of
`-div (a ∇u) ≤ f + div F`. -/
def IsWeakDivergenceFormH10SubsolutionOn {d : ℕ} (a : CoeffField d)
    (U : Set (Vec d)) (u : H1Function U) (f : Vec d → ℝ)
    (F : Vec d → Vec d) : Prop :=
  ∀ φ : H10Function U, φ.AENonnegative →
    WeakDivergenceFormH10TestableOn a U u f F φ ∧
      ∫ x in U, vecDot (matVecMul (a x) (u.grad x))
          (φ.toH1Function.grad x) ≤
        (∫ x in U, f x * φ.toH1Function x) -
          ∫ x in U, vecDot (F x) (φ.toH1Function.grad x)

/-- Safe all-`H¹₀` weak supersolution formulation of
`f + div F ≤ -div (a ∇u)`. -/
def IsWeakDivergenceFormH10SupersolutionOn {d : ℕ} (a : CoeffField d)
    (U : Set (Vec d)) (u : H1Function U) (f : Vec d → ℝ)
    (F : Vec d → Vec d) : Prop :=
  ∀ φ : H10Function U, φ.AENonnegative →
    WeakDivergenceFormH10TestableOn a U u f F φ ∧
      (∫ x in U, f x * φ.toH1Function x) -
          ∫ x in U, vecDot (F x) (φ.toH1Function.grad x) ≤
        ∫ x in U, vecDot (matVecMul (a x) (u.grad x))
          (φ.toH1Function.grad x)

/-- A homogeneous all-`H¹₀` weak subsolution. -/
abbrev IsWeakDivergenceFormH10SubharmonicOn {d : ℕ}
    (a : CoeffField d) (U : Set (Vec d)) (u : H1Function U) : Prop :=
  IsWeakDivergenceFormH10SubsolutionOn a U u 0 0

/-- A homogeneous all-`H¹₀` weak supersolution. -/
abbrev IsWeakDivergenceFormH10SuperharmonicOn {d : ℕ}
    (a : CoeffField d) (U : Set (Vec d)) (u : H1Function U) : Prop :=
  IsWeakDivergenceFormH10SupersolutionOn a U u 0 0

/-- An `L²`-data weak subsolution. The data fields supply continuity and
genuine integrability for the passage from smooth nonnegative tests to all
nonnegative representative-level `H¹₀` tests. -/
structure IsWeakDivergenceFormL2SubsolutionOn {d : ℕ} (a : CoeffField d)
    (U : Set (Vec d)) (u : H1Function U) (f : Vec d → ℝ)
    (F : Vec d → Vec d) : Prop extends DivergenceFormL2DataOn a U u f F where
  inequality : ∀ φ : WeakTestFunction U, φ.Nonnegative →
    ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (φ.grad x) ≤
      (∫ x in U, f x * φ x) -
        ∫ x in U, vecDot (F x) (φ.grad x)

/-- An `L²`-data weak supersolution. The data fields supply continuity and
genuine integrability for the passage from smooth nonnegative tests to all
nonnegative representative-level `H¹₀` tests. -/
structure IsWeakDivergenceFormL2SupersolutionOn {d : ℕ} (a : CoeffField d)
    (U : Set (Vec d)) (u : H1Function U) (f : Vec d → ℝ)
    (F : Vec d → Vec d) : Prop extends DivergenceFormL2DataOn a U u f F where
  inequality : ∀ φ : WeakTestFunction U, φ.Nonnegative →
    (∫ x in U, f x * φ x) -
        ∫ x in U, vecDot (F x) (φ.grad x) ≤
      ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (φ.grad x)

namespace IsWeakDivergenceFormL2SubsolutionOn

/-- Forget the `L²` packaging while retaining the term-by-term integrability
required by the safe smooth-test predicate. -/
theorem toIsWeakDivergenceFormSubsolutionOn
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    {u : H1Function U} {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hsub : IsWeakDivergenceFormL2SubsolutionOn a U u f F) :
    IsWeakDivergenceFormSubsolutionOn a U u f F := by
  intro φ hφ
  exact
    ⟨hsub.toDivergenceFormL2DataOn.testable φ,
      hsub.inequality φ hφ⟩

/-- Extend an `L²`-data smooth-test subsolution to every nonnegative
representative-level `H¹₀` test on a bounded open convex domain. -/
theorem toH10SubsolutionOn
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    {u : H1Function U} {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hsub : IsWeakDivergenceFormL2SubsolutionOn a U u f F)
    (hU : IsOpenBoundedConvexDomain U) :
    IsWeakDivergenceFormH10SubsolutionOn a U u f F := by
  intro φ hφ
  refine ⟨hsub.toDivergenceFormL2DataOn.h10_testable φ, ?_⟩
  obtain ⟨hpositive, hpositiveNonnegative⟩ :=
    φ.toH1Function.exists_nonnegative_supportedSmoothApproximation
      hU φ.supportedSmoothApproximation hφ
  let φn : ℕ → WeakTestFunction U :=
    fun n => hpositive.toWeakTestFunction n
  have hφnNonnegative : ∀ n, (φn n).Nonnegative := by
    intro n x
    exact hpositiveNonnegative n x
  have hgrad : ∀ i : Fin d, Filter.Tendsto
      (fun n =>
        eLpNorm
          (fun x => (φn n).grad x i - φ.toH1Function.grad x i)
          (2 : ℝ≥0∞) (volumeOn U))
      Filter.atTop (nhds 0) := by
    intro i
    simpa only [φn,
      H1Function.SupportedSmoothApproximation.toWeakTestFunction,
      WeakTestFunction.grad_apply,
      WeakTestFunction.partialDeriv] using!
      hpositive.tendsto_grad i
  have hvalue : Filter.Tendsto
      (fun n =>
        eLpNorm
          (fun x => φn n x - φ.toH1Function x)
          (2 : ℝ≥0∞) (volumeOn U))
      Filter.atTop (nhds 0) := by
    simpa only [φn,
      H1Function.SupportedSmoothApproximation.toWeakTestFunction] using!
      hpositive.tendsto_value
  have hflux :=
    tendsto_setIntegral_vecDot_of_tendsto_coordinate_eLpNorm
      hsub.flux_memL2
      (fun n => (φn n).grad_memVectorL2On)
      φ.toH1Function.gradMemL2 hgrad
  have hsource :=
    tendsto_setIntegral_mul_of_tendsto_eLpNorm
      hsub.source_memL2
      (fun n => (φn n).memL2On)
      φ.toH1Function.memL2 hvalue
  have hforcing :=
    tendsto_setIntegral_vecDot_of_tendsto_coordinate_eLpNorm
      hsub.forcing_memL2
      (fun n => (φn n).grad_memVectorL2On)
      φ.toH1Function.gradMemL2 hgrad
  exact
    le_of_tendsto_of_tendsto' hflux (hsource.sub hforcing)
      (fun n => hsub.inequality (φn n) (hφnNonnegative n))

end IsWeakDivergenceFormL2SubsolutionOn

namespace IsWeakDivergenceFormL2SupersolutionOn

/-- Forget the `L²` packaging while retaining the term-by-term integrability
required by the safe smooth-test predicate. -/
theorem toIsWeakDivergenceFormSupersolutionOn
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    {u : H1Function U} {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hsuper : IsWeakDivergenceFormL2SupersolutionOn a U u f F) :
    IsWeakDivergenceFormSupersolutionOn a U u f F := by
  intro φ hφ
  exact
    ⟨hsuper.toDivergenceFormL2DataOn.testable φ,
      hsuper.inequality φ hφ⟩

/-- Extend an `L²`-data smooth-test supersolution to every nonnegative
representative-level `H¹₀` test on a bounded open convex domain. -/
theorem toH10SupersolutionOn
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    {u : H1Function U} {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hsuper : IsWeakDivergenceFormL2SupersolutionOn a U u f F)
    (hU : IsOpenBoundedConvexDomain U) :
    IsWeakDivergenceFormH10SupersolutionOn a U u f F := by
  intro φ hφ
  refine ⟨hsuper.toDivergenceFormL2DataOn.h10_testable φ, ?_⟩
  obtain ⟨hpositive, hpositiveNonnegative⟩ :=
    φ.toH1Function.exists_nonnegative_supportedSmoothApproximation
      hU φ.supportedSmoothApproximation hφ
  let φn : ℕ → WeakTestFunction U :=
    fun n => hpositive.toWeakTestFunction n
  have hφnNonnegative : ∀ n, (φn n).Nonnegative := by
    intro n x
    exact hpositiveNonnegative n x
  have hgrad : ∀ i : Fin d, Filter.Tendsto
      (fun n =>
        eLpNorm
          (fun x => (φn n).grad x i - φ.toH1Function.grad x i)
          (2 : ℝ≥0∞) (volumeOn U))
      Filter.atTop (nhds 0) := by
    intro i
    simpa only [φn,
      H1Function.SupportedSmoothApproximation.toWeakTestFunction,
      WeakTestFunction.grad_apply,
      WeakTestFunction.partialDeriv] using!
      hpositive.tendsto_grad i
  have hvalue : Filter.Tendsto
      (fun n =>
        eLpNorm
          (fun x => φn n x - φ.toH1Function x)
          (2 : ℝ≥0∞) (volumeOn U))
      Filter.atTop (nhds 0) := by
    simpa only [φn,
      H1Function.SupportedSmoothApproximation.toWeakTestFunction] using!
      hpositive.tendsto_value
  have hflux :=
    tendsto_setIntegral_vecDot_of_tendsto_coordinate_eLpNorm
      hsuper.flux_memL2
      (fun n => (φn n).grad_memVectorL2On)
      φ.toH1Function.gradMemL2 hgrad
  have hsource :=
    tendsto_setIntegral_mul_of_tendsto_eLpNorm
      hsuper.source_memL2
      (fun n => (φn n).memL2On)
      φ.toH1Function.memL2 hvalue
  have hforcing :=
    tendsto_setIntegral_vecDot_of_tendsto_coordinate_eLpNorm
      hsuper.forcing_memL2
      (fun n => (φn n).grad_memVectorL2On)
      φ.toH1Function.gradMemL2 hgrad
  exact
    le_of_tendsto_of_tendsto' (hsource.sub hforcing) hflux
      (fun n => hsuper.inequality (φn n) (hφnNonnegative n))

end IsWeakDivergenceFormL2SupersolutionOn

namespace IsWeakDivergenceFormSolutionOn

/-- A smooth-test weak solution is a smooth-test weak subsolution. -/
theorem toSubsolutionOn {d : ℕ} {a : CoeffField d}
    {U : Set (Vec d)} {u : H1Function U}
    {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hsol : IsWeakDivergenceFormSolutionOn a U u f F) :
    IsWeakDivergenceFormSubsolutionOn a U u f F := by
  intro φ _
  rcases hsol φ with ⟨htestable, hidentity⟩
  exact ⟨htestable, hidentity.le⟩

/-- A smooth-test weak solution is a smooth-test weak supersolution. -/
theorem toSupersolutionOn {d : ℕ} {a : CoeffField d}
    {U : Set (Vec d)} {u : H1Function U}
    {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hsol : IsWeakDivergenceFormSolutionOn a U u f F) :
    IsWeakDivergenceFormSupersolutionOn a U u f F := by
  intro φ _
  rcases hsol φ with ⟨htestable, hidentity⟩
  exact ⟨htestable, hidentity.ge⟩

end IsWeakDivergenceFormSolutionOn

namespace IsWeakDivergenceFormSubsolutionOn

/-- Package a safe smooth-test subsolution together with explicit `L²`
pairing data. -/
theorem toL2SubsolutionOn
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    {u : H1Function U} {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hsub : IsWeakDivergenceFormSubsolutionOn a U u f F)
    (hdata : DivergenceFormL2DataOn a U u f F) :
    IsWeakDivergenceFormL2SubsolutionOn a U u f F where
  toDivergenceFormL2DataOn := hdata
  inequality := fun φ hφ => (hsub φ hφ).2

/-- Under explicit `L²` pairing data, a safe smooth-test subsolution extends
to every nonnegative representative-level `H¹₀` test. -/
theorem toH10SubsolutionOn
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    {u : H1Function U} {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hsub : IsWeakDivergenceFormSubsolutionOn a U u f F)
    (hU : IsOpenBoundedConvexDomain U)
    (hdata : DivergenceFormL2DataOn a U u f F) :
    IsWeakDivergenceFormH10SubsolutionOn a U u f F :=
  (hsub.toL2SubsolutionOn hdata).toH10SubsolutionOn hU

/-- Uniform ellipticity and explicit source/forcing membership supply the
`L²` data needed to extend a smooth-test subsolution to all nonnegative
`H¹₀` tests. -/
theorem toH10SubsolutionOn_of_isEllipticFieldOn
    {d : ℕ} {lam Lam : ℝ} {a : CoeffField d}
    {U : Set (Vec d)} {u : H1Function U}
    {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hsub : IsWeakDivergenceFormSubsolutionOn a U u f F)
    (hU : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hf : MemL2On U f) (hF : MemVectorL2On U F) :
    IsWeakDivergenceFormH10SubsolutionOn a U u f F :=
  hsub.toH10SubsolutionOn hU
    (DivergenceFormL2DataOn.of_isEllipticFieldOn hEll hf hF)

/-- A uniformly elliptic homogeneous smooth-test subsolution extends to the
all-`H¹₀` subharmonic interface. -/
theorem toH10SubharmonicOn
    {d : ℕ} {lam Lam : ℝ} {a : CoeffField d}
    {U : Set (Vec d)} {u : H1Function U}
    (hsub : IsWeakDivergenceFormSubharmonicOn a U u)
    (hU : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    IsWeakDivergenceFormH10SubharmonicOn a U u :=
  hsub.toH10SubsolutionOn_of_isEllipticFieldOn hU hEll
    MeasureTheory.MemLp.zero (by
      intro i
      simpa only [Pi.zero_apply] using!
        (MeasureTheory.MemLp.zero :
          MemL2On U (0 : Vec d → ℝ)))

/-- Transport a smooth-test weak subsolution across coefficient fields that
agree almost everywhere on the domain. -/
theorem of_ae_eq_coeff {d : ℕ} {a b : CoeffField d}
    {U : Set (Vec d)} {u : H1Function U}
    {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hab : CoeffAEEqOn U a b)
    (hsub : IsWeakDivergenceFormSubsolutionOn a U u f F) :
    IsWeakDivergenceFormSubsolutionOn b U u f F := by
  intro φ hφ
  rcases hsub φ hφ with ⟨htestable, hinequality⟩
  have hfluxAE :
      (fun x =>
        vecDot (matVecMul (a x) (u.grad x)) (φ.grad x)) =ᵐ[volumeOn U]
      fun x => vecDot (matVecMul (b x) (u.grad x)) (φ.grad x) := by
    filter_upwards [hab] with x hxab
    rw [hxab]
  refine ⟨?_, ?_⟩
  · exact
      ⟨(integrableOn_congr_fun_ae hfluxAE).mp htestable.flux_integrable,
        htestable.source_integrable, htestable.forcing_integrable⟩
  · calc
      ∫ x in U, vecDot (matVecMul (b x) (u.grad x)) (φ.grad x) =
          ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (φ.grad x) :=
        integral_congr_ae hfluxAE.symm
      _ ≤ (∫ x in U, f x * φ x) -
          ∫ x in U, vecDot (F x) (φ.grad x) :=
        hinequality

end IsWeakDivergenceFormSubsolutionOn

namespace IsWeakDivergenceFormSupersolutionOn

/-- Package a safe smooth-test supersolution together with explicit `L²`
pairing data. -/
theorem toL2SupersolutionOn
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    {u : H1Function U} {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hsuper : IsWeakDivergenceFormSupersolutionOn a U u f F)
    (hdata : DivergenceFormL2DataOn a U u f F) :
    IsWeakDivergenceFormL2SupersolutionOn a U u f F where
  toDivergenceFormL2DataOn := hdata
  inequality := fun φ hφ => (hsuper φ hφ).2

/-- Under explicit `L²` pairing data, a safe smooth-test supersolution extends
to every nonnegative representative-level `H¹₀` test. -/
theorem toH10SupersolutionOn
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    {u : H1Function U} {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hsuper : IsWeakDivergenceFormSupersolutionOn a U u f F)
    (hU : IsOpenBoundedConvexDomain U)
    (hdata : DivergenceFormL2DataOn a U u f F) :
    IsWeakDivergenceFormH10SupersolutionOn a U u f F :=
  (hsuper.toL2SupersolutionOn hdata).toH10SupersolutionOn hU

/-- Uniform ellipticity and explicit source/forcing membership supply the
`L²` data needed to extend a smooth-test supersolution to all nonnegative
`H¹₀` tests. -/
theorem toH10SupersolutionOn_of_isEllipticFieldOn
    {d : ℕ} {lam Lam : ℝ} {a : CoeffField d}
    {U : Set (Vec d)} {u : H1Function U}
    {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hsuper : IsWeakDivergenceFormSupersolutionOn a U u f F)
    (hU : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hf : MemL2On U f) (hF : MemVectorL2On U F) :
    IsWeakDivergenceFormH10SupersolutionOn a U u f F :=
  hsuper.toH10SupersolutionOn hU
    (DivergenceFormL2DataOn.of_isEllipticFieldOn hEll hf hF)

/-- A uniformly elliptic homogeneous smooth-test supersolution extends to the
all-`H¹₀` superharmonic interface. -/
theorem toH10SuperharmonicOn
    {d : ℕ} {lam Lam : ℝ} {a : CoeffField d}
    {U : Set (Vec d)} {u : H1Function U}
    (hsuper : IsWeakDivergenceFormSuperharmonicOn a U u)
    (hU : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    IsWeakDivergenceFormH10SuperharmonicOn a U u :=
  hsuper.toH10SupersolutionOn_of_isEllipticFieldOn hU hEll
    MeasureTheory.MemLp.zero (by
      intro i
      simpa only [Pi.zero_apply] using!
        (MeasureTheory.MemLp.zero :
          MemL2On U (0 : Vec d → ℝ)))

/-- Transport a smooth-test weak supersolution across coefficient fields that
agree almost everywhere on the domain. -/
theorem of_ae_eq_coeff {d : ℕ} {a b : CoeffField d}
    {U : Set (Vec d)} {u : H1Function U}
    {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hab : CoeffAEEqOn U a b)
    (hsuper : IsWeakDivergenceFormSupersolutionOn a U u f F) :
    IsWeakDivergenceFormSupersolutionOn b U u f F := by
  intro φ hφ
  rcases hsuper φ hφ with ⟨htestable, hinequality⟩
  have hfluxAE :
      (fun x =>
        vecDot (matVecMul (a x) (u.grad x)) (φ.grad x)) =ᵐ[volumeOn U]
      fun x => vecDot (matVecMul (b x) (u.grad x)) (φ.grad x) := by
    filter_upwards [hab] with x hxab
    rw [hxab]
  refine ⟨?_, ?_⟩
  · exact
      ⟨(integrableOn_congr_fun_ae hfluxAE).mp htestable.flux_integrable,
        htestable.source_integrable, htestable.forcing_integrable⟩
  · calc
      (∫ x in U, f x * φ x) -
          ∫ x in U, vecDot (F x) (φ.grad x) ≤
          ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (φ.grad x) :=
        hinequality
      _ = ∫ x in U, vecDot (matVecMul (b x) (u.grad x)) (φ.grad x) :=
        integral_congr_ae hfluxAE

end IsWeakDivergenceFormSupersolutionOn

namespace IsWeakDivergenceFormH10SolutionOn

/-- An all-`H¹₀` weak solution is an all-`H¹₀` weak subsolution. -/
theorem toSubsolutionOn {d : ℕ} {a : CoeffField d}
    {U : Set (Vec d)} {u : H1Function U}
    {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hsol : IsWeakDivergenceFormH10SolutionOn a U u f F) :
    IsWeakDivergenceFormH10SubsolutionOn a U u f F := by
  intro φ _
  rcases hsol φ with ⟨htestable, hidentity⟩
  exact ⟨htestable, hidentity.le⟩

/-- An all-`H¹₀` weak solution is an all-`H¹₀` weak supersolution. -/
theorem toSupersolutionOn {d : ℕ} {a : CoeffField d}
    {U : Set (Vec d)} {u : H1Function U}
    {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hsol : IsWeakDivergenceFormH10SolutionOn a U u f F) :
    IsWeakDivergenceFormH10SupersolutionOn a U u f F := by
  intro φ _
  rcases hsol φ with ⟨htestable, hidentity⟩
  exact ⟨htestable, hidentity.ge⟩

end IsWeakDivergenceFormH10SolutionOn

namespace IsWeakDivergenceFormH10SubsolutionOn

/-- Transport an all-`H¹₀` weak subsolution across coefficient fields that
agree almost everywhere on the domain. -/
theorem of_ae_eq_coeff {d : ℕ} {a b : CoeffField d}
    {U : Set (Vec d)} {u : H1Function U}
    {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hab : CoeffAEEqOn U a b)
    (hsub : IsWeakDivergenceFormH10SubsolutionOn a U u f F) :
    IsWeakDivergenceFormH10SubsolutionOn b U u f F := by
  intro φ hφ
  rcases hsub φ hφ with ⟨htestable, hinequality⟩
  have hfluxAE :
      (fun x => vecDot (matVecMul (a x) (u.grad x))
        (φ.toH1Function.grad x)) =ᵐ[volumeOn U]
      fun x => vecDot (matVecMul (b x) (u.grad x))
        (φ.toH1Function.grad x) := by
    filter_upwards [hab] with x hxab
    rw [hxab]
  refine ⟨?_, ?_⟩
  · exact
      ⟨(integrableOn_congr_fun_ae hfluxAE).mp htestable.flux_integrable,
        htestable.source_integrable, htestable.forcing_integrable⟩
  · calc
      ∫ x in U, vecDot (matVecMul (b x) (u.grad x))
          (φ.toH1Function.grad x) =
          ∫ x in U, vecDot (matVecMul (a x) (u.grad x))
            (φ.toH1Function.grad x) :=
        integral_congr_ae hfluxAE.symm
      _ ≤ (∫ x in U, f x * φ.toH1Function x) -
          ∫ x in U, vecDot (F x) (φ.toH1Function.grad x) :=
        hinequality

/-- Restrict an all-`H¹₀` weak subsolution to nonnegative smooth compactly
supported tests. -/
theorem toIsWeakDivergenceFormSubsolutionOn
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    {u : H1Function U} {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hU : IsOpen U)
    (hsub : IsWeakDivergenceFormH10SubsolutionOn a U u f F) :
    IsWeakDivergenceFormSubsolutionOn a U u f F := by
  intro φ hφ
  let φ10 : H10Function U :=
    H10Function.ofContDiff hU φ.contDiff φ.hasCompactSupport
      φ.tsupport_subset
  have hφ10 : φ10.AENonnegative := by
    apply H10Function.aeNonnegative_of_forall
    intro x
    simpa only [φ10, H10Function.ofContDiff_toFun] using hφ x
  rcases hsub φ10 hφ10 with ⟨htestable, hinequality⟩
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · simpa only [φ10, H10Function.ofContDiff_grad,
        WeakTestFunction.grad_apply,
        WeakTestFunction.partialDeriv] using! htestable.flux_integrable
    · simpa only [φ10, H10Function.ofContDiff_toFun] using
        htestable.source_integrable
    · simpa only [φ10, H10Function.ofContDiff_grad,
        WeakTestFunction.grad_apply,
        WeakTestFunction.partialDeriv] using! htestable.forcing_integrable
  · simpa only [φ10, H10Function.ofContDiff_toFun,
      H10Function.ofContDiff_grad, WeakTestFunction.grad_apply,
      WeakTestFunction.partialDeriv] using! hinequality

end IsWeakDivergenceFormH10SubsolutionOn

namespace IsWeakDivergenceFormH10SupersolutionOn

/-- Transport an all-`H¹₀` weak supersolution across coefficient fields that
agree almost everywhere on the domain. -/
theorem of_ae_eq_coeff {d : ℕ} {a b : CoeffField d}
    {U : Set (Vec d)} {u : H1Function U}
    {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hab : CoeffAEEqOn U a b)
    (hsuper : IsWeakDivergenceFormH10SupersolutionOn a U u f F) :
    IsWeakDivergenceFormH10SupersolutionOn b U u f F := by
  intro φ hφ
  rcases hsuper φ hφ with ⟨htestable, hinequality⟩
  have hfluxAE :
      (fun x => vecDot (matVecMul (a x) (u.grad x))
        (φ.toH1Function.grad x)) =ᵐ[volumeOn U]
      fun x => vecDot (matVecMul (b x) (u.grad x))
        (φ.toH1Function.grad x) := by
    filter_upwards [hab] with x hxab
    rw [hxab]
  refine ⟨?_, ?_⟩
  · exact
      ⟨(integrableOn_congr_fun_ae hfluxAE).mp htestable.flux_integrable,
        htestable.source_integrable, htestable.forcing_integrable⟩
  · calc
      (∫ x in U, f x * φ.toH1Function x) -
          ∫ x in U, vecDot (F x) (φ.toH1Function.grad x) ≤
          ∫ x in U, vecDot (matVecMul (a x) (u.grad x))
            (φ.toH1Function.grad x) :=
        hinequality
      _ = ∫ x in U, vecDot (matVecMul (b x) (u.grad x))
          (φ.toH1Function.grad x) :=
        integral_congr_ae hfluxAE

/-- Restrict an all-`H¹₀` weak supersolution to nonnegative smooth compactly
supported tests. -/
theorem toIsWeakDivergenceFormSupersolutionOn
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    {u : H1Function U} {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hU : IsOpen U)
    (hsuper : IsWeakDivergenceFormH10SupersolutionOn a U u f F) :
    IsWeakDivergenceFormSupersolutionOn a U u f F := by
  intro φ hφ
  let φ10 : H10Function U :=
    H10Function.ofContDiff hU φ.contDiff φ.hasCompactSupport
      φ.tsupport_subset
  have hφ10 : φ10.AENonnegative := by
    apply H10Function.aeNonnegative_of_forall
    intro x
    simpa only [φ10, H10Function.ofContDiff_toFun] using hφ x
  rcases hsuper φ10 hφ10 with ⟨htestable, hinequality⟩
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · simpa only [φ10, H10Function.ofContDiff_grad,
        WeakTestFunction.grad_apply,
        WeakTestFunction.partialDeriv] using! htestable.flux_integrable
    · simpa only [φ10, H10Function.ofContDiff_toFun] using
        htestable.source_integrable
    · simpa only [φ10, H10Function.ofContDiff_grad,
        WeakTestFunction.grad_apply,
        WeakTestFunction.partialDeriv] using! htestable.forcing_integrable
  · simpa only [φ10, H10Function.ofContDiff_toFun,
      H10Function.ofContDiff_grad, WeakTestFunction.grad_apply,
      WeakTestFunction.partialDeriv] using! hinequality

end IsWeakDivergenceFormH10SupersolutionOn

namespace IsWeakDivergenceFormHarmonicOn

/-- A uniformly elliptic homogeneous weak solution is an all-`H¹₀`
subsolution. -/
theorem toH10SubharmonicOn {d : ℕ} {lam Lam : ℝ}
    {a : CoeffField d} {U : Set (Vec d)} {u : H1Function U}
    (hsol : IsWeakDivergenceFormHarmonicOn a U u)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    IsWeakDivergenceFormH10SubharmonicOn a U u :=
  (hsol.toH10SolutionOn hEll).toSubsolutionOn

/-- A uniformly elliptic homogeneous weak solution is an all-`H¹₀`
supersolution. -/
theorem toH10SuperharmonicOn {d : ℕ} {lam Lam : ℝ}
    {a : CoeffField d} {U : Set (Vec d)} {u : H1Function U}
    (hsol : IsWeakDivergenceFormHarmonicOn a U u)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    IsWeakDivergenceFormH10SuperharmonicOn a U u :=
  (hsol.toH10SolutionOn hEll).toSupersolutionOn

end IsWeakDivergenceFormHarmonicOn

end PDE
