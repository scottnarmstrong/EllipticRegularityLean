module

public import PDEFoundation.PDE.CoefficientL2
public import PDEFoundation.Sobolev.H1.Pairing
public import PDEFoundation.Sobolev.H1.ZeroBoundary

/-!
# Safe weak divergence-form equations

This module gives the representative-level weak formulation for
`-div (a ∇u) = f + div F`.  It keeps every term's integrability alongside the
identity: Lean's Bochner integral is total, so an equality of bare integrals
would otherwise allow non-integrable expressions.

The first interface is smooth-test based.  For `L²` data, the file proves the
extension to all representative-level `H¹₀` tests by pairing continuity.  The
two interfaces remain separate because a bare smooth-test identity without
such data need not have a justified density extension.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open MeasureTheory

/-- Coefficient fields agree almost everywhere on `U`.

This is an exact alias for restricted-volume almost-everywhere equality, not
a new bundled coefficient carrier. -/
abbrev CoeffAEEqOn {d : ℕ} (U : Set (Vec d))
    (a b : CoeffField d) : Prop :=
  a =ᵐ[volumeOn U] b

namespace CoeffAEEqOn

/-- Taking real adjoints preserves coefficient equality almost everywhere. -/
theorem adjoint {d : ℕ} {U : Set (Vec d)} {a b : CoeffField d}
    (hab : CoeffAEEqOn U a b) :
    CoeffAEEqOn U (adjointCoeffField a) (adjointCoeffField b) := by
  filter_upwards [hab] with x hx
  simp only [adjointCoeffField_apply, hx]

/-- Applying almost-everywhere equal coefficient matrices to the same vector
field gives almost-everywhere equal fluxes. -/
theorem matVecMul {d : ℕ} {U : Set (Vec d)} {a b : CoeffField d}
    (hab : CoeffAEEqOn U a b) (G : Vec d → Vec d) :
    (fun x => matVecMul (a x) (G x)) =ᵐ[volumeOn U]
      fun x => matVecMul (b x) (G x) := by
  filter_upwards [hab] with x hx
  rw [hx]

end CoeffAEEqOn

private noncomputable def scalarL2Pairing {d : ℕ} (U : Set (Vec d)) :
    ScalarLp U (2 : ℝ≥0∞) →L[ℝ] ScalarLp U (2 : ℝ≥0∞) →L[ℝ] ℝ := by
  exact (ContinuousLinearMap.mul ℝ ℝ).lpPairing (volumeOn U) 2 2

private theorem scalarLpDualPairing_apply_eq_setIntegral
    {d : ℕ} {U : Set (Vec d)} {g h : Vec d → ℝ}
    (hg : MemL2On U g) (hh : MemL2On U h) :
    scalarL2Pairing U hg.toScalarLp hh.toScalarLp =
      ∫ x in U, g x * h x := by
  rw [scalarL2Pairing, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toScalarLp, hh.coeFn_toScalarLp] with x hxg hxh
  rw [hxg, hxh]
  rfl

/-- Scalar `L²` pairing is continuous under representative-level `L²`
convergence in its second argument. -/
theorem tendsto_setIntegral_mul_of_tendsto_eLpNorm
    {d : ℕ} {U : Set (Vec d)} {g : Vec d → ℝ}
    {h : ℕ → Vec d → ℝ} {hlim : Vec d → ℝ}
    (hg : MemL2On U g) (hh : ∀ n, MemL2On U (h n))
    (hlim_mem : MemL2On U hlim)
    (htendsto : Filter.Tendsto
      (fun n => eLpNorm (fun x => h n x - hlim x) (2 : ℝ≥0∞) (volumeOn U))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫ x in U, g x * h n x) Filter.atTop
      (nhds (∫ x in U, g x * hlim x)) := by
  have hLp : Filter.Tendsto (fun n => (hh n).toScalarLp) Filter.atTop
      (nhds hlim_mem.toScalarLp) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' h hh hlim hlim_mem).mpr htendsto
  have hPair : Filter.Tendsto
      (fun n => scalarL2Pairing U hg.toScalarLp (hh n).toScalarLp)
      Filter.atTop
      (nhds (scalarL2Pairing U hg.toScalarLp hlim_mem.toScalarLp)) := by
    exact ((scalarL2Pairing U hg.toScalarLp).continuous.tendsto _).comp hLp
  have hterms :
      (fun n => scalarL2Pairing U hg.toScalarLp (hh n).toScalarLp) =
        fun n => ∫ x in U, g x * h n x := by
    funext n
    exact scalarLpDualPairing_apply_eq_setIntegral hg (hh n)
  have hlim_term :
      scalarL2Pairing U hg.toScalarLp hlim_mem.toScalarLp =
        ∫ x in U, g x * hlim x :=
    scalarLpDualPairing_apply_eq_setIntegral hg hlim_mem
  rw [hterms, hlim_term] at hPair
  exact hPair

/-- Native-vector `L²` pairing is continuous when every coordinate of its
second argument converges in `L²`. -/
theorem tendsto_setIntegral_vecDot_of_tendsto_coordinate_eLpNorm
    {d : ℕ} {U : Set (Vec d)} {F : Vec d → Vec d}
    {G : ℕ → Vec d → Vec d} {Glim : Vec d → Vec d}
    (hF : MemVectorL2On U F) (hG : ∀ n, MemVectorL2On U (G n))
    (hGlim : MemVectorL2On U Glim)
    (htendsto : ∀ i : Fin d, Filter.Tendsto
      (fun n => eLpNorm (fun x => G n x i - Glim x i) (2 : ℝ≥0∞) (volumeOn U))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫ x in U, vecDot (F x) (G n x)) Filter.atTop
      (nhds (∫ x in U, vecDot (F x) (Glim x))) := by
  have hcoord (i : Fin d) : Filter.Tendsto
      (fun n => ∫ x in U, F x i * G n x i) Filter.atTop
      (nhds (∫ x in U, F x i * Glim x i)) :=
    tendsto_setIntegral_mul_of_tendsto_eLpNorm (hF i) (fun n => hG n i)
      (hGlim i) (htendsto i)
  have hsum : Filter.Tendsto
      (fun n => ∑ i, ∫ x in U, F x i * G n x i) Filter.atTop
      (nhds (∑ i, ∫ x in U, F x i * Glim x i)) :=
    tendsto_finsetSum _ fun i _ => hcoord i
  have hleft :
      (fun n => ∫ x in U, vecDot (F x) (G n x)) =
        fun n => ∑ i, ∫ x in U, F x i * G n x i := by
    funext n
    change (∫ x in U, ∑ i, F x i * G n x i) = _
    rw [integral_finsetSum]
    intro i _
    exact integrableOn_mul_of_memL2On (hF i) (hG n i)
  have hright :
      (∫ x in U, vecDot (F x) (Glim x)) =
        ∑ i, ∫ x in U, F x i * Glim x i := by
    change (∫ x in U, ∑ i, F x i * Glim x i) = _
    rw [integral_finsetSum]
    intro i _
    exact integrableOn_mul_of_memL2On (hF i) (hGlim i)
  rw [hleft, hright]
  exact hsum

/-- Term-by-term integrability required to test a divergence-form equation
against a smooth compactly supported function. -/
structure WeakDivergenceFormTestableOn {d : ℕ} (a : CoeffField d)
    (U : Set (Vec d)) (u : H1Function U) (f : Vec d → ℝ)
    (F : Vec d → Vec d) (φ : WeakTestFunction U) : Prop where
  flux_integrable :
    IntegrableOn
      (fun x => vecDot (matVecMul (a x) (u.grad x)) (φ.grad x)) U
  source_integrable : IntegrableOn (fun x => f x * φ x) U
  forcing_integrable : IntegrableOn (fun x => vecDot (F x) (φ.grad x)) U

/-- Safe smooth-test weak formulation of
`-div (a ∇u) = f + div F` on `U`.

The sign is chosen so that integration by parts gives
`∫ a∇u · ∇φ = ∫ f φ - ∫ F · ∇φ`. -/
def IsWeakDivergenceFormSolutionOn {d : ℕ} (a : CoeffField d)
    (U : Set (Vec d)) (u : H1Function U) (f : Vec d → ℝ)
    (F : Vec d → Vec d) : Prop :=
  ∀ φ : WeakTestFunction U,
    WeakDivergenceFormTestableOn a U u f F φ ∧
      ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (φ.grad x) =
        (∫ x in U, f x * φ x) - ∫ x in U, vecDot (F x) (φ.grad x)

/-- `L²` data sufficient to test all three terms of the weak equation against
smooth compactly supported functions.  The flux is a separate field on
purpose: it is not inferred from a bare coefficient field without a proved
boundedness or ellipticity hypothesis. -/
structure DivergenceFormL2DataOn {d : ℕ} (a : CoeffField d)
    (U : Set (Vec d)) (u : H1Function U) (f : Vec d → ℝ)
    (F : Vec d → Vec d) : Prop where
  flux_memL2 : MemVectorL2On U (fun x => matVecMul (a x) (u.grad x))
  source_memL2 : MemL2On U f
  forcing_memL2 : MemVectorL2On U F

namespace DivergenceFormL2DataOn

/-- `L²` data make each smooth weak-test pairing genuinely integrable. -/
theorem testable {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    {u : H1Function U} {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hdata : DivergenceFormL2DataOn a U u f F) (φ : WeakTestFunction U) :
    WeakDivergenceFormTestableOn a U u f F φ :=
  ⟨integrableOn_vecDot_weakTestFunction_grad hdata.flux_memL2 φ,
    integrableOn_mul_weakTestFunction hdata.source_memL2 φ,
    integrableOn_vecDot_weakTestFunction_grad hdata.forcing_memL2 φ⟩

/-- Uniform ellipticity supplies the missing `L²` flux field from the selected
`H¹` gradient. The source and divergence data retain their own explicit
membership hypotheses. -/
theorem of_isEllipticFieldOn {d : ℕ} {lam Lam : ℝ}
    {a : CoeffField d} {U : Set (Vec d)}
    {u : H1Function U} {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hf : MemL2On U f) (hF : MemVectorL2On U F) :
    DivergenceFormL2DataOn a U u f F where
  flux_memL2 :=
    memVectorL2On_matVecMul_of_isEllipticFieldOn hEll u.gradMemL2
  source_memL2 := hf
  forcing_memL2 := hF

/-- Transport `L²` weak-equation data across an almost-everywhere change of
coefficient representative. -/
theorem of_ae_eq_coeff {d : ℕ} {a b : CoeffField d}
    {U : Set (Vec d)} {u : H1Function U}
    {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hab : CoeffAEEqOn U a b)
    (hdata : DivergenceFormL2DataOn a U u f F) :
    DivergenceFormL2DataOn b U u f F where
  flux_memL2 := by
    intro i
    exact (hdata.flux_memL2 i).ae_eq
      ((hab.matVecMul u.grad).mono fun x hx =>
        congrArg (fun y : Vec d => y i) hx)
  source_memL2 := hdata.source_memL2
  forcing_memL2 := hdata.forcing_memL2

end DivergenceFormL2DataOn

/-- An `L²`-data weak solution.  This packages the data membership separately
from the equation, then projects to the fully safe smooth-test predicate. -/
structure IsWeakDivergenceFormL2SolutionOn {d : ℕ} (a : CoeffField d)
    (U : Set (Vec d)) (u : H1Function U) (f : Vec d → ℝ)
    (F : Vec d → Vec d) : Prop extends DivergenceFormL2DataOn a U u f F where
  identity : ∀ φ : WeakTestFunction U,
    ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (φ.grad x) =
      (∫ x in U, f x * φ x) - ∫ x in U, vecDot (F x) (φ.grad x)

namespace IsWeakDivergenceFormL2SolutionOn

/-- Forget the `L²` packaging while retaining the explicit integrability
required by the safe smooth-test formulation. -/
theorem toIsWeakDivergenceFormSolutionOn {d : ℕ} {a : CoeffField d}
    {U : Set (Vec d)} {u : H1Function U} {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hsol : IsWeakDivergenceFormL2SolutionOn a U u f F) :
    IsWeakDivergenceFormSolutionOn a U u f F := by
  intro φ
  exact ⟨hsol.toDivergenceFormL2DataOn.testable φ, hsol.identity φ⟩

end IsWeakDivergenceFormL2SolutionOn

/-- Term-by-term integrability for an `H¹₀` test representative. -/
structure WeakDivergenceFormH10TestableOn {d : ℕ} (a : CoeffField d)
    (U : Set (Vec d)) (u : H1Function U) (f : Vec d → ℝ)
    (F : Vec d → Vec d) (φ : H10Function U) : Prop where
  flux_integrable :
    IntegrableOn
      (fun x => vecDot (matVecMul (a x) (u.grad x))
        (φ.toH1Function.grad x)) U
  source_integrable : IntegrableOn (fun x => f x * φ.toH1Function x) U
  forcing_integrable :
    IntegrableOn (fun x => vecDot (F x) (φ.toH1Function.grad x)) U

/-- Safe all-`H¹₀` formulation of `-div (a ∇u) = f + div F`.

This is a distinct predicate from the smooth-test formulation.  The theorem
`IsWeakDivergenceFormL2SolutionOn.toH10SolutionOn` proves the implication for
the explicit `L²` tier; a bare smooth-test predicate has no such implication
in this module. -/
def IsWeakDivergenceFormH10SolutionOn {d : ℕ} (a : CoeffField d)
    (U : Set (Vec d)) (u : H1Function U) (f : Vec d → ℝ)
    (F : Vec d → Vec d) : Prop :=
  ∀ φ : H10Function U,
    WeakDivergenceFormH10TestableOn a U u f F φ ∧
      ∫ x in U, vecDot (matVecMul (a x) (u.grad x))
          (φ.toH1Function.grad x) =
        (∫ x in U, f x * φ.toH1Function x) -
          ∫ x in U, vecDot (F x) (φ.toH1Function.grad x)

namespace DivergenceFormL2DataOn

/-- `L²` data also make every `H¹₀` test pairing genuinely integrable. -/
theorem h10_testable {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    {u : H1Function U} {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hdata : DivergenceFormL2DataOn a U u f F) (φ : H10Function U) :
    WeakDivergenceFormH10TestableOn a U u f F φ :=
  ⟨integrableOn_vecDot_of_memVectorL2On hdata.flux_memL2
      φ.toH1Function.gradMemL2,
    integrableOn_mul_of_memL2On hdata.source_memL2
      φ.toH1Function.memL2,
    integrableOn_vecDot_of_memVectorL2On hdata.forcing_memL2
      φ.toH1Function.gradMemL2⟩

end DivergenceFormL2DataOn

namespace IsWeakDivergenceFormL2SolutionOn

/-- Extend an `L²`-data smooth-test solution to all representative-level
`H¹₀` tests.  The proof uses the actual supported smooth approximants stored
in the test function and continuity of the scalar `L²` pairing coordinate by
coordinate; it does not add the extension as an assumption. -/
theorem toH10SolutionOn {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    {u : H1Function U} {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hsol : IsWeakDivergenceFormL2SolutionOn a U u f F) :
    IsWeakDivergenceFormH10SolutionOn a U u f F := by
  intro φ
  refine ⟨hsol.toDivergenceFormL2DataOn.h10_testable φ, ?_⟩
  let φn : ℕ → WeakTestFunction U := fun n => φ.toWeakTestFunction n
  have hgrad : ∀ i : Fin d, Filter.Tendsto
      (fun n => eLpNorm (fun x => (φn n).grad x i - φ.toH1Function.grad x i)
        (2 : ℝ≥0∞) (volumeOn U)) Filter.atTop (nhds 0) := by
    intro i
    simpa only [φn, H10Function.toWeakTestFunction, WeakTestFunction.grad_apply,
      WeakTestFunction.partialDeriv] using! φ.tendsto_approx_grad i
  have hvalue : Filter.Tendsto
      (fun n => eLpNorm (fun x => φn n x - φ.toH1Function x)
        (2 : ℝ≥0∞) (volumeOn U)) Filter.atTop (nhds 0) := by
    simpa only [φn, H10Function.toWeakTestFunction_toFun] using φ.tendsto_approx
  have hflux := tendsto_setIntegral_vecDot_of_tendsto_coordinate_eLpNorm
    hsol.flux_memL2 (fun n => (φn n).grad_memVectorL2On)
    φ.toH1Function.gradMemL2 hgrad
  have hsource := tendsto_setIntegral_mul_of_tendsto_eLpNorm hsol.source_memL2
    (fun n => (φn n).memL2On) φ.toH1Function.memL2 hvalue
  have hforcing := tendsto_setIntegral_vecDot_of_tendsto_coordinate_eLpNorm
    hsol.forcing_memL2 (fun n => (φn n).grad_memVectorL2On)
    φ.toH1Function.gradMemL2 hgrad
  have hrhs := hsource.sub hforcing
  apply tendsto_nhds_unique hflux
  refine hrhs.congr' (Filter.Eventually.of_forall fun n => ?_)
  exact (hsol.identity (φn n)).symm

end IsWeakDivergenceFormL2SolutionOn

namespace IsWeakDivergenceFormH10SolutionOn

/-- Restrict an all-`H¹₀` weak solution to smooth compactly supported tests.
The open-domain hypothesis is exactly what lets a bundled smooth test be
turned into the canonical representative-level `H¹₀` test. -/
theorem toIsWeakDivergenceFormSolutionOn {d : ℕ} {a : CoeffField d}
    {U : Set (Vec d)} {u : H1Function U} {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hU : IsOpen U) (hsol : IsWeakDivergenceFormH10SolutionOn a U u f F) :
    IsWeakDivergenceFormSolutionOn a U u f F := by
  intro φ
  let φ10 : H10Function U :=
    H10Function.ofContDiff hU φ.contDiff φ.hasCompactSupport φ.tsupport_subset
  rcases hsol φ10 with ⟨htestable, hidentity⟩
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · simpa only [φ10, H10Function.ofContDiff_grad,
        WeakTestFunction.grad_apply, WeakTestFunction.partialDeriv] using!
        htestable.flux_integrable
    · simpa only [φ10, H10Function.ofContDiff_toFun] using htestable.source_integrable
    · simpa only [φ10, H10Function.ofContDiff_grad,
        WeakTestFunction.grad_apply, WeakTestFunction.partialDeriv] using!
        htestable.forcing_integrable
  · simpa only [φ10, H10Function.ofContDiff_toFun, H10Function.ofContDiff_grad,
      WeakTestFunction.grad_apply, WeakTestFunction.partialDeriv] using! hidentity

/-- Combine an all-`H¹₀` weak identity with explicit `L²` data to recover the
packaged smooth-test `L²` solution. -/
theorem toL2SolutionOn {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    {u : H1Function U} {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hU : IsOpen U) (hdata : DivergenceFormL2DataOn a U u f F)
    (hsol : IsWeakDivergenceFormH10SolutionOn a U u f F) :
    IsWeakDivergenceFormL2SolutionOn a U u f F where
  toDivergenceFormL2DataOn := hdata
  identity := fun φ => (hsol.toIsWeakDivergenceFormSolutionOn hU φ).2

end IsWeakDivergenceFormH10SolutionOn

/-- A weak solution is harmonic precisely when both lower-order data fields
are the zero fields. -/
abbrev IsWeakDivergenceFormHarmonicOn {d : ℕ} (a : CoeffField d)
    (U : Set (Vec d)) (u : H1Function U) : Prop :=
  IsWeakDivergenceFormSolutionOn a U u 0 0

/-- The adjoint weak equation uses the transpose coefficient field, without
assuming that coefficients are symmetric. -/
abbrev IsWeakAdjointDivergenceFormSolutionOn {d : ℕ} (a : CoeffField d)
    (U : Set (Vec d)) (u : H1Function U) (f : Vec d → ℝ)
    (F : Vec d → Vec d) : Prop :=
  IsWeakDivergenceFormSolutionOn (adjointCoeffField a) U u f F

namespace IsWeakDivergenceFormSolutionOn

/-- Transport a safe smooth-test weak solution across coefficient fields that
agree almost everywhere on the domain.  No symmetry is used. -/
theorem of_ae_eq_coeff {d : ℕ} {a b : CoeffField d} {U : Set (Vec d)}
    {u : H1Function U} {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hab : CoeffAEEqOn U a b)
    (hsol : IsWeakDivergenceFormSolutionOn a U u f F) :
    IsWeakDivergenceFormSolutionOn b U u f F := by
  intro φ
  rcases hsol φ with ⟨htestable, hidentity⟩
  have hflux_ae :
      (fun x => vecDot (matVecMul (a x) (u.grad x)) (φ.grad x)) =ᵐ[volumeOn U]
        fun x => vecDot (matVecMul (b x) (u.grad x)) (φ.grad x) := by
    filter_upwards [hab] with x hxab
    simp only [hxab]
  refine ⟨?_, ?_⟩
  · exact
      ⟨(integrableOn_congr_fun_ae hflux_ae).mp htestable.flux_integrable,
        htestable.source_integrable, htestable.forcing_integrable⟩
  · calc
      ∫ x in U, vecDot (matVecMul (b x) (u.grad x)) (φ.grad x) =
          ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (φ.grad x) :=
        integral_congr_ae hflux_ae.symm
      _ = (∫ x in U, f x * φ x) - ∫ x in U, vecDot (F x) (φ.grad x) :=
        hidentity

/-- Restrict a weak divergence-form solution to an open subset.

The restricted `H1Function` keeps the exact value and gradient
representatives. Every test supported in the smaller domain is reused in the
larger domain, and its value and gradient vanish off the smaller domain. -/
theorem restrict
    {d : ℕ} {a : CoeffField d} {U V : Set (Vec d)}
    {u : H1Function U} {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hsol : IsWeakDivergenceFormSolutionOn a U u f F)
    (hUOpen : IsOpen U) (hVOpen : IsOpen V) (hVU : V ⊆ U) :
    IsWeakDivergenceFormSolutionOn a V
      (u.restrict hVOpen hVU) f F := by
  intro φ
  let φU : WeakTestFunction U :=
    { toFun := φ.toFun
      contDiff := φ.contDiff
      hasCompactSupport := φ.hasCompactSupport
      tsupport_subset := φ.tsupport_subset.trans hVU }
  rcases hsol φU with ⟨htestable, hidentity⟩
  have hφzero :
      ∀ x ∈ U \ V, φ x = 0 := by
    intro x hx
    exact image_eq_zero_of_notMem_tsupport
      (fun hxt => hx.2 (φ.tsupport_subset hxt))
  have hgradzero :
      ∀ x ∈ U \ V, φ.grad x = 0 := by
    intro x hx
    have hxt : x ∉ tsupport φ.toFun :=
      fun hmem => hx.2 (φ.tsupport_subset hmem)
    funext i
    simp only [WeakTestFunction.grad_apply,
      WeakTestFunction.partialDeriv]
    rw [fderiv_of_notMem_tsupport ℝ hxt]
    simp
  have hflux :
      (∫ x in U,
        vecDot (matVecMul (a x) (u.grad x)) (φ.grad x)) =
      ∫ x in V,
        vecDot (matVecMul (a x) (u.grad x)) (φ.grad x) := by
    exact
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        hUOpen.measurableSet hVU fun x hx => by
          rw [hgradzero x hx]
          simp [vecDot]
  have hsource :
      (∫ x in U, f x * φ x) =
        ∫ x in V, f x * φ x := by
    exact
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        hUOpen.measurableSet hVU fun x hx => by
          rw [hφzero x hx, mul_zero]
  have hforcing :
      (∫ x in U, vecDot (F x) (φ.grad x)) =
        ∫ x in V, vecDot (F x) (φ.grad x) := by
    exact
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        hUOpen.measurableSet hVU fun x hx => by
          rw [hgradzero x hx]
          simp [vecDot]
  refine ⟨?_, ?_⟩
  · exact
      ⟨by
        simpa only [H1Function.restrict_grad] using!
          htestable.flux_integrable.mono_set hVU,
       htestable.source_integrable.mono_set hVU,
       htestable.forcing_integrable.mono_set hVU⟩
  · change
      (∫ x in U,
        vecDot (matVecMul (a x) (u.grad x)) (φ.grad x)) =
        (∫ x in U, f x * φ x) -
          ∫ x in U, vecDot (F x) (φ.grad x) at hidentity
    rw [hflux, hsource, hforcing] at hidentity
    simpa only [H1Function.restrict_grad] using hidentity

/-- Package a safe smooth-test weak solution into the `L²` tier using
ellipticity and explicit data membership. -/
theorem toL2SolutionOn_of_isEllipticFieldOn
    {d : ℕ} {lam Lam : ℝ} {a : CoeffField d} {U : Set (Vec d)}
    {u : H1Function U} {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hsol : IsWeakDivergenceFormSolutionOn a U u f F)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hf : MemL2On U f) (hF : MemVectorL2On U F) :
    IsWeakDivergenceFormL2SolutionOn a U u f F where
  toDivergenceFormL2DataOn :=
    DivergenceFormL2DataOn.of_isEllipticFieldOn hEll hf hF
  identity := fun φ => (hsol φ).2

/-- Under the explicit ellipticity and data hypotheses, a safe smooth-test
solution may be tested against every representative-level `H¹₀` function. -/
theorem toH10SolutionOn_of_isEllipticFieldOn
    {d : ℕ} {lam Lam : ℝ} {a : CoeffField d} {U : Set (Vec d)}
    {u : H1Function U} {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hsol : IsWeakDivergenceFormSolutionOn a U u f F)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hf : MemL2On U f) (hF : MemVectorL2On U F) :
    IsWeakDivergenceFormH10SolutionOn a U u f F :=
  (hsol.toL2SolutionOn_of_isEllipticFieldOn hEll hf hF).toH10SolutionOn

end IsWeakDivergenceFormSolutionOn

namespace IsWeakDivergenceFormL2SolutionOn

/-- Transport a packaged `L²` weak solution across an almost-everywhere
change of coefficient representative. -/
theorem of_ae_eq_coeff {d : ℕ} {a b : CoeffField d}
    {U : Set (Vec d)} {u : H1Function U}
    {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hab : CoeffAEEqOn U a b)
    (hsol : IsWeakDivergenceFormL2SolutionOn a U u f F) :
    IsWeakDivergenceFormL2SolutionOn b U u f F where
  toDivergenceFormL2DataOn :=
    hsol.toDivergenceFormL2DataOn.of_ae_eq_coeff hab
  identity := fun φ =>
    (hsol.toIsWeakDivergenceFormSolutionOn.of_ae_eq_coeff hab φ).2

end IsWeakDivergenceFormL2SolutionOn

namespace IsWeakDivergenceFormHarmonicOn

/-- A uniformly elliptic homogeneous weak solution may be tested against every
representative-level `H¹₀` function. -/
theorem toH10SolutionOn {d : ℕ} {lam Lam : ℝ}
    {a : CoeffField d} {U : Set (Vec d)} {u : H1Function U}
    (hsol : IsWeakDivergenceFormHarmonicOn a U u)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    IsWeakDivergenceFormH10SolutionOn a U u 0 0 :=
  hsol.toH10SolutionOn_of_isEllipticFieldOn hEll
    MeasureTheory.MemLp.zero (by
      intro i
      simpa only [Pi.zero_apply] using!
        (MeasureTheory.MemLp.zero :
          MemL2On U (0 : Vec d → ℝ)))

end IsWeakDivergenceFormHarmonicOn

end PDE
