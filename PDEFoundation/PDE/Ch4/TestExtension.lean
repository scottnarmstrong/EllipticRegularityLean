module

public import PDEFoundation.PDE.DGNM.Bridge
public import PDEFoundation.Sobolev.Ch4.PositiveDensity
public import PDEFoundation.Sobolev.Ch4.LipschitzH1

/-!
# Extending weak inequalities to `H¹₀`, Lipschitz and compactly supported tests, on arbitrary
# bounded open sets

The convex-domain bridge `PDE.DGNM.subharmonic_test` etc. rests on the positivity-preserving
density of nonnegative `H¹₀` functions, which the repository proves on convex domains.  Here the
same statements are proved on an arbitrary bounded open set `U` (annuli, `B_R ∖ closedBall`, ...),
using `Ch4Infra.exists_nonnegative_supportedSmoothApproximation_open`.

For homogeneous *solutions* the existing bridge never used convexity, only measurability of `U`;
`solution_test_open` restates it for an arbitrary open set.
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory

namespace PDE.Ch4Infra

variable {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}

/-- An `L²`-data smooth-test subsolution on a bounded open set extends to every nonnegative
`H¹₀` test. -/
theorem l2Subsolution_toH10_open {u : H1Function U} {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hsub : IsWeakDivergenceFormL2SubsolutionOn a U u f F) (hU : IsOpen U)
    (hfin : volume U ≠ ⊤) : IsWeakDivergenceFormH10SubsolutionOn a U u f F := by
  intro φ hφ
  refine ⟨hsub.toDivergenceFormL2DataOn.h10_testable φ, ?_⟩
  obtain ⟨hpositive, hpositiveNonnegative⟩ :=
    exists_nonnegative_supportedSmoothApproximation_open hU hfin
      (u := φ.toH1Function) φ.supportedSmoothApproximation hφ
  let φn : ℕ → WeakTestFunction U := fun n => hpositive.toWeakTestFunction n
  have hφnNonnegative : ∀ n, (φn n).Nonnegative := fun n x => hpositiveNonnegative n x
  have hgrad : ∀ i : Fin d, Filter.Tendsto
      (fun n => eLpNorm (fun x => (φn n).grad x i - φ.toH1Function.grad x i)
        (2 : ℝ≥0∞) (volumeOn U)) Filter.atTop (nhds 0) := by
    intro i
    simpa only [φn, H1Function.SupportedSmoothApproximation.toWeakTestFunction,
      WeakTestFunction.grad_apply, WeakTestFunction.partialDeriv] using! hpositive.tendsto_grad i
  have hvalue : Filter.Tendsto
      (fun n => eLpNorm (fun x => φn n x - φ.toH1Function x) (2 : ℝ≥0∞) (volumeOn U))
      Filter.atTop (nhds 0) := by
    simpa only [φn, H1Function.SupportedSmoothApproximation.toWeakTestFunction] using!
      hpositive.tendsto_value
  have hflux := tendsto_setIntegral_vecDot_of_tendsto_coordinate_eLpNorm hsub.flux_memL2
    (fun n => (φn n).grad_memVectorL2On) φ.toH1Function.gradMemL2 hgrad
  have hsource := tendsto_setIntegral_mul_of_tendsto_eLpNorm hsub.source_memL2
    (fun n => (φn n).memL2On) φ.toH1Function.memL2 hvalue
  have hforcing := tendsto_setIntegral_vecDot_of_tendsto_coordinate_eLpNorm hsub.forcing_memL2
    (fun n => (φn n).grad_memVectorL2On) φ.toH1Function.gradMemL2 hgrad
  exact le_of_tendsto_of_tendsto' hflux (hsource.sub hforcing)
    (fun n => hsub.inequality (φn n) (hφnNonnegative n))

/-- An `L²`-data smooth-test supersolution on a bounded open set extends to every nonnegative
`H¹₀` test. -/
theorem l2Supersolution_toH10_open {u : H1Function U} {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hsuper : IsWeakDivergenceFormL2SupersolutionOn a U u f F) (hU : IsOpen U)
    (hfin : volume U ≠ ⊤) : IsWeakDivergenceFormH10SupersolutionOn a U u f F := by
  intro φ hφ
  refine ⟨hsuper.toDivergenceFormL2DataOn.h10_testable φ, ?_⟩
  obtain ⟨hpositive, hpositiveNonnegative⟩ :=
    exists_nonnegative_supportedSmoothApproximation_open hU hfin
      (u := φ.toH1Function) φ.supportedSmoothApproximation hφ
  let φn : ℕ → WeakTestFunction U := fun n => hpositive.toWeakTestFunction n
  have hφnNonnegative : ∀ n, (φn n).Nonnegative := fun n x => hpositiveNonnegative n x
  have hgrad : ∀ i : Fin d, Filter.Tendsto
      (fun n => eLpNorm (fun x => (φn n).grad x i - φ.toH1Function.grad x i)
        (2 : ℝ≥0∞) (volumeOn U)) Filter.atTop (nhds 0) := by
    intro i
    simpa only [φn, H1Function.SupportedSmoothApproximation.toWeakTestFunction,
      WeakTestFunction.grad_apply, WeakTestFunction.partialDeriv] using! hpositive.tendsto_grad i
  have hvalue : Filter.Tendsto
      (fun n => eLpNorm (fun x => φn n x - φ.toH1Function x) (2 : ℝ≥0∞) (volumeOn U))
      Filter.atTop (nhds 0) := by
    simpa only [φn, H1Function.SupportedSmoothApproximation.toWeakTestFunction] using!
      hpositive.tendsto_value
  have hflux := tendsto_setIntegral_vecDot_of_tendsto_coordinate_eLpNorm hsuper.flux_memL2
    (fun n => (φn n).grad_memVectorL2On) φ.toH1Function.gradMemL2 hgrad
  have hsource := tendsto_setIntegral_mul_of_tendsto_eLpNorm hsuper.source_memL2
    (fun n => (φn n).memL2On) φ.toH1Function.memL2 hvalue
  have hforcing := tendsto_setIntegral_vecDot_of_tendsto_coordinate_eLpNorm hsuper.forcing_memL2
    (fun n => (φn n).grad_memVectorL2On) φ.toH1Function.gradMemL2 hgrad
  exact le_of_tendsto_of_tendsto' (hsource.sub hforcing) hflux
    (fun n => hsuper.inequality (φn n) (hφnNonnegative n))

variable {Λ : ℝ}

private theorem zero_l2data {b : CoeffField d} {u : H1Function U}
    (hb : IsEllipticFieldOn 1 Λ U b) : DivergenceFormL2DataOn b U u 0 0 :=
  DivergenceFormL2DataOn.of_isEllipticFieldOn hb MeasureTheory.MemLp.zero
    (by intro i; simpa only [Pi.zero_apply] using!
      (MeasureTheory.MemLp.zero : MemL2On U (0 : Vec d → ℝ)))

/-- **Subharmonic test bridge on a bounded open set.**  A smooth-test subharmonic function with
a.e.-measurable elliptic coefficients satisfies `∫ a∇u·∇φ ≤ 0` (integrable integrand) for every
a.e.-nonnegative `H¹₀` test. -/
theorem subharmonic_test_open (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsub : IsWeakDivergenceFormSubharmonicOn a U u)
    (φ : H10Function U) (hφ : φ.AENonnegative) :
    IntegrableOn (fun x => vecDot (matVecMul (a x) (u.grad x)) (φ.toH1Function.grad x)) U ∧
      ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (φ.toH1Function.grad x) ≤ 0 := by
  obtain ⟨b, hb, hab⟩ := exists_isEllipticFieldOn_coeffAEEqOn hU.measurableSet ha hEll
  have hsubB := IsWeakDivergenceFormSubsolutionOn.of_ae_eq_coeff hab hsub
  have hH10B := l2Subsolution_toH10_open (hsubB.toL2SubsolutionOn (zero_l2data hb)) hU hfin
  have hH10A := IsWeakDivergenceFormH10SubsolutionOn.of_ae_eq_coeff hab.symm hH10B
  exact DGNM.H10Subharmonic.test hH10A φ hφ

/-- **Superharmonic test bridge on a bounded open set.** -/
theorem superharmonic_test_open (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsuper : IsWeakDivergenceFormSuperharmonicOn a U u)
    (φ : H10Function U) (hφ : φ.AENonnegative) :
    IntegrableOn (fun x => vecDot (matVecMul (a x) (u.grad x)) (φ.toH1Function.grad x)) U ∧
      0 ≤ ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (φ.toH1Function.grad x) := by
  obtain ⟨b, hb, hab⟩ := exists_isEllipticFieldOn_coeffAEEqOn hU.measurableSet ha hEll
  have hsuperB := IsWeakDivergenceFormSupersolutionOn.of_ae_eq_coeff hab hsuper
  have hH10B := l2Supersolution_toH10_open (hsuperB.toL2SupersolutionOn (zero_l2data hb)) hU hfin
  have hH10A := IsWeakDivergenceFormH10SupersolutionOn.of_ae_eq_coeff hab.symm hH10B
  exact DGNM.H10Superharmonic.test hH10A φ hφ

/-- **Solution test bridge on an arbitrary open set** (no boundedness or convexity needed). -/
theorem solution_test_open (hU : IsOpen U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsol : IsWeakDivergenceFormSolutionOn a U u (0 : Vec d → ℝ) 0)
    (φ : H10Function U) :
    IntegrableOn (fun x => vecDot (matVecMul (a x) (u.grad x)) (φ.toH1Function.grad x)) U ∧
      ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (φ.toH1Function.grad x) = 0 := by
  obtain ⟨b, hb, hab⟩ := exists_isEllipticFieldOn_coeffAEEqOn hU.measurableSet ha hEll
  have hsolB := IsWeakDivergenceFormSolutionOn.of_ae_eq_coeff hab hsol
  have hH10B := IsWeakDivergenceFormHarmonicOn.toH10SolutionOn hsolB hb
  have hH10A : IsWeakDivergenceFormH10SolutionOn a U u (0 : Vec d → ℝ) 0 := by
    intro φ
    rcases hH10B φ with ⟨htestable, hidentity⟩
    have hfluxAE :
        (fun x => vecDot (matVecMul (b x) (u.grad x)) (φ.toH1Function.grad x)) =ᵐ[volumeOn U]
        fun x => vecDot (matVecMul (a x) (u.grad x)) (φ.toH1Function.grad x) := by
      filter_upwards [hab] with x hx
      rw [hx]
    refine ⟨⟨(integrableOn_congr_fun_ae hfluxAE).mp htestable.flux_integrable,
      htestable.source_integrable, htestable.forcing_integrable⟩, ?_⟩
    rw [← integral_congr_ae hfluxAE]
    exact hidentity
  exact DGNM.H10Solution.test hH10A φ

end PDE.Ch4Infra
