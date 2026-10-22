module

public import PDEFoundation.Ambient.CoefficientField
public import PDEFoundation.Sobolev.H1.Pairing

/-!
# `L²` fluxes of uniformly elliptic coefficient fields

The coefficient-field convention supplies a measurable zero extension and a
pointwise bound by the explicit upper ellipticity parameter `Lam`.  This file
turns that information into the coordinatewise native-vector `L²` fact needed
to form divergence-form weak pairings.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

/-- Multiplication by a measurable uniformly elliptic coefficient field sends
native coordinatewise `L²(U)` vector fields to native coordinatewise `L²(U)`
vector fields.  The bound used for every matrix entry is the explicit upper
ellipticity parameter `Lam`; no symmetry is assumed. -/
theorem memVectorL2On_matVecMul_of_isEllipticFieldOn {d : ℕ} {lam Lam : ℝ}
    {U : Set (Vec d)} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam U a)
    {f : Vec d → Vec d} (hf : MemVectorL2On U f) :
    MemVectorL2On U (fun x => matVecMul (a x) (f x)) := by
  classical
  intro i
  have hsum : MemLpOn U (2 : ℝ≥0∞)
      (fun x => ∑ j : Fin d, a x i j * f x j) := by
    refine MeasureTheory.memLp_finsetSum
      (s := Finset.univ)
      (f := fun j : Fin d => fun x : Vec d => a x i j * f x j) ?_
    intro j _
    have hfj : MemLpOn U (2 : ℝ≥0∞) (fun x => f x j) := hf j
    let coeff : Vec d → ℝ := fun x => if x ∈ U then a x i j else 0
    have hcoeff_meas : Measurable coeff := by
      simpa only [coeff] using
        (measurable_pi_iff.mp (measurable_pi_iff.mp hEll.1 i) j)
    have hmem : ∀ᵐ x ∂ volumeOn U, x ∈ U := by
      exact
        (MeasureTheory.ae_restrict_iff'
          (measurableSet_of_isEllipticFieldOn hEll)).2
          (Filter.Eventually.of_forall fun x hx => hx)
    have hcoeff_ae : AEMeasurable (fun x => a x i j) (volumeOn U) := by
      refine hcoeff_meas.aemeasurable.congr ?_
      filter_upwards [hmem] with x hx
      simp only [coeff, hx, ↓reduceIte]
    have hterm_meas : AEStronglyMeasurable (fun x => a x i j * f x j) (volumeOn U) :=
      hcoeff_ae.aestronglyMeasurable.mul hfj.aestronglyMeasurable
    have hbound : ∀ᵐ x ∂ volumeOn U, ‖a x i j * f x j‖ ≤ Lam * ‖f x j‖ := by
      filter_upwards [hmem] with x hx
      have hcoeff_le : |a x i j| ≤ Lam :=
        abs_apply_le_of_isEllipticFieldOn hEll hx i j
      calc
        ‖a x i j * f x j‖ = |a x i j| * ‖f x j‖ := by
          rw [norm_mul, Real.norm_eq_abs]
        _ ≤ Lam * ‖f x j‖ :=
          mul_le_mul_of_nonneg_right hcoeff_le (norm_nonneg _)
    exact MeasureTheory.MemLp.of_le_mul hfj hterm_meas hbound
  simpa only [matVecMul] using hsum

/-- The coefficient energy of an `L²` native-vector field is integrable.

The coefficient field need not be symmetric. Its explicit upper ellipticity
bound supplies `L²` integrability of the flux, and Hölder gives
integrability of the pairing. -/
theorem integrableOn_coefficientEnergy_of_isEllipticFieldOn
    {d : ℕ} {lam Lam : ℝ} {U : Set (Vec d)}
    {a : CoeffField d} {f : Vec d → Vec d}
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hf : MemVectorL2On U f) :
    IntegrableOn
      (fun x => vecDot (f x) (matVecMul (a x) (f x))) U := by
  have hflux :
      MemVectorL2On U (fun x => matVecMul (a x) (f x)) :=
    memVectorL2On_matVecMul_of_isEllipticFieldOn hEll hf
  exact integrableOn_vecDot_of_memVectorL2On hf hflux

/-- Integrated coercivity on a measurable subdomain, normalized by the
explicit lower ellipticity parameter.

Every dependency is visible: `S` must be measurable and lie in the
ellipticity domain, `f` must belong to native-vector `L²(U)`, and division
uses the displayed hypothesis `0 < lam`. -/
theorem setIntegral_vecNormSq_le_coefficientEnergy_div
    {d : ℕ} {lam Lam : ℝ} {U S : Set (Vec d)}
    {a : CoeffField d} {f : Vec d → Vec d}
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hf : MemVectorL2On U f)
    (hSmeas : MeasurableSet S) (hSU : S ⊆ U)
    (hlam : 0 < lam) :
    ∫ x in S, vecNormSq (f x) ≤
      (∫ x in S, vecDot (f x) (matVecMul (a x) (f x))) / lam := by
  have hgradU : IntegrableOn (fun x => vecNormSq (f x)) U :=
    integrableOn_vecNormSq_of_memVectorL2On hf
  have henergyU :
      IntegrableOn
        (fun x => vecDot (f x) (matVecMul (a x) (f x))) U :=
    integrableOn_coefficientEnergy_of_isEllipticFieldOn hEll hf
  have hleft :
      IntegrableOn (fun x => lam * vecNormSq (f x)) S :=
    (hgradU.mono_set hSU).const_mul lam
  have henergy :
      IntegrableOn
        (fun x => vecDot (f x) (matVecMul (a x) (f x))) S :=
    henergyU.mono_set hSU
  have hcoerciveIntegral :
      (∫ x in S, lam * vecNormSq (f x)) ≤
        ∫ x in S, vecDot (f x) (matVecMul (a x) (f x)) := by
    exact setIntegral_mono_on hleft henergy hSmeas fun x hx =>
      (hEll.elliptic (hSU hx)).coercive (f x)
  have hcoercive :
      lam * (∫ x in S, vecNormSq (f x)) ≤
        ∫ x in S, vecDot (f x) (matVecMul (a x) (f x)) := by
    calc
      lam * (∫ x in S, vecNormSq (f x)) =
          ∫ x in S, lam * vecNormSq (f x) := by
        symm
        exact integral_const_mul lam _
      _ ≤ ∫ x in S,
          vecDot (f x) (matVecMul (a x) (f x)) :=
        hcoerciveIntegral
  apply (le_div_iff₀ hlam).2
  simpa only [mul_comm] using hcoercive

end PDE
