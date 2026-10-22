module

public import PDEFoundation.Sobolev.Trace.Model.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.InnerProductSpace.NormPow
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Calculus on the half-space model

Basic facts used by the trace estimates: openness and measurability of the half-spaces,
differentiability of a `C¹`-up-to-the-boundary function on the open half-space, the derivatives of
its vertical and horizontal slices, and a fundamental-theorem-of-calculus bound in `lintegral`
form.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology
open scoped ENNReal

variable {n : ℕ}

theorem mem_upperHalf_iff {z : Vec n × ℝ} : z ∈ upperHalf n ↔ 0 < z.2 := by
  simp [upperHalf]

theorem mem_closedUpperHalf_iff {z : Vec n × ℝ} : z ∈ closedUpperHalf n ↔ 0 ≤ z.2 := by
  simp [closedUpperHalf]

theorem trace_isOpen_upperHalf : IsOpen (upperHalf n) := isOpen_univ.prod isOpen_Ioi

theorem trace_measurableSet_upperHalf : MeasurableSet (upperHalf n) :=
  MeasurableSet.univ.prod measurableSet_Ioi

theorem upperHalf_subset_closed : upperHalf n ⊆ closedUpperHalf n :=
  prod_mono subset_rfl Ioi_subset_Ici_self

theorem uniqueDiffOn_closedUpperHalf : UniqueDiffOn ℝ (closedUpperHalf n) := by
  refine uniqueDiffOn_convex (convex_univ.prod (convex_Ici 0)) ?_
  refine ⟨((0 : Vec n), (1 : ℝ)), ?_⟩
  rw [closedUpperHalf, interior_prod_eq, interior_univ, interior_Ici]
  simp

theorem closedUpperHalf_mem_nhds {z : Vec n × ℝ} (hz : 0 < z.2) :
    closedUpperHalf n ∈ 𝓝 z :=
  Filter.mem_of_superset (trace_isOpen_upperHalf.mem_nhds (mem_upperHalf_iff.2 hz))
    upperHalf_subset_closed

section Smooth

variable {v : Vec n × ℝ → ℝ} (hv : ContDiffOn ℝ 1 v (closedUpperHalf n))
include hv

theorem differentiableAt_of_pos {z : Vec n × ℝ} (hz : 0 < z.2) : DifferentiableAt ℝ v z :=
  (hv.differentiableOn one_ne_zero).differentiableAt (closedUpperHalf_mem_nhds hz)

theorem hasFDerivAt_of_pos {z : Vec n × ℝ} (hz : 0 < z.2) :
    HasFDerivAt v (fderiv ℝ v z) z :=
  (differentiableAt_of_pos hv hz).hasFDerivAt

theorem continuousOn_fderiv_upper : ContinuousOn (fderiv ℝ v) (upperHalf n) := by
  have h := hv.continuousOn_fderivWithin uniqueDiffOn_closedUpperHalf le_rfl
  refine (h.mono upperHalf_subset_closed).congr ?_
  intro z hz
  exact (fderivWithin_of_mem_nhds (closedUpperHalf_mem_nhds (mem_upperHalf_iff.1 hz))).symm

/-- The vertical slice of `v` has derivative `∂ₜ v` at positive heights. -/
theorem hasDerivAt_slice (x' : Vec n) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => v (x', s)) (normDeriv v (x', t)) t := by
  have hc : HasDerivAt (fun s : ℝ => ((x' : Vec n), s)) ((0 : Vec n), (1 : ℝ)) t :=
    (hasDerivAt_const t x').prodMk (hasDerivAt_id t)
  exact (hasFDerivAt_of_pos hv (z := (x', t)) ht).comp_hasDerivAt t hc

/-- The horizontal slice at height `h > 0` along the segment `x' + θ k`. -/
theorem hasDerivAt_segment (x' k : Vec n) {h : ℝ} (hh : 0 < h) (θ : ℝ) :
    HasDerivAt (fun s : ℝ => v (x' + s • k, h)) (fderiv ℝ v (x' + θ • k, h) (k, 0)) θ := by
  have hc : HasDerivAt (fun s : ℝ => (x' + s • k, h)) (k, (0 : ℝ)) θ := by
    have h1 : HasDerivAt (fun s : ℝ => x' + s • k) k θ := by
      simpa using ((hasDerivAt_id θ).smul_const k).const_add x'
    exact h1.prodMk (hasDerivAt_const θ h)
  exact (hasFDerivAt_of_pos hv (z := (x' + θ • k, h)) hh).comp_hasDerivAt θ hc

theorem continuousOn_slice (x' : Vec n) : ContinuousOn (fun s : ℝ => v (x', s)) (Ici 0) := by
  refine hv.continuousOn.comp (Continuous.continuousOn (by fun_prop)) ?_
  intro s hs
  exact mem_closedUpperHalf_iff.2 hs

/-- The derivative of the vertical slice, extended continuously to the boundary. -/
theorem continuousOn_slice_deriv (x' : Vec n) :
    ContinuousOn (fun s : ℝ => fderivWithin ℝ v (closedUpperHalf n) (x', s) (0, 1)) (Ici 0) := by
  have h := hv.continuousOn_fderivWithin uniqueDiffOn_closedUpperHalf le_rfl
  have h2 : ContinuousOn (fun s : ℝ => fderivWithin ℝ v (closedUpperHalf n) (x', s))
      (Ici 0) :=
    h.comp (Continuous.continuousOn (by fun_prop)) (fun s hs => mem_closedUpperHalf_iff.2 hs)
  exact (ContinuousLinearMap.apply ℝ ℝ ((0 : Vec n), (1 : ℝ))).continuous.comp_continuousOn h2

omit hv in
theorem slice_deriv_eq (x' : Vec n) {s : ℝ} (hs : 0 < s) :
    fderivWithin ℝ v (closedUpperHalf n) (x', s) (0, 1) = normDeriv v (x', s) := by
  rw [fderivWithin_of_mem_nhds (closedUpperHalf_mem_nhds (z := (x', s)) hs)]
  rfl

end Smooth

/-- Fundamental theorem of calculus, `lintegral` form: if `u` is continuous on `[a, b]` with
derivative `u'` on `(a, b)` and `u'` is interval integrable, then
`|u b - u a| ≤ ∫_{(a,b]} |u'|`. -/
theorem ofReal_abs_sub_le_lintegral {u u' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hu : ContinuousOn u (Icc a b)) (hd : ∀ t ∈ Ioo a b, HasDerivAt u (u' t) t)
    (hi : IntervalIntegrable u' volume a b) :
    ENNReal.ofReal |u b - u a| ≤ ∫⁻ t in Ioc a b, ENNReal.ofReal |u' t| := by
  have h1 : ∫ t in a..b, u' t = u b - u a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hu hd hi
  have h2 : |u b - u a| ≤ ∫ t in a..b, |u' t| := by
    rw [← h1]
    exact intervalIntegral.abs_integral_le_integral_abs hab
  have h3 : IntegrableOn (fun t => |u' t|) (Ioc a b) := by
    have := hi.abs
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le hab] at this
  calc ENNReal.ofReal |u b - u a| ≤ ENNReal.ofReal (∫ t in a..b, |u' t|) :=
        ENNReal.ofReal_le_ofReal h2
    _ = ∫⁻ t in Ioc a b, ENNReal.ofReal |u' t| := by
        rw [intervalIntegral.integral_of_le hab,
          ofReal_integral_eq_lintegral_ofReal h3 (Filter.Eventually.of_forall fun t => abs_nonneg _)]

end PDE.TraceLane
