module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Power-weight integrals for the Hardy inequality

Exact `lintegral` evaluations of `t ↦ t ^ s` over `(0, r]` (for `s > -1`) and over `(c, ∞)`
(for `s < -1`), in the `ofReal` form used by the weighted Hölder proof of Hardy's inequality.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set
open scoped ENNReal

/-- `∫_0^r t^s dt = r^(s+1)/(s+1)` for `s > -1`, as a `lintegral`. -/
theorem lintegral_Ioc_rpow {s : ℝ} (hs : -1 < s) {r : ℝ} (hr : 0 < r) :
    ∫⁻ t in Ioc 0 r, ENNReal.ofReal (t ^ s) = ENNReal.ofReal (r ^ (s + 1) / (s + 1)) := by
  have hint : IntegrableOn (fun t : ℝ => t ^ s) (Ioc 0 r) :=
    (intervalIntegral.intervalIntegrable_rpow' hs).1
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    rw [← intervalIntegral.integral_of_le hr.le, integral_rpow (Or.inl hs)]
    rw [Real.zero_rpow (by linarith : s + 1 ≠ 0), sub_zero]
  · refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun t ht => ?_)
    exact Real.rpow_nonneg ht.1.le _

/-- `∫_c^∞ r^s dr = -c^(s+1)/(s+1)` for `s < -1`, as a `lintegral`. -/
theorem lintegral_Ioi_rpow {s : ℝ} (hs : s < -1) {c : ℝ} (hc : 0 < c) :
    ∫⁻ r in Ioi c, ENNReal.ofReal (r ^ s) = ENNReal.ofReal (-c ^ (s + 1) / (s + 1)) := by
  rw [← integral_Ioi_rpow_of_lt hs hc,
    ← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt hs hc)]
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
  exact Real.rpow_nonneg (hc.le.trans ht.le) _

end PDE.TraceLane
