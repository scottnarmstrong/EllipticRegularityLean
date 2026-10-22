module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Mean versus median in `L^r` of a probability space

On a probability space, the `L^r` distance of `f` to its mean is at most twice the `L^r`
distance of `f` to any constant, `r ≥ 1`.  This is the Hölder step in Step 3 of the
Sobolev--Poincaré inequality on normalized convex domains.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE

/-- `‖f - ∫ f‖_{L^r(ν)} ≤ 2 ‖f - m‖_{L^r(ν)}` for a probability measure `ν`, `r ≥ 1`. -/
theorem eLpNorm_sub_integral_le {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {r : ℝ≥0∞} (hr : 1 ≤ r) {f : α → ℝ} (hf : MemLp f r ν) (m : ℝ) :
    eLpNorm (fun x => f x - ∫ y, f y ∂ν) r ν ≤ 2 * eLpNorm (fun x => f x - m) r ν := by
  have hint : Integrable f ν := hf.integrable hr
  have hfm : MemLp (fun x => f x - m) r ν := hf.sub (memLp_const m)
  set c : ℝ := m - ∫ y, f y ∂ν with hcdef
  have hdecomp : (fun x => f x - ∫ y, f y ∂ν) = (fun x => f x - m) + (fun _ => c) := by
    funext x
    simp only [Pi.add_apply, hcdef]
    ring
  have hr0 : r ≠ 0 := (zero_lt_one.trans_le hr).ne'
  have hconst : eLpNorm (fun _ : α => c) r ν = ‖c‖ₑ := by
    rw [eLpNorm_const c hr0 (IsProbabilityMeasure.ne_zero ν), measure_univ, ENNReal.one_rpow,
      mul_one]
  have hcint : ∫ y, (f y - m) ∂ν = -c := by
    rw [integral_sub hint (integrable_const m), integral_const]
    simp [hcdef]
  have hc : ‖c‖ₑ ≤ eLpNorm (fun x => f x - m) r ν := by
    calc ‖c‖ₑ = ‖∫ y, (f y - m) ∂ν‖ₑ := by rw [hcint, enorm_neg]
      _ ≤ ∫⁻ y, ‖f y - m‖ₑ ∂ν := enorm_integral_le_lintegral_enorm _
      _ = eLpNorm (fun x => f x - m) 1 ν :=
          (eLpNorm_one_eq_lintegral_enorm hfm.aestronglyMeasurable).symm
      _ ≤ eLpNorm (fun x => f x - m) r ν :=
          eLpNorm_le_eLpNorm_of_exponent_le hr
  rw [hdecomp]
  calc eLpNorm ((fun x => f x - m) + fun _ => c) r ν
      ≤ eLpNorm (fun x => f x - m) r ν + eLpNorm (fun _ : α => c) r ν :=
        eLpNorm_add_le hr
    _ ≤ eLpNorm (fun x => f x - m) r ν + eLpNorm (fun x => f x - m) r ν := by
        rw [hconst]; gcongr
    _ = 2 * eLpNorm (fun x => f x - m) r ν := (two_mul _).symm

end PDE
