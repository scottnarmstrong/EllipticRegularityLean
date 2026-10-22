module

public import PDEFoundation.Analysis.Newtonian.Potential.DerivDecay
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fubini for the Newton kernel against compactly supported test functions

For continuous compactly supported `a`, `b`, the function `(x, y) ↦ E_i(x - y) a(y) b(x)` is
integrable on the product, and the order of integration can be exchanged.
-/

@[expose] public section

open MeasureTheory Set
open scoped Convolution

namespace PDE.NewtonWeakType

noncomputable section

variable {d : ℕ}

theorem newtonKernel_neg (z : Vec d) : newtonKernel (-z) = -newtonKernel z := by
  rw [newtonKernel_eq, newtonKernel_eq, vecEuclideanNorm_neg]
  simp

theorem integrable_newtonKernel_mul_prod (hd : 0 < d) (i : Fin d) {a b : Vec d → ℝ}
    (ha : Continuous a) (hac : HasCompactSupport a) (hb : Continuous b)
    (hbc : HasCompactSupport b) {R : ℝ} (hR : 0 < R)
    (hsa : ∀ y, a y ≠ 0 → vecEuclideanNorm y < R)
    (hsb : ∀ x, b x ≠ 0 → vecEuclideanNorm x < R) :
    Integrable (fun p : Vec d × Vec d => newtonKernel (p.1 - p.2) i * a p.2 * b p.1)
      (volume.prod volume) := by
  set S : Set (Vec d) := euclideanBall 0 (2 * R) with hS
  have hSm : MeasurableSet S := measurableSet_euclideanBall _ _
  have hK' : Integrable (S.indicator (fun z : Vec d => newtonKernel z i)) volume :=
    (integrable_indicator_iff hSm).mpr
      (integrableOn_euclideanBall_newtonKernel_apply hd i (by linarith))
  have ha_int : Integrable a volume := ha.integrable_of_hasCompactSupport hac
  have hconv := Integrable.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ)
    (μ := (volume : Measure (Vec d))) (ν := (volume : Measure (Vec d))) ha_int hK'
  obtain ⟨C, hC⟩ := hb.bounded_above_of_compact_support hbc
  have hbm : AEStronglyMeasurable (fun p : Vec d × Vec d => b p.1)
      ((volume : Measure (Vec d)).prod volume) :=
    (hb.comp continuous_fst).aestronglyMeasurable
  have := hconv.bdd_mul hbm (Filter.Eventually.of_forall fun p => hC p.1)
  refine this.congr (Filter.Eventually.of_forall fun p => ?_)
  by_cases h1 : a p.2 = 0
  · simp [h1]
  by_cases h2 : b p.1 = 0
  · simp [h2]
  have hy := hsa _ h1
  have hx := hsb _ h2
  have hmem : p.1 - p.2 ∈ S := by
    rw [hS, mem_euclideanBall_iff_vecEuclideanNorm_lt (by linarith), sub_zero]
    have := vecEuclideanNorm_add_le (p.1) (-p.2)
    rw [vecEuclideanNorm_neg] at this
    simp only [← sub_eq_add_neg] at this
    linarith
  simp only [ContinuousLinearMap.mul_apply', indicator_of_mem hmem]
  ring

/-- Exchange of the order of integration for the Newton kernel. -/
theorem integral_newtonKernel_swap (hd : 0 < d) (i : Fin d) {a b : Vec d → ℝ}
    (ha : Continuous a) (hac : HasCompactSupport a) (hb : Continuous b)
    (hbc : HasCompactSupport b) {R : ℝ} (hR : 0 < R)
    (hsa : ∀ y, a y ≠ 0 → vecEuclideanNorm y < R)
    (hsb : ∀ x, b x ≠ 0 → vecEuclideanNorm x < R) :
    (∫ x, (∫ y, newtonKernel (x - y) i * a y) * b x) =
      ∫ y, a y * ∫ x, newtonKernel (x - y) i * b x := by
  have hint := integrable_newtonKernel_mul_prod hd i ha hac hb hbc hR hsa hsb
  have h1 : (∫ x, (∫ y, newtonKernel (x - y) i * a y) * b x) =
      ∫ x, ∫ y, newtonKernel (x - y) i * a y * b x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [← integral_mul_const]
  have h2 : (∫ y, a y * ∫ x, newtonKernel (x - y) i * b x) =
      ∫ y, ∫ x, newtonKernel (x - y) i * a y * b x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring
  rw [h1, h2]
  exact integral_integral_swap (f := fun x y => newtonKernel (x - y) i * a y * b x) hint

theorem integrable_integral_newtonKernel_mul (hd : 0 < d) (i : Fin d) {a b : Vec d → ℝ}
    (ha : Continuous a) (hac : HasCompactSupport a) (hb : Continuous b)
    (hbc : HasCompactSupport b) {R : ℝ} (hR : 0 < R)
    (hsa : ∀ y, a y ≠ 0 → vecEuclideanNorm y < R)
    (hsb : ∀ x, b x ≠ 0 → vecEuclideanNorm x < R) :
    Integrable (fun x => (∫ y, newtonKernel (x - y) i * a y) * b x) volume := by
  have hint := integrable_newtonKernel_mul_prod hd i ha hac hb hbc hR hsa hsb
  have := hint.integral_prod_left
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [← integral_mul_const]

end

end PDE.NewtonWeakType
