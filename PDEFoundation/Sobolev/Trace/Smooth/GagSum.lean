module

public import PDEFoundation.Sobolev.Trace.Smooth.Scalar
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Subadditivity of the Gagliardo seminorm

The Gagliardo seminorm of a sum is bounded by the sum of the seminorms (Minkowski in
`L^p(μ ⊗ μ)` for the function `(x - y)/|x-y|^{q/p}`), and the seminorm only depends on the
`μ`-a.e. class of the function.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set
open scoped ENNReal NNReal

variable {d : ℕ}

/-- The function `(f x - f y) / |x - y|^{q/p}` on pairs, whose `L^p` norm is the seminorm. -/
noncomputable def gagFun (q p : ℝ) (f : Vec d → ℝ) (z : Vec d × Vec d) : ℝ :=
  (f z.1 - f z.2) / vecEuclideanNorm (z.1 - z.2) ^ (q / p)

theorem gagKernel_eq {q p : ℝ} (hp : 0 < p) (f : Vec d → ℝ) (x y : Vec d) :
    gagKernel q p f x y = ENNReal.ofReal (|gagFun q p f (x, y)| ^ p) := by
  unfold gagKernel gagFun
  congr 1
  have hr := vecEuclideanNorm_nonneg (x - y)
  have h1 : (vecEuclideanNorm (x - y) ^ (q / p)) ^ p = vecEuclideanNorm (x - y) ^ q := by
    rw [← Real.rpow_mul hr, div_mul_cancel₀ _ hp.ne']
  rw [abs_div, Real.div_rpow (abs_nonneg _) (abs_nonneg _),
    abs_of_nonneg (Real.rpow_nonneg hr _), h1]

theorem measurable_gagFun {q p : ℝ} {f : Vec d → ℝ} (hf : Measurable f) :
    Measurable (gagFun q p f) := by
  unfold gagFun
  refine ((hf.comp measurable_fst).sub (hf.comp measurable_snd)).div ?_
  exact (Measurable.pow_const (continuous_vecEuclideanNorm.measurable.comp
    (measurable_fst.sub measurable_snd)) _)

theorem gagInt_eq_lintegral_prod (μ : Measure (Vec d)) [SFinite μ] {q p : ℝ} (hp : 0 < p)
    {f : Vec d → ℝ} (hf : Measurable f) :
    gagInt μ q p f = ∫⁻ z, ENNReal.ofReal (|gagFun q p f z| ^ p) ∂(μ.prod μ) := by
  have hm : Measurable fun z => ENNReal.ofReal (|gagFun q p f z| ^ p) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_abs.measurable.comp (measurable_gagFun hf)).pow_const _)
  rw [lintegral_prod _ hm.aemeasurable]
  unfold gagInt
  simp_rw [gagKernel_eq hp]

theorem gagInt_rpow_eq_eLpNorm (μ : Measure (Vec d)) [SFinite μ] {q p : ℝ} (hp : 0 < p)
    {f : Vec d → ℝ} (hf : Measurable f) :
    gagInt μ q p f ^ (1 / p) = eLpNorm (gagFun q p f) (ENNReal.ofReal p) (μ.prod μ) := by
  rw [gagInt_eq_lintegral_prod μ hp hf,
    eLpNorm_eq_lintegral_ofReal_rpow hp (measurable_gagFun hf).aestronglyMeasurable]

/-- Minkowski for the Gagliardo seminorm. -/
theorem gagInt_rpow_sum_le (μ : Measure (Vec d)) [SFinite μ] {q p : ℝ} (hp : 1 ≤ p) {ι : Type*}
    (s : Finset ι) (f : ι → Vec d → ℝ) (hf : ∀ i, Measurable (f i)) :
    gagInt μ q p (fun x => ∑ i ∈ s, f i x) ^ (1 / p) ≤ ∑ i ∈ s, gagInt μ q p (f i) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have hsum : Measurable fun x => ∑ i ∈ s, f i x :=
    Finset.measurable_sum _ fun i _ => hf i
  rw [gagInt_rpow_eq_eLpNorm μ hp0 hsum]
  simp_rw [gagInt_rpow_eq_eLpNorm μ hp0 (hf _)]
  have h1 : gagFun q p (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, gagFun q p (f i) := by
    funext z
    simp only [gagFun, Finset.sum_apply, ← Finset.sum_sub_distrib, Finset.sum_div]
  rw [h1]
  exact eLpNorm_sum_le (by simpa using hp)

/-- The seminorm depends only on the a.e. class. -/
theorem gagInt_congr_ae {μ : Measure (Vec d)} {q p : ℝ} {f g : Vec d → ℝ} (h : f =ᵐ[μ] g) :
    gagInt μ q p f = gagInt μ q p g := by
  unfold gagInt
  refine lintegral_congr_ae ?_
  filter_upwards [h] with x hx
  refine lintegral_congr_ae ?_
  filter_upwards [h] with y hy
  simp only [gagKernel, hx, hy]

end PDE.TraceLane
