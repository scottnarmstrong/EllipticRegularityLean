module

public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.MeasureTheory.Function.L2Space


/-!
# Measure-theoretic helpers: `L²` limits of products and Fubini bookkeeping
-/

@[expose] public section

namespace PDE.Parabolic.Energy

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- Fubini for a.e.: a statement holding for a.e. slice and every point holds a.e. in the product. -/
theorem ae_prod_of_ae_slice {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν] {P : α → β → Prop}
    (h : ∀ᵐ y ∂ν, ∀ x, P x y) : ∀ᵐ z ∂μ.prod ν, P z.1 z.2 := by
  obtain ⟨T, hTsub, hTm, hT0⟩ := exists_measurable_superset_of_null (ae_iff.1 h)
  rw [ae_iff]
  refine measure_mono_null (t := (univ : Set α) ×ˢ T) ?_ ?_
  · intro z hz
    exact ⟨mem_univ _, hTsub (fun hall => hz (hall z.1))⟩
  · rw [Measure.prod_prod, hT0, mul_zero]

/-- Fubini for a.e. in the other order. -/
theorem ae_ae_swap {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν] {p : α × β → Prop}
    (h : ∀ᵐ z ∂μ.prod ν, p z) : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, p (x, y) := by
  have h2 : ∀ᵐ w ∂ν.prod μ, p w.swap :=
    (Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae h
  exact Measure.ae_ae_of_ae_prod h2

/-- Products of `L²`-convergent sequences converge in `L¹`. -/
theorem tendsto_integral_mul_of_L2 {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {F G : ℕ → X → ℝ} {F0 G0 : X → ℝ}
    (hF : ∀ n, MemLp (F n) 2 μ) (hG : ∀ n, MemLp (G n) 2 μ)
    (hF0 : MemLp F0 2 μ) (hG0 : MemLp G0 2 μ)
    (hFl : Tendsto (fun n => eLpNorm (F n - F0) 2 μ) atTop (𝓝 0))
    (hGl : Tendsto (fun n => eLpNorm (G n - G0) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, F n x * G n x ∂μ) atTop (𝓝 (∫ x, F0 x * G0 x ∂μ)) := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have hA := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' F hF F0 hF0).2 hFl
  have hB := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' G hG G0 hG0).2 hGl
  have hi := Filter.Tendsto.inner (𝕜 := ℝ) hA hB
  have key : ∀ (f g : X → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ),
      inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
    intro f g hf hg
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
    rw [h1, h2]
    simp [mul_comm]
  simp only [key] at hi
  exact hi

/-- Multiplication by a bounded measurable weight preserves `L²` convergence. -/
theorem eLpNorm_mul_sub_le {X : Type*} [MeasurableSpace X] {μ : Measure X} {w f f0 : X → ℝ}
    {C : ℝ} (hwm : AEStronglyMeasurable w μ) (hf : AEStronglyMeasurable f μ)
    (hf0 : AEStronglyMeasurable f0 μ) (hw : ∀ᵐ x ∂μ, |w x| ≤ C) :
    eLpNorm ((fun x => w x * f x) - (fun x => w x * f0 x)) 2 μ ≤
      ENNReal.ofReal C * eLpNorm (f - f0) 2 μ := by
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul ?_ (hw.mono fun x hx => ?_) 2
  · exact (hwm.mul hf).sub (hwm.mul hf0)
  · simp only [Pi.sub_apply, Real.norm_eq_abs]
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)

/-- A bounded weight times a product of two `L²` functions is integrable. -/
theorem integrable_weight_mul {X : Type*} [MeasurableSpace X] {μ : Measure X} {w f h : X → ℝ}
    (hw : AEStronglyMeasurable w μ) {M : ℝ} (hM : ∀ᵐ z ∂μ, |w z| ≤ M) (hf : MemLp f 2 μ)
    (hh : MemLp h 2 μ) : Integrable (fun z => w z * f z * h z) μ := by
  have := (hf.integrable_mul hh).bdd_mul hw (c := M)
    (hM.mono fun z hz => by simpa [Real.norm_eq_abs] using hz)
  simpa [mul_assoc] using this

/-- Weighted version of `tendsto_integral_mul_of_L2`. -/
theorem tendsto_integral_weight_mul_of_L2 {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {w : X → ℝ} (hw : AEStronglyMeasurable w μ) {M : ℝ} (hM : ∀ᵐ x ∂μ, |w x| ≤ M)
    {F G : ℕ → X → ℝ} {F0 G0 : X → ℝ}
    (hF : ∀ n, MemLp (F n) 2 μ) (hG : ∀ n, MemLp (G n) 2 μ)
    (hF0 : MemLp F0 2 μ) (hG0 : MemLp G0 2 μ)
    (hFl : Tendsto (fun n => eLpNorm (F n - F0) 2 μ) atTop (𝓝 0))
    (hGl : Tendsto (fun n => eLpNorm (G n - G0) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, w x * F n x * G n x ∂μ) atTop (𝓝 (∫ x, w x * F0 x * G0 x ∂μ)) := by
  have hwF : ∀ n, MemLp (fun x => w x * F n x) 2 μ := fun n =>
    (hF n).of_le_mul (c := M) (hw.mul (hF n).aestronglyMeasurable)
      (hM.mono fun x hx => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right hx (abs_nonneg _))
  have hwF0 : MemLp (fun x => w x * F0 x) 2 μ :=
    hF0.of_le_mul (c := M) (hw.mul hF0.aestronglyMeasurable)
      (hM.mono fun x hx => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right hx (abs_nonneg _))
  have hl : Tendsto (fun n => eLpNorm ((fun x => w x * F n x) - (fun x => w x * F0 x)) 2 μ)
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => bot_le)
      (fun n => eLpNorm_mul_sub_le hw (hF n).aestronglyMeasurable hF0.aestronglyMeasurable hM)
    have := (ENNReal.Tendsto.const_mul hFl (Or.inr ENNReal.ofReal_ne_top) :
      Tendsto (fun n => ENNReal.ofReal M * eLpNorm (F n - F0) 2 μ) atTop (𝓝 (ENNReal.ofReal M * 0)))
    simpa using this
  exact tendsto_integral_mul_of_L2 hwF hG hwF0 hG0 hl hGl

end PDE.Parabolic.Energy
