module

public import PDEFoundation.Sobolev.Trace.Assembly.Basic

/-!
# Lower semicontinuity of the Gagliardo seminorm

If `f n → g` almost everywhere for the surface measure and `[f n] ≤ B n → B`, then `[g] ≤ B`
(Fatou's lemma, applied to the inner and then the outer integral).
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

variable {d : ℕ} {Ω : Set (Vec d)}

/-- The Gagliardo integrand. -/
noncomputable def fatouKernel (d : ℕ) (q p : ℝ) (x y : Vec d) (a b : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (|a - b| ^ p / vecEuclideanNorm (x - y) ^ q)

theorem continuous_fatouKernel {q p : ℝ} (hp : 0 < p) (x y : Vec d) :
    Continuous (Function.uncurry (fatouKernel d q p x y)) := by
  have h1 : Continuous fun ab : ℝ × ℝ => |ab.1 - ab.2| ^ p :=
    (continuous_abs.comp (continuous_fst.sub continuous_snd)).rpow_const fun _ => Or.inr hp.le
  exact ENNReal.continuous_ofReal.comp (h1.div_const _)

theorem tendsto_fatouKernel {q p : ℝ} (hp : 0 < p) (x y : Vec d) {a b : ℕ → ℝ} {a₀ b₀ : ℝ}
    (ha : Tendsto a atTop (𝓝 a₀)) (hb : Tendsto b atTop (𝓝 b₀)) :
    Tendsto (fun n => fatouKernel d q p x y (a n) (b n)) atTop (𝓝 (fatouKernel d q p x y a₀ b₀)) := by
  have h := ((continuous_fatouKernel (q := q) hp x y).tendsto (a₀, b₀)).comp (ha.prodMk_nhds hb)
  simpa only [Function.comp_def, Function.uncurry_apply_pair] using h

/-- The `p`-th power of the Gagliardo seminorm as a double integral of `fatouKernel`. -/
theorem gagliardoSeminorm_eq_fatou (s p : ℝ) (f : Vec d → ℝ) :
    gagliardoSeminorm Ω s p f = (∫⁻ x, ∫⁻ y, fatouKernel d ((d : ℝ) - 1 + s * p) p x y (f x) (f y)
      ∂boundarySurfaceMeasure Ω ∂boundarySurfaceMeasure Ω) ^ (1 / p) := rfl

theorem aemeasurable_fatouKernel_prod {μ : Measure (Vec d)} [SFinite μ] {q p : ℝ} {f : Vec d → ℝ}
    (hf : AEMeasurable f μ) :
    AEMeasurable (fun z : Vec d × Vec d => fatouKernel d q p z.1 z.2 (f z.1) (f z.2)) (μ.prod μ) := by
  have h1 : AEMeasurable (fun z : Vec d × Vec d => f z.1) (μ.prod μ) :=
    hf.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have h2 : AEMeasurable (fun z : Vec d × Vec d => f z.2) (μ.prod μ) :=
    hf.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  unfold fatouKernel
  refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
  refine AEMeasurable.div ?_ ?_
  · exact (continuous_abs.measurable.comp_aemeasurable (h1.sub h2)).pow_const p
  · exact ((continuous_vecEuclideanNorm.measurable.comp (measurable_fst.sub measurable_snd)).pow_const
      q).aemeasurable

/-- Fatou for the double Gagliardo integral, for an arbitrary s-finite measure. -/
theorem lintegral_fatouKernel_le_liminf (μ : Measure (Vec d)) [SFinite μ] {q p : ℝ} (hp : 0 < p)
    {f : ℕ → Vec d → ℝ} {g : Vec d → ℝ} (hf : ∀ n, AEMeasurable (f n) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    ∫⁻ x, ∫⁻ y, fatouKernel d q p x y (g x) (g y) ∂μ ∂μ ≤
      liminf (fun n => ∫⁻ x, ∫⁻ y, fatouKernel d q p x y (f n x) (f n y) ∂μ ∂μ) atTop := by
  have hinner : ∀ᵐ x ∂μ, ∫⁻ y, fatouKernel d q p x y (g x) (g y) ∂μ ≤
      liminf (fun n => ∫⁻ y, fatouKernel d q p x y (f n x) (f n y) ∂μ) atTop := by
    filter_upwards [hlim] with x hx
    have hmeas : ∀ n, AEMeasurable (fun y => fatouKernel d q p x y (f n x) (f n y)) μ := by
      intro n
      unfold fatouKernel
      refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
      refine AEMeasurable.div ?_ ?_
      · exact (continuous_abs.measurable.comp_aemeasurable ((hf n).const_sub (f n x))).pow_const p
      · exact ((continuous_vecEuclideanNorm.measurable.comp
          (measurable_const.sub measurable_id)).pow_const q).aemeasurable
    calc ∫⁻ y, fatouKernel d q p x y (g x) (g y) ∂μ
        = ∫⁻ y, liminf (fun n => fatouKernel d q p x y (f n x) (f n y)) atTop ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hlim] with y hy
          exact ((tendsto_fatouKernel hp x y hx hy).liminf_eq).symm
      _ ≤ _ := lintegral_liminf_le' hmeas
  calc ∫⁻ x, ∫⁻ y, fatouKernel d q p x y (g x) (g y) ∂μ ∂μ
      ≤ ∫⁻ x, liminf (fun n => ∫⁻ y, fatouKernel d q p x y (f n x) (f n y) ∂μ) atTop ∂μ :=
        lintegral_mono_ae hinner
    _ ≤ _ := lintegral_liminf_le' fun n =>
        (aemeasurable_fatouKernel_prod (hf n)).lintegral_prod_right'

/-- **Fatou for the Gagliardo seminorm.** -/
theorem gagliardoSeminorm_le_of_tendsto [IsFiniteMeasure (boundarySurfaceMeasure Ω)]
    {s p : ℝ} (hp : 0 < p) {f : ℕ → Vec d → ℝ} {g : Vec d → ℝ}
    (hf : ∀ n, AEMeasurable (f n) (boundarySurfaceMeasure Ω))
    (hlim : ∀ᵐ x ∂boundarySurfaceMeasure Ω, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    {B : ℕ → ℝ≥0∞} {B₀ : ℝ≥0∞} (hB : Tendsto B atTop (𝓝 B₀))
    (hfB : ∀ n, gagliardoSeminorm Ω s p (f n) ≤ B n) :
    gagliardoSeminorm Ω s p g ≤ B₀ := by
  have hp' : 0 < 1 / p := by positivity
  have houter := lintegral_fatouKernel_le_liminf (boundarySurfaceMeasure Ω)
    (q := (d : ℝ) - 1 + s * p) hp hf hlim
  have hIB : ∀ n, (∫⁻ x, ∫⁻ y, fatouKernel d ((d : ℝ) - 1 + s * p) p x y (f n x) (f n y)
      ∂boundarySurfaceMeasure Ω ∂boundarySurfaceMeasure Ω) ≤ B n ^ p := by
    intro n
    have h := hfB n
    rw [gagliardoSeminorm_eq_fatou] at h
    calc _ = ((∫⁻ x, ∫⁻ y, fatouKernel d ((d : ℝ) - 1 + s * p) p x y (f n x) (f n y)
          ∂boundarySurfaceMeasure Ω ∂boundarySurfaceMeasure Ω) ^ (1 / p)) ^ p := by
          rw [← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]
      _ ≤ B n ^ p := ENNReal.rpow_le_rpow h hp.le
  have hlimB : Tendsto (fun n => B n ^ p) atTop (𝓝 (B₀ ^ p)) :=
    (ENNReal.continuous_rpow_const.tendsto B₀).comp hB
  have hIg := houter.trans ((liminf_le_liminf (Eventually.of_forall hIB)).trans_eq hlimB.liminf_eq)
  rw [gagliardoSeminorm_eq_fatou]
  calc _ ≤ (B₀ ^ p) ^ (1 / p) := ENNReal.rpow_le_rpow hIg hp'.le
    _ = B₀ := by rw [← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one]

end PDE.TraceLane
