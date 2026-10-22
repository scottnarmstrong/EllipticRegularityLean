module

public import PDEFoundation

/-!
# Measure-level facts for parabolic rescaling

The affine maps `Ψ y = c + r • y`, `τ s = T₀ + r² * s` and `Φ = Ψ × τ` are measurable
embeddings (indeed homeomorphisms) pushing volume to a constant multiple of volume.  Generic
transfer lemmas for `MemLp`, a.e. statements, integrability, integrals, `AEMeasurable` and
essential bounds along a measurable embedding with `map F μ = k • ν` are collected here.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Parabolic.Rescale

section Generic

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {F : α → β} {μ : Measure α} {ν : Measure β} {k : ℝ≥0∞}

theorem memLp_comp_of_map_eq_smul (hF : MeasurableEmbedding F) (hk : k ≠ ∞)
    (h : μ.map F = k • ν) {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} {g : β → E}
    (hg : MemLp g p ν) : MemLp (g ∘ F) p μ := by
  rw [← hF.memLp_map_measure_iff, h]
  exact hg.smul_measure hk

theorem memLp_of_comp_of_map_eq_smul (hF : MeasurableEmbedding F) (hk0 : k ≠ 0) (hk : k ≠ ∞)
    (h : μ.map F = k • ν) {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} {g : β → E}
    (hg : MemLp (g ∘ F) p μ) : MemLp g p ν := by
  rw [← hF.memLp_map_measure_iff, h] at hg
  have h2 : MemLp g p (k⁻¹ • k • ν) := hg.smul_measure (ENNReal.inv_ne_top.2 hk0)
  rwa [smul_smul, ENNReal.inv_mul_cancel hk0 hk, one_smul] at h2

theorem ae_comp_of_map_eq_smul (hF : MeasurableEmbedding F)
    (h : μ.map F = k • ν) {P : β → Prop} (hP : ∀ᵐ y ∂ν, P y) :
    ∀ᵐ x ∂μ, P (F x) := by
  rw [← hF.ae_map_iff, h]
  exact Measure.ae_smul_measure hP k

theorem integrable_comp_of_map_eq_smul (hF : MeasurableEmbedding F) (hk : k ≠ ∞)
    (h : μ.map F = k • ν) {E : Type*} [NormedAddCommGroup E] {g : β → E}
    (hg : Integrable g ν) : Integrable (g ∘ F) μ := by
  rw [← hF.integrable_map_iff, h]
  exact hg.smul_measure hk

theorem integral_comp_of_map_eq_smul (hF : MeasurableEmbedding F)
    (h : μ.map F = k • ν) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : β → E) : ∫ x, g (F x) ∂μ = k.toReal • ∫ y, g y ∂ν := by
  rw [← hF.integral_map, h, integral_smul_measure]

theorem aemeasurable_comp_of_map_eq_smul (hF : MeasurableEmbedding F)
    (h : μ.map F = k • ν) {E : Type*} [MeasurableSpace E] {g : β → E}
    (hg : AEMeasurable g ν) : AEMeasurable (g ∘ F) μ := by
  rw [← hF.aemeasurable_map_iff, h]
  exact hg.smul_measure k

theorem measure_preimage_eq_zero_iff (hF : MeasurableEmbedding F) (hk : k ≠ 0)
    (h : μ.map F = k • ν) (S : Set β) : μ (F ⁻¹' S) = 0 ↔ ν S = 0 := by
  rw [← hF.map_apply, h, Measure.smul_apply, smul_eq_mul, mul_eq_zero]
  simp [hk]

theorem essSup_comp_of_map_eq_smul (hF : MeasurableEmbedding F) (hk : k ≠ 0)
    (h : μ.map F = k • ν) {γ : Type*} [ConditionallyCompleteLinearOrder γ] (g : β → γ) :
    essSup (g ∘ F) μ = essSup g ν := by
  rw [essSup_eq_sInf, essSup_eq_sInf]
  congr 1
  ext a
  exact measure_preimage_eq_zero_iff hF hk h {y | a < g y}

theorem essInf_comp_of_map_eq_smul (hF : MeasurableEmbedding F) (hk : k ≠ 0)
    (h : μ.map F = k • ν) {γ : Type*} [ConditionallyCompleteLinearOrder γ] (g : β → γ) :
    essInf (g ∘ F) μ = essInf g ν := by
  rw [essInf_eq_sSup, essInf_eq_sSup]
  congr 1
  ext a
  exact measure_preimage_eq_zero_iff hF hk h {y | g y < a}

theorem map_restrict_of_embedding (hF : MeasurableEmbedding F) (μ : Measure α) (S : Set α) :
    (μ.restrict S).map F = (μ.map F).restrict (F '' S) := by
  rw [hF.restrict_map, preimage_image_eq _ hF.injective]

end Generic

end PDE.Parabolic.Rescale
