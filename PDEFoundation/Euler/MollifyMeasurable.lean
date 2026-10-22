module

public import PDEFoundation.Euler.MollifyPairing
public import PDEFoundation.Euler.TorusBasic

/-!
# Periodic extension: measurability on `ℝ² × [0,T]`

A function on space-time that is measurable on `[0,1]² × [0,T]` (`eulerMeasure T`) and `ℤ²`-periodic in `x`
for every `t` is a.e.-strongly measurable for `volume.prod (volume.restrict [0,T])`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

/-- Space-time measure with the spatial factor extended to all of `Vec 2`. -/
noncomputable def eulerMeasureExt (T : ℝ) : Measure (Vec 2 × ℝ) :=
  (volume : Measure (Vec 2)).prod (volume.restrict (Icc 0 T))

instance (T : ℝ) : SFinite (eulerMeasureExt T) := by unfold eulerMeasureExt; infer_instance

theorem eulerMeasure_le_ext (T : ℝ) : eulerMeasure T ≤ eulerMeasureExt T := by
  rw [eulerMeasure_eq_prod, eulerMeasureExt]
  exact Measure.prod_mono Measure.restrict_le_self le_rfl

theorem aestronglyMeasurable_ext_of_periodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℝ} {u : Vec 2 × ℝ → E} (hu : AEStronglyMeasurable u (eulerMeasure T))
    (hup : ∀ t, IsTorusPeriodic (fun x => u (x, t))) :
    AEStronglyMeasurable u (eulerMeasureExt T) := by
  set μ := eulerMeasureExt T with hμ
  let τ : (Fin 2 → ℤ) → Vec 2 × ℝ → Vec 2 × ℝ := fun k p => (p.1 - latVec k, p.2)
  have hτmp : ∀ k, MeasurePreserving (τ k) μ μ := fun k =>
    (measurePreserving_sub_right (volume : Measure (Vec 2)) (latVec k)).prod
      (MeasurePreserving.id (volume.restrict (Icc (0 : ℝ) T)))
  have hτemb : ∀ k, MeasurableEmbedding (τ k) := fun k =>
    (measurableEmbedding_subRight (latVec k)).prodMap MeasurableEmbedding.id
  have hcubeμ : μ.restrict (torusCube ×ˢ univ) = eulerMeasure T := by
    rw [hμ, eulerMeasureExt, eulerMeasure_eq_prod, ← Measure.prod_restrict]
    simp
  have hcover : (univ : Set (Vec 2 × ℝ)) ⊆ ⋃ k : Fin 2 → ℤ, (τ k) ⁻¹' (torusCube ×ˢ univ) := by
    intro p _
    simp only [mem_iUnion, mem_preimage, mem_prod, mem_univ, and_true]
    refine ⟨fun i => ⌊p.1 i⌋, ?_⟩
    show p.1 - latVec _ ∈ torusCube
    constructor <;> intro i <;> simp only [Pi.sub_apply, latVec_apply, Pi.zero_apply, Pi.one_apply]
    · linarith [Int.floor_le (p.1 i)]
    · linarith [Int.lt_floor_add_one (p.1 i)]
  have hall : μ.restrict (⋃ k : Fin 2 → ℤ, (τ k) ⁻¹' (torusCube ×ˢ univ)) = μ :=
    Measure.restrict_eq_self_of_ae_mem (Filter.Eventually.of_forall fun p => hcover (mem_univ p))
  rw [← hall, aestronglyMeasurable_iUnion_iff]
  intro k
  have hmp := (hτmp k).restrict_preimage_emb (hτemb k) (torusCube ×ˢ univ)
  rw [hcubeμ] at hmp
  have := hu.comp_measurePreserving hmp
  refine this.congr ?_
  refine Filter.Eventually.of_forall fun p => ?_
  simp only [Function.comp, τ]
  exact (hup p.2).sub_latVec k p.1

end PDE
