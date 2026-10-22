module

public import EllipticRegularity.Holder.PlanarHolderAssemblyLocal
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.Compactness.Lindelof

/-! # Gluing local Hölder representatives on open cubes -/

@[expose] public section

namespace PDE

open MeasureTheory Set

noncomputable section

private theorem openCube_subset_closedCube
    (z : Vec 2) (δ : ℝ) :
    centeredAxisCube z δ ⊆ closedCenteredAxisCube z δ := by
  intro x hx i hi
  exact ⟨(hx i hi).1.le, (hx i hi).2.le⟩

/-- Uniform local Hölder representatives glue to one representative on an
open set. The pointwise local Hölder bound retains its original constant. -/
theorem exists_glued_localHolder_representative
    {S : Set (Vec 2)} {u : Vec 2 → ℝ} {δ α K : ℝ}
    (hS : IsOpen S) (hδ : 0 < δ) (hα : 0 < α) (hK : 0 ≤ K)
    (hlocal : ∀ z ∈ S, ∃ f : Vec 2 → ℝ,
      (∀ᵐ y ∂volumeOn (closedCenteredAxisCube z δ), f y = u y) ∧
      ∀ x ∈ closedCenteredAxisCube z δ,
        ∀ y ∈ closedCenteredAxisCube z δ,
          |f x - f y| ≤ K * vecEuclideanNorm (x - y) ^ α) :
    ∃ v : Vec 2 → ℝ,
      (∀ᵐ x ∂volumeOn S, v x = u x) ∧
      ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ < δ →
        |v x - v y| ≤ K * vecEuclideanNorm (x - y) ^ α := by
  classical
  let patch (z : S) : Set (Vec 2) := centeredAxisCube z.1 δ
  let f (z : S) : Vec 2 → ℝ := Classical.choose (hlocal z.1 z.2)
  have hf (z : S) :
      (∀ᵐ y ∂volumeOn (closedCenteredAxisCube z.1 δ), f z y = u y) ∧
      ∀ x ∈ closedCenteredAxisCube z.1 δ,
        ∀ y ∈ closedCenteredAxisCube z.1 δ,
          |f z x - f z y| ≤ K * vecEuclideanNorm (x - y) ^ α :=
    Classical.choose_spec (hlocal z.1 z.2)
  have hpatchClosed (z : S) : patch z ⊆ closedCenteredAxisCube z.1 δ :=
    openCube_subset_closedCube z.1 δ
  have hcont (z : S) : ContinuousOn (f z)
      (closedCenteredAxisCube z.1 δ) :=
    (show EuclideanHolderSeminormLE
      (closedCenteredAxisCube z.1 δ) (f z) α K from (hf z).2).continuousOn hα hK
  have hoverlap (z w : S) : EqOn (f z) (f w) (patch z ∩ patch w) := by
    let I : Set (Vec 2) := patch z ∩ patch w
    have hIz : I ⊆ closedCenteredAxisCube z.1 δ :=
      inter_subset_left.trans (hpatchClosed z)
    have hIw : I ⊆ closedCenteredAxisCube w.1 δ :=
      inter_subset_right.trans (hpatchClosed w)
    have haeZ : f z =ᵐ[volumeOn I] u :=
      ae_restrict_of_ae_restrict_of_subset hIz (hf z).1
    have haeW : f w =ᵐ[volumeOn I] u :=
      ae_restrict_of_ae_restrict_of_subset hIw (hf w).1
    exact Measure.eqOn_open_of_ae_eq (haeZ.trans haeW.symm)
      ((isOpen_centeredAxisCube z.1 δ).inter
        (isOpen_centeredAxisCube w.1 δ))
      ((hcont z).mono hIz) ((hcont w).mono hIw)
  let v : Vec 2 → ℝ := fun x =>
    if hx : x ∈ S then f ⟨x, hx⟩ x else 0
  have hvpatch (z : S) : EqOn v (f z) (S ∩ patch z) := by
    intro y hy
    have hyself : y ∈ patch (⟨y, hy.1⟩ : S) := by
      dsimp only [patch]
      exact center_mem_centeredAxisCube y hδ
    have heq := hoverlap ⟨y, hy.1⟩ z ⟨hyself, hy.2⟩
    simpa only [v, dite_eq_left hy.1] using heq
  have haepatch (z : S) : v =ᵐ[volumeOn (S ∩ patch z)] u := by
    have heq : v =ᵐ[volumeOn (S ∩ patch z)] f z :=
      (hvpatch z).aeEq_restrict (hS.inter (isOpen_centeredAxisCube z.1 δ)).measurableSet
    have hsub : S ∩ patch z ⊆ closedCenteredAxisCube z.1 δ :=
      inter_subset_right.trans (hpatchClosed z)
    exact heq.trans (ae_restrict_of_ae_restrict_of_subset hsub (hf z).1)
  obtain ⟨T, hTcount, hTcover⟩ :=
    (HereditarilyLindelofSpace.isLindelof S).elim_countable_subcover
      (fun z : S => S ∩ patch z)
      (fun z => hS.inter (isOpen_centeredAxisCube z.1 δ))
      (by
        intro x hx
        apply mem_iUnion.mpr
        refine ⟨⟨x, hx⟩, hx, ?_⟩
        exact center_mem_centeredAxisCube x hδ)
  have hnull (z : S) :
      volume {x | x ∈ S ∩ patch z ∧ v x ≠ u x} = 0 := by
    have hmeas : MeasurableSet (S ∩ patch z) :=
      (hS.inter (isOpen_centeredAxisCube z.1 δ)).measurableSet
    have hae := (ae_restrict_iff' hmeas).1 (haepatch z)
    simpa only [ae_iff, not_imp, not_not] using hae
  have hnullUnion :
      volume (⋃ z ∈ T, {x | x ∈ S ∩ patch z ∧ v x ≠ u x}) = 0 :=
    (measure_biUnion_null_iff hTcount).2 fun z _ => hnull z
  have hbad : {x | x ∈ S ∧ v x ≠ u x} ⊆
      ⋃ z ∈ T, {x | x ∈ S ∩ patch z ∧ v x ≠ u x} := by
    intro x hx
    obtain ⟨z, hzT, hxpatch⟩ := mem_iUnion₂.mp (hTcover hx.1)
    exact mem_iUnion₂.mpr ⟨z, hzT, hxpatch, hx.2⟩
  have hglobae : v =ᵐ[volumeOn S] u := by
    apply (ae_restrict_iff' hS.measurableSet).2
    apply ae_iff.mpr
    have hbad' : {x | ¬(x ∈ S → v x = u x)} ⊆
        ⋃ z ∈ T, {x | x ∈ S ∩ patch z ∧ v x ≠ u x} := by
      simpa only [not_imp, not_not] using hbad
    exact measure_mono_null hbad' hnullUnion
  refine ⟨v, hglobae, ?_⟩
  intro x hx y hy hxy
  let zx : S := ⟨x, hx⟩
  have hxpatch : x ∈ S ∩ patch zx :=
    ⟨hx, center_mem_centeredAxisCube x hδ⟩
  have hypatch : y ∈ S ∩ patch zx := by
    refine ⟨hy, ?_⟩
    dsimp only [patch, zx]
    rw [centeredAxisCube_eq_metric_ball x hδ, Metric.mem_ball, dist_eq_norm]
    simpa only [norm_sub_rev] using hxy
  rw [(hvpatch zx) hxpatch, (hvpatch zx) hypatch]
  exact (hf zx).2 x (hpatchClosed zx hxpatch.2)
    y (hpatchClosed zx hypatch.2)

end

end PDE
