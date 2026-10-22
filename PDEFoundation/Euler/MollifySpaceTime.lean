module

public import PDEFoundation.Euler.MollifyMeasurable
public import PDEFoundation.Euler.MollifyCommute

/-!
# Space-time spatial mollification: measurability

`mollifyST a u (x,t) = (molK a ⋆ u(·,t)) x` and `mollifyVecST` for planar fields.  If `u` is a.e. strongly
measurable for `eulerMeasureExt T` then so is `mollifyST a u`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

/-- Spatial mollification of a scalar space-time function, at each fixed time. -/
noncomputable def mollifyST (a : ℝ) (u : Vec 2 × ℝ → ℝ) : Vec 2 × ℝ → ℝ :=
  fun z => mollify a (fun x => u (x, z.2)) z.1

/-- Spatial mollification of a planar space-time field, at each fixed time. -/
noncomputable def mollifyVecST (a : ℝ) (u : Vec 2 × ℝ → Vec 2) : Vec 2 × ℝ → Vec 2 :=
  fun z => mollifyVec a (fun x => u (x, z.2)) z.1

theorem mollifyVecST_apply (a : ℝ) (u : Vec 2 × ℝ → Vec 2) (z : Vec 2 × ℝ) (i : Fin 2) :
    mollifyVecST a u z i = mollifyST a (fun w => u w i) z := rfl

theorem aestronglyMeasurable_mollifyST (a : ℝ) {T : ℝ} {u : Vec 2 × ℝ → ℝ}
    (hu : AEStronglyMeasurable u (eulerMeasureExt T)) :
    AEStronglyMeasurable (mollifyST a u) (eulerMeasureExt T) := by
  set μ := eulerMeasureExt T with hμ
  have hshear : ∀ s : Vec 2, MeasurePreserving (fun p : Vec 2 × ℝ => (p.1 - s, p.2)) μ μ := fun s =>
    (measurePreserving_sub_right (volume : Measure (Vec 2)) s).prod
      (MeasurePreserving.id (volume.restrict (Icc (0 : ℝ) T)))
  have hskew : MeasurePreserving (fun q : Vec 2 × (Vec 2 × ℝ) => (q.1, (q.2.1 - q.1, q.2.2)))
      ((volume : Measure (Vec 2)).prod μ) ((volume : Measure (Vec 2)).prod μ) := by
    refine MeasurePreserving.skew_product (MeasurePreserving.id (volume : Measure (Vec 2)))
      (g := fun (s : Vec 2) (p : Vec 2 × ℝ) => (p.1 - s, p.2)) ?_ ?_
    · exact (measurable_snd.fst.sub measurable_fst).prodMk measurable_snd.snd
    · exact Filter.Eventually.of_forall fun s => (hshear s).map_eq
  have hΨ : MeasurePreserving (fun q : (Vec 2 × ℝ) × Vec 2 => (q.2, (q.1.1 - q.2, q.1.2)))
      (μ.prod (volume : Measure (Vec 2))) ((volume : Measure (Vec 2)).prod μ) :=
    hskew.comp (Measure.measurePreserving_swap (μ := μ) (ν := (volume : Measure (Vec 2))))
  have hu2 : AEStronglyMeasurable (fun q : Vec 2 × (Vec 2 × ℝ) => u q.2)
      ((volume : Measure (Vec 2)).prod μ) := hu.comp_snd
  have hΘ : AEStronglyMeasurable (fun q : (Vec 2 × ℝ) × Vec 2 => molK a q.2 * u (q.1.1 - q.2, q.1.2))
      (μ.prod (volume : Measure (Vec 2))) := by
    have h1 := hu2.comp_measurePreserving hΨ
    have h2 : AEStronglyMeasurable (fun q : (Vec 2 × ℝ) × Vec 2 => molK a q.2)
        (μ.prod (volume : Measure (Vec 2))) :=
      (Continuous.aestronglyMeasurable (by exact (molK_contDiff a).continuous)).comp_snd
    exact h2.mul h1
  have := hΘ.integral_prod_right'
  refine this.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [mollifyST, mollify_apply]

end PDE
