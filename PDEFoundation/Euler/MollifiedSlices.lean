module

public import PDEFoundation.Euler.MollifyBundle
public import PDEFoundation.Euler.MollifyDeriv

/-!
# Mollified slices of a bounded weak solution

For `w` with `IsEulerWeakSolution`-type data (measurable, periodic slices, a.e. bounded), the space-time fields
`mollifyVecST a w` and `∂ⱼ mollifyVecST a w` are a.e. strongly measurable and a.e. bounded on `eulerMeasure T`
(the derivative bound `pdMolKNorm a j * √B` depends on the scale `a`), and a.e. slices are locally integrable.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

/-- Mollified gradient field `∂ⱼ (mollifyVec a w(·,t))ᵢ (x)` as a function on space-time. -/
noncomputable def gradMollST (a : ℝ) (w : Vec 2 × ℝ → Vec 2) (z : Vec 2 × ℝ) (i j : Fin 2) : ℝ :=
  gradMat (fun y => mollifyVecST a w (y, z.2)) z.1 i j

theorem ae_slice_locInt {T : ℝ} {w : Vec 2 × ℝ → Vec 2}
    (hmeas : AEStronglyMeasurable w (eulerMeasure T))
    (hper : ∀ t, IsTorusPeriodic (fun x => w (x, t))) {B : ℝ}
    (hB : ∀ᵐ z ∂(eulerMeasure T), vecNormSq (w z) ≤ B) :
    ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)),
      (∀ i, LocallyIntegrable (fun x => w (x, t) i) volume) ∧
      (∀ᵐ y ∂(volume : Measure (Vec 2)), vecNormSq (w (y, t)) ≤ B) := by
  have hint : ∀ i, Integrable (fun z => w z i) (eulerMeasure T) :=
    integrable_coord_of_bounded hmeas hB
  have prod_eq : eulerMeasure T = (volume.restrict torusCube).prod (volume.restrict (Icc (0 : ℝ) T)) :=
    eulerMeasure_eq_prod T
  have hbt : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), ∀ᵐ x ∂(volume.restrict torusCube),
      vecNormSq (w (x, t)) ≤ B := by
    rw [prod_eq] at hB
    have h1 := (Measure.measurePreserving_swap (μ := volume.restrict (Icc (0 : ℝ) T))
      (ν := volume.restrict torusCube)).quasiMeasurePreserving.ae hB
    exact Measure.ae_ae_of_ae_prod h1
  have hint0 := hint 0
  have hint1 := hint 1
  rw [prod_eq] at hint0 hint1
  filter_upwards [hint0.prod_left_ae, hint1.prod_left_ae, hbt] with t i0 i1 hb
  refine ⟨fun i => ?_, (hper t).ae_of_ae_cube (P := fun r => vecNormSq r ≤ B) hb⟩
  have hi : Integrable (fun x => w (x, t) i) (volume.restrict torusCube) := by fin_cases i <;> assumption
  exact IsTorusPeriodic.locallyIntegrable ((hper t).comp (fun r => r i)) hi

theorem aestronglyMeasurable_mollifyVecST {T : ℝ} {w : Vec 2 × ℝ → Vec 2}
    (hmeas : AEStronglyMeasurable w (eulerMeasure T))
    (hper : ∀ t, IsTorusPeriodic (fun x => w (x, t))) (a : ℝ) (i : Fin 2) :
    AEStronglyMeasurable (fun z => mollifyVecST a w z i) (eulerMeasure T) := by
  have h1 : AEStronglyMeasurable (fun z => w z i) (eulerMeasure T) :=
    (continuous_apply i).comp_aestronglyMeasurable hmeas
  have h2 := aestronglyMeasurable_ext_of_periodic h1 (fun t => (hper t).comp (fun r => r i))
  exact (aestronglyMeasurable_mollifyST a h2).mono_measure (eulerMeasure_le_ext T)

theorem ae_abs_mollifyVecST_le {T : ℝ} {w : Vec 2 × ℝ → Vec 2}
    (hmeas : AEStronglyMeasurable w (eulerMeasure T))
    (hper : ∀ t, IsTorusPeriodic (fun x => w (x, t))) {B : ℝ}
    (hB : ∀ᵐ z ∂(eulerMeasure T), vecNormSq (w z) ≤ B) {a : ℝ} (ha : 0 < a) (i : Fin 2) :
    ∀ᵐ z ∂(eulerMeasure T), |mollifyVecST a w z i| ≤ Real.sqrt B := by
  have h := ae_slice_locInt hmeas hper hB
  have h2 : ∀ᵐ z ∂(eulerMeasure T), (∀ i, LocallyIntegrable (fun x => w (x, z.2) i) volume) ∧
      (∀ᵐ y ∂(volume : Measure (Vec 2)), vecNormSq (w (y, z.2)) ≤ B) := by
    rw [eulerMeasure_eq_prod]
    exact (Measure.quasiMeasurePreserving_snd (μ := volume.restrict torusCube)
      (ν := volume.restrict (Icc (0 : ℝ) T))).ae h
  filter_upwards [h2] with z ⟨hloc, hb⟩
  exact abs_mollifyVec_le ha hloc (B := Real.sqrt B)
    (hb.mono fun y hy i => abs_coord_le_sqrt hy i) z.1 i

theorem aestronglyMeasurable_gradMollST {T : ℝ} {w : Vec 2 × ℝ → Vec 2}
    (hmeas : AEStronglyMeasurable w (eulerMeasure T))
    (hper : ∀ t, IsTorusPeriodic (fun x => w (x, t))) {B : ℝ}
    (hB : ∀ᵐ z ∂(eulerMeasure T), vecNormSq (w z) ≤ B) {a : ℝ} (ha : 0 < a) (i j : Fin 2) :
    AEStronglyMeasurable (fun z => gradMollST a w z i j) (eulerMeasure T) := by
  have h1 : AEStronglyMeasurable (fun z => w z i) (eulerMeasure T) :=
    (continuous_apply i).comp_aestronglyMeasurable hmeas
  have h2 := aestronglyMeasurable_ext_of_periodic h1 (fun t => (hper t).comp (fun r => r i))
  have h3 := ae_slice_locInt hmeas hper hB
  have hloc : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)),
      LocallyIntegrable (fun x => (fun z => w z i) (x, t)) volume :=
    h3.mono fun t ht => ht.1 i
  exact (aestronglyMeasurable_pd_mollifyST ha h2 hloc j).mono_measure (eulerMeasure_le_ext T)

theorem ae_abs_gradMollST_le {T : ℝ} {w : Vec 2 × ℝ → Vec 2}
    (hmeas : AEStronglyMeasurable w (eulerMeasure T))
    (hper : ∀ t, IsTorusPeriodic (fun x => w (x, t))) {B : ℝ}
    (hB : ∀ᵐ z ∂(eulerMeasure T), vecNormSq (w z) ≤ B) {a : ℝ} (ha : 0 < a) (i j : Fin 2) :
    ∀ᵐ z ∂(eulerMeasure T), |gradMollST a w z i j| ≤ pdMolKNorm a j * Real.sqrt B := by
  have h := ae_slice_locInt hmeas hper hB
  have h2 : ∀ᵐ z ∂(eulerMeasure T), (∀ i, LocallyIntegrable (fun x => w (x, z.2) i) volume) ∧
      (∀ᵐ y ∂(volume : Measure (Vec 2)), vecNormSq (w (y, z.2)) ≤ B) := by
    rw [eulerMeasure_eq_prod]
    exact (Measure.quasiMeasurePreserving_snd (μ := volume.restrict torusCube)
      (ν := volume.restrict (Icc (0 : ℝ) T))).ae h
  filter_upwards [h2] with z ⟨hloc, hb⟩
  exact abs_pd_mollify_le ha (hloc i) (B := Real.sqrt B)
    (hb.mono fun y hy => abs_coord_le_sqrt hy i) j z.1

end PDE
