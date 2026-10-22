module

public import PDEFoundation.Ambient.PlanarRadialProjection
public import PDEFoundation.Ambient.MatAppend
public import PDEFoundation.Geometry.EuclideanBall.Topology
public import Mathlib.MeasureTheory.Constructions.Pi

/-! # Measurability of planar radial coefficients in larger dimensions -/

@[expose] public section

namespace PDE

open MeasureTheory

/-- Every entry of the planar reflection pulled back by coordinate splitting
is measurable, including on the set where the first block vanishes. -/
theorem measurable_planarBlock_radialReflectionMatrix_apply
    (n : ℕ) (i j : Fin 2) :
    Measurable (fun z : Vec (2 + n) =>
      radialReflectionMatrix (vecAppendEquiv 2 n z).1 i j) := by
  have hf : Measurable (fun z : Vec (2 + n) => (vecAppendEquiv 2 n z).1) :=
    (vecAppendEquiv 2 n).continuous.fst.measurable
  have hproduct : Measurable (fun z : Vec (2 + n) =>
      (vecAppendEquiv 2 n z).1 i * (vecAppendEquiv 2 n z).1 j /
        vecNormSq (vecAppendEquiv 2 n z).1) :=
    (((measurable_pi_apply i).comp hf).mul
      ((measurable_pi_apply j).comp hf)).div
      (continuous_vecNormSq.measurable.comp hf)
  simp only [radialReflectionMatrix, two_smul, Matrix.add_apply,
    Matrix.sub_apply, radialProjectionMatrix_apply]
  exact (hproduct.add hproduct).sub measurable_const

/-- Scaling the planar coefficient and adjoining an unused identity block
preserves coordinate measurability. -/
theorem measurable_matAppend_smul_one_add_planarRadialReflectionMatrix_apply
    (n : ℕ) (c δ : ℝ) (i j : Fin (2 + n)) :
    Measurable (fun z : Vec (2 + n) =>
      matAppend (c • ((1 : Mat 2) +
        δ • radialReflectionMatrix (vecAppendEquiv 2 n z).1)) (1 : Mat n) i j) := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [matAppend_apply_castAdd_castAdd, Matrix.smul_apply,
        Matrix.add_apply, smul_eq_mul]
      exact (measurable_const.add
        ((measurable_planarBlock_radialReflectionMatrix_apply n i j).const_mul δ)).const_mul c
    · simp only [matAppend_apply_castAdd_natAdd]
      exact measurable_const
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [matAppend_apply_natAdd_castAdd]
      exact measurable_const
    · simp only [matAppend_apply_natAdd_natAdd]
      exact measurable_const

end PDE
