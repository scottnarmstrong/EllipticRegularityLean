module

public import PDEFoundation.Measure.VecAppendLpReflection
public import PDEFoundation.Geometry.VecAppendBall
public import PDEFoundation.Measure.BallVolume

@[expose] public section

namespace PDE
open MeasureTheory Set
open scoped ENNReal

/-- Nonmembership on the first half-radius ball survives adjoining unused
coordinates and restriction to the full round ball. -/
theorem not_memLp_comp_fst_vecAppendEquiv_euclideanBall
    (m n : ℕ) {R : ℝ} (hR : 0 < R) {p : ℝ≥0∞} {f : Vec m → ℝ}
    (hf : AEStronglyMeasurable f
      (volume.restrict (euclideanBall (0 : Vec m) (R / 2))))
    (hNot : ¬ MemLp f p
      (volume.restrict (euclideanBall (0 : Vec m) (R / 2)))) :
    ¬ MemLp (fun z : Vec (m + n) => f (vecAppendEquiv m n z).1) p
      (volume.restrict (euclideanBall (0 : Vec (m + n)) R)) := by
  intro hFull
  have hhalf : 0 < R / 2 := half_pos hR
  have hCylinder := hFull.mono_measure
    (Measure.restrict_mono
      (preimage_vecAppendEquiv_prod_halfBall_subset_euclideanBall m n hR) le_rfl)
  apply hNot
  exact memLp_of_comp_fst_vecAppendEquiv m n
    (measurableSet_euclideanBall 0 (R / 2))
    (measurableSet_euclideanBall 0 (R / 2))
    (volume_euclideanBall_pos 0 hhalf)
    (lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top 0 hhalf.le)) hf hCylinder

end PDE
