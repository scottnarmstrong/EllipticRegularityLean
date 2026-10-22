module

public import PDEFoundation.Monotonicity.Core.Bridge
import PDEFoundation.Monotonicity.Core.RellichSphere

/-!
# Elementary bounds for spherical means

Constants have sphere mean equal to themselves, and a pointwise bound on the sphere bounds the
sphere mean.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE.MonoSqBalls

variable {d : ℕ}

theorem sphereMean_const [NeZero d] (x : Vec d) (r c : ℝ) :
    sphereMean x r (fun _ => c) = c := by
  unfold sphereMean
  have h := Internal.sphereMeasure_real_univ_ne_zero (d := d)
  have : NeZero ((volume : Measure (HilbertVec d)).toSphere) := by
    refine ⟨fun h0 => ?_⟩
    apply h
    simp only [Internal.sphereMeasure, Measure.real]
    rw [h0]; simp
  have : IsFiniteMeasure ((volume : Measure (HilbertVec d)).toSphere) := by
    infer_instance
  exact average_const _ c

theorem sphereMean_le_of_le [NeZero d] {g : Vec d → ℝ} {r K : ℝ}
    (hg : ContinuousOn g (euclideanSphere (0 : Vec d) r))
    (h : ∀ x ∈ euclideanSphere (0 : Vec d) r, g x ≤ K) :
    sphereMean (0 : Vec d) r g ≤ K := by
  have hc := sphereMean_const (0 : Vec d) r K
  have hint := integrable_sphere_comp hg
  have hint2 : Integrable (fun _ : Metric.sphere (0 : HilbertVec d) 1 => K)
      ((volume : Measure (HilbertVec d)).toSphere) := by
    have : IsFiniteMeasure ((volume : Measure (HilbertVec d)).toSphere) := by infer_instance
    exact integrable_const K
  rw [← hc]
  unfold sphereMean
  simp only [zero_add]
  rw [average_eq, average_eq]
  refine smul_le_smul_of_nonneg_left (integral_mono hint hint2 fun ω => ?_)
    (inv_nonneg.mpr measureReal_nonneg)
  exact h _ (sphere_smul_toVec_mem r ω)

end PDE.MonoSqBalls
