module

public import PDEFoundation.Geometry.EuclideanBall.Topology
public import PDEFoundation.Measure.RestrictedVolume
public import Mathlib.Topology.Bases

/-!
# Local almost-everywhere bounds on small balls give a bound on `B_{1/2}`
-/

@[expose] public section

namespace PDE.DGNMLog

open MeasureTheory Filter Topology

theorem ae_le_of_local_ball_bound {d : ℕ} {f : Vec d → ℝ} {S : ℝ}
    (h : ∀ x ∈ euclideanBall (0 : Vec d) (1 / 2),
      ∀ᵐ z ∂(volumeOn (euclideanBall x (1 / 8))), f z ≤ S) :
    ∀ᵐ z ∂(volumeOn (euclideanBall (0 : Vec d) (1 / 2))), f z ≤ S := by
  set s := euclideanBall (0 : Vec d) (1 / 2) with hs
  obtain ⟨T, hTs, hTc, hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (s := s) (f := fun x => euclideanBall x (1 / 8))
    (fun x hx => mem_nhdsWithin_of_mem_nhds
      ((isOpen_euclideanBall x (1 / 8)).mem_nhds (center_mem_euclideanBall x (by norm_num))))
  have h1 : ∀ᵐ z ∂(volume.restrict (⋃ x ∈ T, euclideanBall x (1 / 8))), f z ≤ S := by
    rw [ae_restrict_biUnion_iff _ hTc]
    intro x hx
    exact h x (hTs hx)
  exact ae_restrict_of_ae_restrict_of_subset hcover h1

end PDE.DGNMLog
