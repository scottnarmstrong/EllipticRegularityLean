module

public import PDEFoundation.Measure.FiniteBallCoverEstimate
public import Mathlib.Topology.Compactness.Compact

/-!
# Measure estimate from a compact cover by balls with large averages

Compactness reduces a pointwise cover by native round balls to the finite
covering estimate.
-/

@[expose] public section

namespace PDE

open MeasureTheory

/-- A compact set covered pointwise by positive-radius balls on which `|b|`
has average larger than `t > 0` satisfies the triple-dilate measure estimate. -/
theorem volume_compact_toReal_le_of_euclideanBall_average_gt
    {d : ℕ} {K : Set (Vec d)} (hK : IsCompact K)
    (b : Vec d → ℝ) (t : ℝ) (ht : 0 < t)
    (hb : Integrable b volume)
    (hcover : ∀ x ∈ K, ∃ z : Vec d, ∃ R : ℝ,
      0 < R ∧ x ∈ euclideanBall z R ∧
        t < ⨍ y in euclideanBall z R, |b y| ∂volume) :
    (volume K).toReal ≤
      (3 : ℝ) ^ d / t * ∫ x, |b x| ∂volume := by
  classical
  have hcover' (x : K) : ∃ z : Vec d, ∃ R : ℝ,
      0 < R ∧ x.1 ∈ euclideanBall z R ∧
        t < ⨍ y in euclideanBall z R, |b y| ∂volume :=
    hcover x.1 x.2
  choose z R hR hx havg using hcover'
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun x : K => euclideanBall (z x) (R x))
    (fun x => isOpen_euclideanBall (z x) (R x)) (by
      intro x hxK
      exact Set.mem_iUnion.mpr ⟨⟨x, hxK⟩, hx ⟨x, hxK⟩⟩)
  have hballs_top :
      (∑ x ∈ s, volume (euclideanBall (z x) (R x))) ≠ ⊤ := by
    exact ENNReal.sum_ne_top.mpr fun x _ =>
      volume_euclideanBall_ne_top (z x) (hR x).le
  have hunion_top :
      volume (⋃ x ∈ s, euclideanBall (z x) (R x)) ≠ ⊤ := by
    exact ne_top_of_le_ne_top
      hballs_top
      (measure_biUnion_finset_le s fun x => euclideanBall (z x) (R x))
  calc
    (volume K).toReal ≤
        (volume (⋃ x ∈ s, euclideanBall (z x) (R x))).toReal :=
      ENNReal.toReal_mono hunion_top (measure_mono hs)
    _ ≤ (3 : ℝ) ^ d / t * ∫ x, |b x| ∂volume :=
      volume_iUnion_euclideanBall_toReal_le s z R b t
        (fun x _ => hR x) ht hb (fun x _ => havg x)

end PDE
