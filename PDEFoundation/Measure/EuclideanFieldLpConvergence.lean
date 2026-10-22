module

public import PDEFoundation.Measure.FiniteVectorConvergence
public import PDEFoundation.Sobolev.W1p.EuclideanGradient

/-! # Coordinatewise convergence of native Euclidean fields -/

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open Filter MeasureTheory

/-- Coordinatewise strong `Lᵖ` convergence of native finite vector fields
implies strong `Lᵖ` convergence of their exact Euclidean difference. -/
theorem tendsto_eLpNorm_euclideanField_sub_zero_of_coordinate
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {m : ℕ} {p : ENNReal} {gSeq : ℕ → α → Vec m} {g : α → Vec m}
    (hp : 1 ≤ p) (_hpTop : p ≠ ∞)
    (hgSeq : ∀ n i, MemLp (fun x => gSeq n x i) p μ)
    (hg : ∀ i, MemLp (fun x => g x i) p μ)
    (hcoord : ∀ i, Tendsto
      (fun n => eLpNorm (fun x => gSeq n x i - g x i) p μ)
      atTop (𝓝 0)) :
    Tendsto
      (fun n => eLpNorm
        (fun x => vecEuclideanNorm (gSeq n x - g x)) p μ)
      atTop (𝓝 0) := by
  have hsub (n : ℕ) (i : Fin m) :
      MemLp (fun x => gSeq n x i - g x i) p μ :=
    (hgSeq n i).sub (hg i)
  have hmag (n : ℕ) :
      MemLp (fun x => vecEuclideanNorm (gSeq n x - g x)) p μ := by
    let H : α → Vec m := fun x => gSeq n x - g x
    have hHilbert : MemLp (fun x => (H x).toHilbertVec) p μ := by
      simpa only [Vec.toHilbertVec_apply, H, Pi.sub_apply] using
        (memLp_piLp_iff (f := fun x => (H x).toHilbertVec) (p := p) (μ := μ)).mpr
          (hsub n)
    exact hHilbert.norm.ae_eq (Filter.Eventually.of_forall fun x =>
      (Vec.vecEuclideanNorm_eq_norm_toHilbertVec (H x)).symm)
  apply tendsto_eLpNorm_vecEuclideanNorm_sub_zero_of_coordinate hp
  · intro n i
    exact (hsub n i).aestronglyMeasurable
  · exact hcoord

end PDE
