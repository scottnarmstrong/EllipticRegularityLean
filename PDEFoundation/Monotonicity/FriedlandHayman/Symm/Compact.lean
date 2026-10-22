module

public import PDEFoundation.Monotonicity.FriedlandHayman.Symm.Orbit
public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Friedland--Hayman: compactness of the polarization hull and the height-moment maximizer

The closure `Hull g e` of the polarization orbit is compact in the sup norm (Arzelà--Ascoli, with
the common Lipschitz constant and sup bound), so the continuous height moment attains its maximum
on it.
-/

@[expose] public section

open MeasureTheory Metric Set

namespace PDE.FHLane.Rearr

noncomputable section

variable {D : ℕ}

/-- The pointwise-closed family of `L`-Lipschitz functions with values in `[0, M]`. -/
def LipBox (D : ℕ) (L : NNReal) (M : ℝ) : Set (Sph D → ℝ) :=
  {f | (∀ x, f x ∈ Icc 0 M) ∧ ∀ x y, dist (f x) (f y) ≤ L * dist x y}

theorem isCompact_lipBox (L : NNReal) (M : ℝ) : IsCompact (LipBox D L M) := by
  have hc : IsClosed (LipBox D L M) := by
    have h1 : IsClosed {f : Sph D → ℝ | ∀ x, f x ∈ Icc 0 M} := by
      rw [ofPred_forall]
      exact isClosed_iInter fun x => isClosed_Icc.preimage (continuous_apply x)
    have h2 : IsClosed {f : Sph D → ℝ | ∀ x y, dist (f x) (f y) ≤ L * dist x y} := by
      rw [ofPred_forall]
      refine isClosed_iInter fun x => ?_
      rw [ofPred_forall]
      exact isClosed_iInter fun y =>
        isClosed_le (((continuous_apply x).dist (continuous_apply y))) continuous_const
    exact h1.inter h2
  refine IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ => isCompact_Icc (a := 0) (b := M))
    hc fun f hf x _ => hf.1 x

theorem isCompact_hull {g : C(Sph D, ℝ)} {L : NNReal} {M : ℝ} (hg : Inv g L M g)
    (e : HilbertVec D) : IsCompact (Hull g e) := by
  set C : Set C(Sph D, ℝ) := {k | LipschitzWith L k ∧ ∀ x, k x ∈ Icc 0 M} with hC
  have himg : ContinuousMap.toFun '' C = LipBox D L M := by
    ext f
    constructor
    · rintro ⟨k, ⟨hk, hb⟩, rfl⟩
      exact ⟨hb, fun x y => hk.dist_le_mul x y⟩
    · intro hf
      have hlip : LipschitzWith L f := LipschitzWith.of_dist_le_mul hf.2
      exact ⟨⟨f, hlip.continuous⟩, ⟨hlip, hf.1⟩, rfl⟩
  have hCc : IsCompact C := by
    refine ArzelaAscoli.isCompact_of_equicontinuous C ?_ ?_
    · rw [himg]; exact isCompact_lipBox L M
    · exact (LipschitzWith.uniformEquicontinuous (fun (k : C) (x : Sph D) => (k : C(Sph D, ℝ)) x) L
        fun k => k.2.1).equicontinuous
  refine hCc.of_isClosed_subset isClosed_closure fun k hk => ?_
  obtain ⟨h0, hM, hL, -⟩ := hull_inv hg hk
  exact ⟨hL, fun x => ⟨h0 x, hM x⟩⟩

/-- The height moment. -/
def moment (e : HilbertVec D) (k : C(Sph D, ℝ)) : ℝ :=
  ∫ x, k x * inner ℝ (x : HilbertVec D) e ∂(sphMeasure D)

theorem exists_max_moment {g : C(Sph D, ℝ)} {L : NNReal} {M : ℝ} (hg : Inv g L M g)
    (e : HilbertVec D) : ∃ k ∈ Hull g e, ∀ k' ∈ Hull g e, moment e k' ≤ moment e k :=
  (isCompact_hull hg e).exists_isMaxOn ⟨g, self_mem_hull g e⟩ (continuous_moment e).continuousOn

end

end PDE.FHLane.Rearr
