module

public import PDEFoundation.Sobolev.Trace.Assembly.Basic
public import PDEFoundation.Sobolev.Trace.Density.Translation
public import PDEFoundation.Sobolev.Trace.Density.LocalMollify

/-!
# Translate-and-mollify approximation

Let `W, G` be `L^p(ℝ^d)` functions (value and gradient) such that `G` is the weak gradient of `W`
on an open set `O`.  Suppose that for all small `τ > 0` the translate `closure Ω + τ e` of the
closure of a bounded set `Ω` lies in `O`.  Then `(W, G)` is the `W^{1,p}(Ω)`-limit of smooth
functions: take `φ(x) = (ρ_δ ⋆ W)(x + τ e)`; for `x ∈ closure Ω` the ball of radius `δ` around
`x + τ e` lies in `O`, so `∇φ(x) = (ρ_δ ⋆ G)(x + τ e)`, and the error is controlled by the
convergence of mollification and the continuity of translation in `L^p(ℝ^d)`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal Convolution

variable {d : ℕ}

/-- The sum of the `L^q` seminorms of a value and the coordinates of a vector field. -/
noncomputable def pairSeminorm (μ : Measure (Vec d)) (q : ℝ≥0∞) (f : Vec d → ℝ)
    (F : Vec d → Vec d) : ℝ≥0∞ :=
  eLpNorm f q μ + ∑ i, eLpNorm (fun x => F x i) q μ

theorem w1pPairNorm_le_pairSeminorm {Ω : Set (Vec d)} {p : ℝ} (hp : 1 ≤ p) (f : Vec d → ℝ)
    {F : Vec d → Vec d} (hF : AEStronglyMeasurable F (volumeOn Ω)) :
    w1pPairNorm Ω p f F ≤ pairSeminorm (volumeOn Ω) (ENNReal.ofReal p) f F := by
  have hq : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  unfold w1pPairNorm pairSeminorm
  gcongr
  calc eLpNorm (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p) (volumeOn Ω)
      ≤ eLpNorm (∑ i, fun x => ‖F x i‖) (ENNReal.ofReal p) (volumeOn Ω) := by
        refine eLpNorm_mono (continuous_vecEuclideanNorm.comp_aestronglyMeasurable hF) fun x => ?_
        simp only [Finset.sum_apply, Real.norm_eq_abs]
        rw [abs_of_nonneg (vecEuclideanNorm_nonneg _), abs_of_nonneg
          (Finset.sum_nonneg fun i _ => abs_nonneg _)]
        exact vecEuclideanNorm_le_sum_abs _
    _ ≤ ∑ i, eLpNorm (fun x => ‖F x i‖) (ENNReal.ofReal p) (volumeOn Ω) :=
        eLpNorm_sum_le hq
    _ = ∑ i, eLpNorm (fun x => F x i) (ENNReal.ofReal p) (volumeOn Ω) := by
        refine Finset.sum_congr rfl fun i _ => eLpNorm_norm _ ?_
        exact (continuous_apply i).comp_aestronglyMeasurable hF

/-- Triangle-type bound for a function that is, on `Ω`, a translate of `A` plus `B`. -/
theorem eLpNorm_restrict_le_of_decomp {Ω : Set (Vec d)} (hΩ : MeasurableSet Ω) {q : ℝ≥0∞}
    (hq : 1 ≤ q) {f A B : Vec d → ℝ} (v : Vec d) (hf : ∀ x ∈ Ω, f x = A (x + v) + B x)
    (hA : AEStronglyMeasurable A volume) :
    eLpNorm f q (volumeOn Ω) ≤ eLpNorm A q volume + eLpNorm B q volume := by
  have hfe : f =ᵐ[volumeOn Ω] fun x => A (x + v) + B x :=
    (ae_restrict_iff' hΩ).2 (Eventually.of_forall hf)
  rw [eLpNorm_congr_ae hfe]
  refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
  refine (eLpNorm_add_le hq (f := fun x => A (x + v)) (g := B)).trans ?_
  rw [eLpNorm_comp_add_right hA v]

end PDE.TraceLane
