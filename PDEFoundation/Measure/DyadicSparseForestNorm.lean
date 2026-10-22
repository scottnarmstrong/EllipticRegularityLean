module

public import PDEFoundation.Measure.DyadicSparseEssentialInfNorm
public import PDEFoundation.Measure.DyadicSparseForestSupport
public import PDEFoundation.Measure.DisjointSupportLpNorm

/-! # Strong norm of a dyadic sparse forest -/

@[expose] public section

namespace PDE

open BoxIntegral MeasureTheory Set Function
open scoped _root_.ENNReal

noncomputable section

variable {d m : ℕ} {ρ : Type*}

/-- Sparse sums generated independently inside countably many boxes with
disjoint interiors satisfy the same strong bound as a single sparse sum. -/
theorem eLpNorm_dyadicSparseForest_le [Countable ρ]
    (root : ρ → Box (Fin d))
    (hroot : Pairwise fun i j => Disjoint (Box.Ioo (root i)) (Box.Ioo (root j)))
    (g : ρ → Vec d → Vec m)
    (hg : ∀ i j, MemLp (fun x => g i x j) 2
      (volumeOn (root i : Set (Vec d))))
    (b : Vec d → ℝ) {p : ℝ} (hp : 1 < p)
    (hb : MemLp b (ENNReal.ofReal p) volume) :
    eLpNorm
        (fun x => ∑' i,
          dyadicSparseSum (root i) (dyadicSparseFamily (root i) (g i))
            (dyadicBoxEssentialInfReal (root i) b) x)
        (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((4 / 3 : ℝ) * p) *
        eLpNorm b (ENNReal.ofReal p) volume := by
  let U : ρ → Set (Vec d) := fun i => (root i : Set (Vec d))
  let f : ρ → Vec d → ENNReal := fun i =>
    dyadicSparseSum (root i) (dyadicSparseFamily (root i) (g i))
      (dyadicBoxEssentialInfReal (root i) b)
  let bnn : Vec d → ENNReal := fun x => ENNReal.ofReal |b x|
  have hUmeas : ∀ i, MeasurableSet (U i) := fun i => (root i).measurableSet_coe
  have hU : Pairwise (Disjoint on U) := by
    intro i j hij
    exact disjoint_coe_of_disjoint_Ioo (root i) (root j) (hroot hij)
  have hfmeas : ∀ i, Measurable (f i) := fun i =>
    measurable_dyadicSparseSum (root i) (dyadicSparseFamily (root i) (g i))
      (dyadicBoxEssentialInfReal (root i) b)
  have hf0 : ∀ i x, x ∉ U i → f i x = 0 := by
    intro i x hx
    exact dyadicSparseSum_eq_zero_of_not_mem (root i)
      (dyadicSparseFamily (root i) (g i))
      (dyadicBoxEssentialInfReal (root i) b) hx
  have hbnn (μ : Measure (Vec d)) (hbμ : AEStronglyMeasurable b μ) :
      eLpNorm bnn (ENNReal.ofReal p) μ = eLpNorm b (ENNReal.ofReal p) μ := by
    calc
      eLpNorm bnn (ENNReal.ofReal p) μ =
          eLpNorm (fun x => |b x|) (ENNReal.ofReal p) μ :=
        eLpNorm_ofReal _ (ae_of_all μ fun x => abs_nonneg (b x))
      _ = eLpNorm b (ENNReal.ofReal p) μ := by
        simpa only [Real.norm_eq_abs] using!
          (eLpNorm_norm (μ := μ) (p := ENNReal.ofReal p) b hbμ)
  have hbound : ∀ i,
      eLpNorm (f i) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal ((4 / 3 : ℝ) * p) *
          eLpNorm bnn (ENNReal.ofReal p) (volume.restrict (U i)) := by
    intro i
    have hsupp : Function.support (f i) ⊆ U i := by
      intro x hx
      by_contra hxU
      exact hx (hf0 i x hxU)
    calc
      eLpNorm (f i) (ENNReal.ofReal p) volume =
          eLpNorm (f i) (ENNReal.ofReal p) (volume.restrict (U i)) :=
        (eLpNorm_restrict_eq_of_support_subset (hfmeas i).aestronglyMeasurable hsupp).symm
      _ ≤ ENNReal.ofReal ((4 / 3 : ℝ) * p) *
          eLpNorm b (ENNReal.ofReal p) (volume.restrict (U i)) :=
        eLpNorm_dyadicSparseSum_essentialInf_le (root i) (g i) (hg i) b hp
          (hb.mono_measure Measure.restrict_le_self)
      _ = ENNReal.ofReal ((4 / 3 : ℝ) * p) *
          eLpNorm bnn (ENNReal.ofReal p) (volume.restrict (U i)) := by
        rw [hbnn _ hb.aestronglyMeasurable.restrict]
  have hglue := eLpNorm_tsum_le_of_pairwiseDisjoint volume U hUmeas hU f
    hfmeas hf0 bnn (lt_trans (by norm_num) hp)
    (ENNReal.ofReal ((4 / 3 : ℝ) * p)) hbound
  simpa only [f, bnn, hbnn volume hb.aestronglyMeasurable] using hglue

end

end PDE
