module

public import PDEFoundation.Measure.EuclideanFieldLpConvergence
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # One almost-everywhere subsequence for finitely many coordinates -/

@[expose] public section

namespace PDE

open Filter MeasureTheory
open scoped ENNReal Topology BigOperators

/-- Finitely many coordinatewise strong `L²` convergences have one shared
strictly monotone subsequence converging almost everywhere in every coordinate. -/
theorem exists_strictMono_ae_tendsto_all_coordinates_of_eLpNorm_two
    {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {μ : Measure α} [IsFiniteMeasure μ]
    {gSeq : ℕ → α → ι → ℝ} {g : α → ι → ℝ}
    (hgSeq : ∀ n i, MemLp (fun x => gSeq n x i) 2 μ)
    (hg : ∀ i, MemLp (fun x => g x i) 2 μ)
    (hcoord : ∀ i, Tendsto
      (fun n => eLpNorm (fun x => gSeq n x i - g x i) 2 μ)
      atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ x ∂μ, ∀ i,
      Tendsto (fun n => gSeq (φ n) x i) atTop (𝓝 (g x i)) := by
  let q : ℕ → α → ℝ := fun n x => ∑ i : ι, |gSeq n x i - g x i|
  have hdiff (n : ℕ) (i : ι) :
      MemLp (fun x => gSeq n x i - g x i) 2 μ :=
    (hgSeq n i).sub (hg i)
  have habs (n : ℕ) (i : ι) :
      MemLp (fun x => |gSeq n x i - g x i|) 2 μ := by
    simpa only [Real.norm_eq_abs] using (hdiff n i).norm
  have hqMem (n : ℕ) : MemLp (q n) 2 μ := by
    dsimp only [q]
    exact memLp_finsetSum Finset.univ fun i _ => habs n i
  have habsConv (i : ι) : Tendsto
      (fun n => eLpNorm (fun x => |gSeq n x i - g x i|) 2 μ)
      atTop (𝓝 0) := by
    have heq : (fun n =>
        eLpNorm (fun x => |gSeq n x i - g x i|) 2 μ) =
        fun n => eLpNorm (fun x => gSeq n x i - g x i) 2 μ := by
      funext n
      simpa only [Real.norm_eq_abs] using!
        eLpNorm_norm (fun x => gSeq n x i - g x i) (p := 2) (μ := μ)
          (hdiff n i).aestronglyMeasurable
    rw [heq]
    exact hcoord i
  have hsum : Tendsto
      (fun n => ∑ i : ι,
        eLpNorm (fun x => |gSeq n x i - g x i|) 2 μ)
      atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using!
      tendsto_finsetSum Finset.univ (fun i _ => habsConv i)
  have hqNorm : Tendsto (fun n => eLpNorm (q n) 2 μ) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    · exact fun _ => zero_le
    · intro n
      dsimp only [q]
      rw [← Finset.sum_fn]
      exact eLpNorm_sum_le (s := Finset.univ)
        (by norm_num)
  have hqMeasure : TendstoInMeasure μ q atTop (fun _ => 0) := by
    apply tendstoInMeasure_of_tendsto_eLpNorm (p := (2 : ENNReal)) (by norm_num)
    have heq (n : ℕ) : q n - (fun _ => 0) = q n := by
      funext x
      simp
    simpa only [heq] using hqNorm
  obtain ⟨φ, hφ, hqAe⟩ := hqMeasure.exists_seq_tendsto_ae
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hqAe] with x hx
  intro i
  have habsLe : ∀ n,
      |gSeq (φ n) x i - g x i| ≤ q (φ n) x := by
    intro n
    exact Finset.single_le_sum
      (fun j _ => abs_nonneg (gSeq (φ n) x j - g x j)) (Finset.mem_univ i)
  have habsTend : Tendsto
      (fun n => |gSeq (φ n) x i - g x i|) atTop (𝓝 0) := by
    exact squeeze_zero' (Eventually.of_forall fun n => abs_nonneg _)
      (Eventually.of_forall habsLe) hx
  have hdiffTend : Tendsto
      (fun n => gSeq (φ n) x i - g x i) atTop (𝓝 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).2 habsTend
  exact tendsto_sub_nhds_zero_iff.1 hdiffTend

end PDE
