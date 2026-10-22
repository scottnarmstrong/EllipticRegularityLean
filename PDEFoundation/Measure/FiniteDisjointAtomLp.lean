module

public import PDEFoundation.Measure.DisjointSupportLpNorm
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

namespace PDE

open MeasureTheory Set Function
open scoped ENNReal BigOperators

noncomputable section

variable {α ι : Type*} [Fintype ι]

/-- A real finite atom function, written literally as a sum of indicators. -/
def finiteDisjointAtomSum (E : ι → Set α) (v : ι → ℝ) : α → ℝ :=
  fun x => ∑ i, (E i).indicator (fun _ => v i) x

private theorem finiteDisjointAtomSum_eq_of_mem
    (E : ι → Set α) (hdisj : Pairwise (Disjoint on E)) (v : ι → ℝ)
    {i : ι} {x : α} (hxi : x ∈ E i) :
    finiteDisjointAtomSum E v x = v i := by
  classical
  unfold finiteDisjointAtomSum
  rw [Finset.sum_eq_single i]
  · simp [hxi]
  · intro j _ hji
    have hxj : x ∉ E j := by
      intro hxj
      exact (Set.disjoint_left.mp (hdisj hji)) hxj hxi
    simp [hxj]
  · simp

private theorem finiteDisjointAtomSum_eq_zero_of_not_mem
    (E : ι → Set α) (v : ι → ℝ) {x : α}
    (hx : ∀ i, x ∉ E i) :
    finiteDisjointAtomSum E v x = 0 := by
  classical
  simp [finiteDisjointAtomSum, hx]

variable [MeasurableSpace α]

/-- The literal finite atom sum is measurable. -/
theorem measurable_finiteDisjointAtomSum
    (E : ι → Set α) (hE : ∀ i, MeasurableSet (E i)) (v : ι → ℝ) :
    Measurable (finiteDisjointAtomSum E v) := by
  classical
  exact Finset.measurable_sum _ fun i _ => measurable_const.indicator (hE i)

/-- Exact extended moment of a finite real sum on pairwise disjoint atoms. -/
theorem lintegral_enorm_finiteDisjointAtomSum_rpow
    (μ : Measure α) (E : ι → Set α) (hE : ∀ i, MeasurableSet (E i))
    (hdisj : Pairwise (Disjoint on E)) (v : ι → ℝ)
    {p : ℝ} (hp : 0 < p) :
    (∫⁻ x, ‖finiteDisjointAtomSum E v x‖ₑ ^ p ∂μ) =
      ∑ i, μ (E i) * ENNReal.ofReal |v i| ^ p := by
  classical
  have hpoint : ∀ x,
      ‖finiteDisjointAtomSum E v x‖ₑ ^ p =
        ∑ i, (E i).indicator (fun _ => ENNReal.ofReal |v i| ^ p) x := by
    intro x
    by_cases hx : ∃ i, x ∈ E i
    · obtain ⟨i, hxi⟩ := hx
      rw [finiteDisjointAtomSum_eq_of_mem E hdisj v hxi]
      rw [Finset.sum_eq_single i]
      · simp [hxi, Real.enorm_eq_ofReal_abs]
      · intro j _ hji
        have hxj : x ∉ E j := by
          intro hxj
          exact (Set.disjoint_left.mp (hdisj hji)) hxj hxi
        simp [hxj]
      · simp
    · push Not at hx
      rw [finiteDisjointAtomSum_eq_zero_of_not_mem E v hx]
      simp [hx, ENNReal.zero_rpow_of_pos hp]
  simp_rw [hpoint]
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [lintegral_indicator (hE i), setLIntegral_const]
    exact mul_comm _ _
  · intro i _
    exact measurable_const.indicator (hE i)

/-- A finite real atom sum belongs to every extended `Lᵖ` space on a finite
measure space. -/
theorem memLp_finiteDisjointAtomSum
    (μ : Measure α) [IsFiniteMeasure μ]
    (E : ι → Set α) (hE : ∀ i, MeasurableSet (E i))
    (v : ι → ℝ) (p : ENNReal) :
    MemLp (finiteDisjointAtomSum E v) p μ := by
  classical
  unfold finiteDisjointAtomSum
  simpa only [Finset.sum_apply] using
    (memLp_finsetSum (p := p) Finset.univ fun i _ =>
      memLp_indicator_const p (hE i) (v i)
        (Or.inr (measure_lt_top μ (E i)).ne))

/-- The positive power of the finite atom sum's `Lᵖ` seminorm is exactly its
weighted atomic moment. -/
theorem eLpNorm_finiteDisjointAtomSum_rpow
    (μ : Measure α) (E : ι → Set α) (hE : ∀ i, MeasurableSet (E i))
    (hdisj : Pairwise (Disjoint on E)) (v : ι → ℝ)
    {p : ℝ} (hp : 0 < p) :
    eLpNorm (finiteDisjointAtomSum E v) (ENNReal.ofReal p) μ ^ p =
      ∑ i, μ (E i) * ENNReal.ofReal |v i| ^ p := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top
    (measurable_finiteDisjointAtomSum E hE v).aestronglyMeasurable,
    ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul]
  have hp0 : p ≠ 0 := hp.ne'
  rw [one_div_mul_cancel hp0, ENNReal.rpow_one]
  exact lintegral_enorm_finiteDisjointAtomSum_rpow μ E hE hdisj v hp

/-- On a finite measure space, the real `p`-power of the atom sum's seminorm
is the literal real weighted moment. -/
theorem eLpNorm_finiteDisjointAtomSum_toReal_rpow
    (μ : Measure α) [IsFiniteMeasure μ]
    (E : ι → Set α) (hE : ∀ i, MeasurableSet (E i))
    (hdisj : Pairwise (Disjoint on E)) (v : ι → ℝ)
    {p : ℝ} (hp : 0 < p) :
    (eLpNorm (finiteDisjointAtomSum E v) (ENNReal.ofReal p) μ).toReal ^ p =
      ∑ i, (μ (E i)).toReal * |v i| ^ p := by
  have h := congrArg ENNReal.toReal
    (eLpNorm_finiteDisjointAtomSum_rpow μ E hE hdisj v hp)
  rw [← ENNReal.toReal_rpow] at h
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top
    (measure_lt_top μ (E i)).ne
    (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top))] at h
  simp only [ENNReal.toReal_mul] at h
  simp_rw [← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (abs_nonneg _)] at h
  exact h

end

end PDE
