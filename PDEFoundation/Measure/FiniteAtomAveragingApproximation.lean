module

public import PDEFoundation.Measure.FiniteAtomAveragingContraction
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

@[expose] public section

namespace PDE

open MeasureTheory Set Function
open scoped ENNReal BigOperators

noncomputable section

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]

omit [MeasurableSpace α] in
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

private theorem finiteAtomAverage_finiteDisjointAtomSum_eq
    (μ : Measure α) [IsFiniteMeasure μ]
    (E : ι → Set α) (hE : ∀ i, MeasurableSet (E i))
    (hdisj : Pairwise (Disjoint on E))
    (v : ι → ℝ) (i : ι) (hμ : μ (E i) ≠ 0) :
    finiteAtomAverage μ (E i) (finiteDisjointAtomSum E v) = v i := by
  have hint : ∫ x in E i, finiteDisjointAtomSum E v x ∂μ =
      ∫ _x in E i, v i ∂μ := by
    apply integral_congr_ae
    exact ae_restrict_of_forall_mem (hE i) fun x hx =>
      finiteDisjointAtomSum_eq_of_mem E hdisj v hx
  unfold finiteAtomAverage
  rw [hint, setIntegral_const, smul_eq_mul, measureReal_def]
  have htop : μ (E i) ≠ ∞ := (measure_lt_top μ (E i)).ne
  have hpos : 0 < (μ (E i)).toReal := ENNReal.toReal_pos hμ htop
  rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]

/-- A finite disjoint atom function is fixed almost everywhere by averaging
over the same atoms. Zero-measure atoms are discarded only almost everywhere. -/
theorem finiteAtomAveraging_finiteDisjointAtomSum_ae_eq
    (μ : Measure α) [IsFiniteMeasure μ]
    (E : ι → Set α) (hE : ∀ i, MeasurableSet (E i))
    (hdisj : Pairwise (Disjoint on E)) (v : ι → ℝ) :
    finiteAtomAveraging μ E (finiteDisjointAtomSum E v) =ᵐ[μ]
      finiteDisjointAtomSum E v := by
  classical
  have hgood : ∀ᵐ x ∂μ, ∀ i, μ (E i) = 0 → x ∉ E i := by
    apply ae_all_iff.mpr
    intro i
    by_cases hi : μ (E i) = 0
    · filter_upwards [(measure_eq_zero_iff_ae_notMem.mp hi)] with x hx
      exact fun _ => hx
    · exact Filter.Eventually.of_forall fun _ h => (hi h).elim
  filter_upwards [hgood] with x hx
  by_cases hmem : ∃ i, x ∈ E i
  · obtain ⟨i, hxi⟩ := hmem
    have hμi : μ (E i) ≠ 0 := by
      intro hzero
      exact hx i hzero hxi
    rw [finiteDisjointAtomSum_eq_of_mem E hdisj v hxi]
    unfold finiteAtomAveraging finiteDisjointAtomSum
    rw [Finset.sum_eq_single i]
    · simp only [Set.indicator_of_mem hxi]
      change finiteAtomAverage μ (E i) (finiteDisjointAtomSum E v) = v i
      exact finiteAtomAverage_finiteDisjointAtomSum_eq μ E hE hdisj v i hμi
    · intro j _ hji
      have hxj : x ∉ E j := by
        intro hxj
        exact (Set.disjoint_left.mp (hdisj hji)) hxj hxi
      simp [hxj]
    · simp
  · push Not at hmem
    simp [finiteAtomAveraging, finiteDisjointAtomSum, hmem]

/-- Finite atom averaging respects subtraction when both functions are
integrable. -/
theorem finiteAtomAveraging_sub
    (μ : Measure α) (E : ι → Set α) {f g : α → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    finiteAtomAveraging μ E (f - g) =
      finiteAtomAveraging μ E f - finiteAtomAveraging μ E g := by
  funext x
  unfold finiteAtomAveraging finiteDisjointAtomSum finiteAtomAverage
  simp only [Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_sub hf.integrableOn hg.integrableOn]
  by_cases hxi : x ∈ E i <;> simp [hxi]
  ring

/-- Atom averaging approximates an `L²` function within twice the distance to
any function that is constant on the same disjoint atoms. -/
theorem eLpNorm_finiteAtomAveraging_sub_le_two_mul
    (μ : Measure α) [IsFiniteMeasure μ]
    (E : ι → Set α) (hE : ∀ i, MeasurableSet (E i))
    (hdisj : Pairwise (Disjoint on E))
    (f : α → ℝ) (hf : MemLp f 2 μ) (v : ι → ℝ) :
    eLpNorm (finiteAtomAveraging μ E f - f) 2 μ ≤
      2 * eLpNorm (f - finiteDisjointAtomSum E v) 2 μ := by
  let g : α → ℝ := finiteDisjointAtomSum E v
  have hg : MemLp g 2 μ := memLp_finiteDisjointAtomSum μ E hE v 2
  have hfi : Integrable f μ := hf.integrable (by norm_num)
  have hgi : Integrable g μ := hg.integrable (by norm_num)
  have hfix := finiteAtomAveraging_finiteDisjointAtomSum_ae_eq μ E hE hdisj v
  have hlinear := finiteAtomAveraging_sub μ E hfi hgi
  have hdecomp :
      finiteAtomAveraging μ E f - f =ᵐ[μ]
        finiteAtomAveraging μ E (f - g) + (g - f) := by
    filter_upwards [hfix] with x hx
    change finiteAtomAveraging μ E g x = g x at hx
    have hl := congrFun hlinear x
    change finiteAtomAveraging μ E f x - f x =
      finiteAtomAveraging μ E (f - g) x + (g - f) x
    rw [hl]
    simp only [Pi.sub_apply]
    rw [hx]
    ring
  have hdiff : MemLp (f - g) 2 μ := hf.sub hg
  have havg := eLpNorm_finiteAtomAveraging_le
    μ E hE hdisj (f - g) (p := (2 : ℝ)) (by norm_num) (by
      simpa only [ENNReal.ofReal_ofNat] using hdiff)
  rw [eLpNorm_congr_ae hdecomp]
  calc
    eLpNorm (finiteAtomAveraging μ E (f - g) + (g - f)) 2 μ ≤
        eLpNorm (finiteAtomAveraging μ E (f - g)) 2 μ +
          eLpNorm (g - f) 2 μ :=
      eLpNorm_add_le (by norm_num)
    _ ≤ eLpNorm (f - g) 2 μ + eLpNorm (g - f) 2 μ :=
      add_le_add (by simpa only [ENNReal.ofReal_ofNat] using havg) le_rfl
    _ = 2 * eLpNorm (f - g) 2 μ := by
      rw [show g - f = -(f - g) by funext x; simp]
      rw [eLpNorm_neg]
      ring

end

end PDE
