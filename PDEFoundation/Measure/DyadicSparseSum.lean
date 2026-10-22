module

public import PDEFoundation.Measure.FiniteSparseStrongNorm
public import PDEFoundation.Measure.DirectedLpBound

/-! # Literal countable dyadic sparse sums -/

@[expose] public section

namespace PDE

open BoxIntegral MeasureTheory Set
open scoped _root_.ENNReal

noncomputable section

variable {d : ℕ}

/-- The literal nonnegative countable sum over a set of dyadic paths. -/
def dyadicSparseSum (I : Box (Fin d))
    (S : Set (List (Set (Fin d))))
    (a : List (Set (Fin d)) → ℝ) (x : Vec d) : ENNReal :=
  ∑' q : List (Set (Fin d)),
    S.indicator (fun q => ENNReal.ofReal
      ((dyadicDescendant I q : Set (Vec d)).indicator (fun _ => a q) x)) q

/-- The elements of a finite set which belong to an arbitrary set. -/
noncomputable def finsetWithinSet {α : Type*} (T : Finset α) (S : Set α) : Finset α := by
  classical
  exact T.filter (· ∈ S)

theorem mem_finsetWithinSet {α : Type*} (T : Finset α) (S : Set α) (x : α) :
    x ∈ finsetWithinSet T S ↔ x ∈ T ∧ x ∈ S := by
  classical
  simp [finsetWithinSet]

/-- A literal dyadic sparse sum is measurable. -/
theorem measurable_dyadicSparseSum (I : Box (Fin d))
    (S : Set (List (Set (Fin d))))
    (a : List (Set (Fin d)) → ℝ) :
    Measurable (dyadicSparseSum I S a) := by
  unfold dyadicSparseSum
  apply Measurable.tsum
  intro q
  by_cases hq : q ∈ S
  · simp only [Set.indicator_of_mem hq]
    exact ((measurable_const.indicator (measurableSet_dyadicDescendant I q)).ennreal_ofReal)
  · simp only [Set.indicator_of_notMem hq]
    exact measurable_const

/-- The countable sparse sum is the supremum of its literal finite partial
sums. -/
theorem dyadicSparseSum_eq_iSup_finiteSparseSum
    (I : Box (Fin d)) (S : Set (List (Set (Fin d))))
    (a : List (Set (Fin d)) → ℝ)
    (ha : ∀ q ∈ S, 0 ≤ a q) (x : Vec d) :
    dyadicSparseSum I S a x =
      ⨆ T : Finset (List (Set (Fin d))),
        ENNReal.ofReal (finiteSparseSum I (finsetWithinSet T S) a x) := by
  classical
  rw [dyadicSparseSum, ENNReal.tsum_eq_iSup_sum]
  congr 1
  funext T
  rw [finiteSparseSum, ENNReal.ofReal_sum_of_nonneg]
  · rw [finsetWithinSet, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hqS : q ∈ S
    · simp only [hqS, Set.indicator_of_mem, ite_eq_left]
    · simp [Set.indicator, hqS]
  · intro q hq
    exact Set.indicator_nonneg (fun _ _ => ha q (mem_finsetWithinSet T S q |>.mp hq).2) x

/-- The actual countable sparse sum inherits the sharp finite sparse norm
bound from all of its finite partial sums. -/
theorem eLpNorm_dyadicSparseSum_le
    (I : Box (Fin d)) (S : Set (List (Set (Fin d))))
    (b : Vec d → ℝ) (a : List (Set (Fin d)) → ℝ)
    (E : List (Set (Fin d)) → Set (Vec d))
    (ha : ∀ q ∈ S, 0 ≤ a q)
    (hE : ∀ q ∈ S, MeasurableSet (E q))
    (hsub : ∀ q ∈ S, E q ⊆ (dyadicDescendant I q : Set (Vec d)))
    (hdisj : S.PairwiseDisjoint E)
    (hpacking : ∀ q ∈ S, ENNReal.ofReal (3 / 4 : ℝ) *
      volume (dyadicDescendant I q : Set (Vec d)) ≤ volume (E q))
    (hminor : ∀ q ∈ S,
      ∀ᵐ x ∂volume.restrict (dyadicDescendant I q : Set (Vec d)),
        a q ≤ |b x|)
    {p : ℝ} (hp : 1 < p)
    (hb : MemLp b (ENNReal.ofReal p)
      (volume.restrict (I : Set (Vec d)))) :
    eLpNorm (dyadicSparseSum I S a) (ENNReal.ofReal p)
        (volume.restrict (I : Set (Vec d))) ≤
      ENNReal.ofReal ((4 / 3 : ℝ) * p) *
        eLpNorm b (ENNReal.ofReal p)
          (volume.restrict (I : Set (Vec d))) := by
  classical
  let μ := volume.restrict (I : Set (Vec d))
  let F : Finset (List (Set (Fin d))) → Vec d → ENNReal := fun T x =>
    ENNReal.ofReal (finiteSparseSum I (finsetWithinSet T S) a x)
  let K := ENNReal.ofReal ((4 / 3 : ℝ) * p) *
    eLpNorm b (ENNReal.ofReal p) μ
  have hFTmeas : ∀ T, Measurable (F T) := fun T =>
    (measurable_finiteSparseSum I (finsetWithinSet T S) a).ennreal_ofReal
  have hpartial (T : Finset (List (Set (Fin d)))) :
      eLpNorm (F T) (ENNReal.ofReal p) μ ≤ K := by
    let R := finsetWithinSet T S
    have hR (q) (hq : q ∈ R) : q ∈ S := (mem_finsetWithinSet T S q).mp hq |>.2
    have hreal := eLpNorm_finiteSparseSum_le I R b a E
      (fun q hq => ha q (hR q hq))
      (fun q hq => hE q (hR q hq))
      (fun q hq => hsub q (hR q hq))
      (by
        intro q hq r hr hqr
        exact hdisj (hR q hq) (hR r hr) hqr)
      (fun q hq => hpacking q (hR q hq))
      (fun q hq => hminor q (hR q hq)) hp hb
    have hnonneg : ∀ x, 0 ≤ finiteSparseSum I R a x :=
      finiteSparseSum_nonneg I R a (fun q hq => ha q (hR q hq))
    have hnorm : eLpNorm (F T) (ENNReal.ofReal p) μ =
        eLpNorm (finiteSparseSum I R a) (ENNReal.ofReal p) μ := by
      exact eLpNorm_ofReal _ (ae_of_all μ hnonneg)
    simpa only [F, R, K] using hnorm.trans_le hreal
  have hdir : Directed (· ≤ ·) F := by
    intro T U
    refine ⟨T ∪ U, ?_, ?_⟩
    · intro x
      apply ENNReal.ofReal_le_ofReal
      unfold finiteSparseSum
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        apply (mem_finsetWithinSet (T ∪ U) S q).mpr
        exact ⟨Finset.mem_union_left U (mem_finsetWithinSet T S q |>.mp hq).1,
          (mem_finsetWithinSet T S q |>.mp hq).2⟩
      · intro q _hq _hnot
        exact Set.indicator_nonneg (fun _ _ => ha q
          (mem_finsetWithinSet (T ∪ U) S q |>.mp _hq).2) x
    · intro x
      apply ENNReal.ofReal_le_ofReal
      unfold finiteSparseSum
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        apply (mem_finsetWithinSet (T ∪ U) S q).mpr
        exact ⟨Finset.mem_union_right T (mem_finsetWithinSet U S q |>.mp hq).1,
          (mem_finsetWithinSet U S q |>.mp hq).2⟩
      · intro q _hq _hnot
        exact Set.indicator_nonneg (fun _ _ => ha q
          (mem_finsetWithinSet (T ∪ U) S q |>.mp _hq).2) x
  have hsup := eLpNorm_iSup_le_of_directed μ F hFTmeas hdir
    (zero_lt_one.trans hp) hpartial
  have hpoint : (fun x => ⨆ T, F T x) = dyadicSparseSum I S a := by
    funext x
    exact (dyadicSparseSum_eq_iSup_finiteSparseSum I S a ha x).symm
  rw [hpoint] at hsup
  exact hsup

end

end PDE
