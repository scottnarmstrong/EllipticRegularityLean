module

public import PDEFoundation.Ambient.HilbertVec
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Geometry.Euclidean.Volume.Measure

/-!
# A generic grid of small cubes adapted to a compact set

Given a compact `S ⊆ HilbertVec d`, a measure `μ` with `μ S < ∞` and `λ > 0`, there is a finite
family of disjoint half-open lattice cubes covering a neighbourhood `cthickening δ S`, each closed
cube lying in a ball of radius `λ` centred on `S`, with `Σ μ(S ∩ closed cube) ≤ μ S`.  The lattice
offset is chosen so that every face hyperplane meets `S` in a `μ`-null set: only countably many
parallel hyperplanes can carry positive mass.
-/

@[expose] public section

namespace PDE.IsoperimetricProof

open MeasureTheory Set Metric Function

variable {d : ℕ}

/-- The half-open lattice cube with offset `a`, side `h` and index `k`. -/
def gridCell (a : Fin d → ℝ) (h : ℝ) (k : Fin d → ℤ) : Set (HilbertVec d) :=
  {x | ∀ i, a i + k i * h ≤ x i ∧ x i < a i + (k i + 1) * h}

/-- The closed lattice cube. -/
def gridCellClosed (a : Fin d → ℝ) (h : ℝ) (k : Fin d → ℤ) : Set (HilbertVec d) :=
  {x | ∀ i, a i + k i * h ≤ x i ∧ x i ≤ a i + (k i + 1) * h}

theorem continuous_hilbertVec_apply (i : Fin d) : Continuous fun x : HilbertVec d => x i :=
  PiLp.continuous_apply 2 _ i

theorem measurableSet_gridCell (a : Fin d → ℝ) (h : ℝ) (k : Fin d → ℤ) :
    MeasurableSet (gridCell a h k) := by
  have : gridCell a h k = ⋂ i, (fun x : HilbertVec d => x i) ⁻¹' Ico (a i + k i * h)
      (a i + (k i + 1) * h) := by
    ext x; simp [gridCell, mem_iInter]
  rw [this]
  exact MeasurableSet.iInter fun i =>
    (continuous_hilbertVec_apply i).measurable measurableSet_Ico

theorem isClosed_gridCellClosed (a : Fin d → ℝ) (h : ℝ) (k : Fin d → ℤ) :
    IsClosed (gridCellClosed a h k) := by
  have : gridCellClosed a h k = ⋂ i, (fun x : HilbertVec d => x i) ⁻¹' Icc (a i + k i * h)
      (a i + (k i + 1) * h) := by
    ext x; simp [gridCellClosed, mem_iInter]
  rw [this]
  exact isClosed_iInter fun i => isClosed_Icc.preimage (continuous_hilbertVec_apply i)

theorem gridCell_subset_closed (a : Fin d → ℝ) (h : ℝ) (k : Fin d → ℤ) :
    gridCell a h k ⊆ gridCellClosed a h k := fun _ hx i => ⟨(hx i).1, (hx i).2.le⟩

theorem int_eq_of_floor_bounds {h t : ℝ} (hh : 0 < h) {m n : ℤ} (hm1 : m * h ≤ t)
    (hm2 : t < (m + 1) * h) (hn1 : n * h ≤ t) (hn2 : t < (n + 1) * h) : m = n := by
  have h1 : (m : ℝ) < n + 1 := by
    by_contra hc; push Not at hc; nlinarith
  have h2 : (n : ℝ) < m + 1 := by
    by_contra hc; push Not at hc; nlinarith
  have h1' : m < n + 1 := by exact_mod_cast h1
  have h2' : n < m + 1 := by exact_mod_cast h2
  omega

theorem pairwise_disjoint_gridCell (a : Fin d → ℝ) {h : ℝ} (hh : 0 < h) :
    Pairwise (Disjoint on gridCell a h) := by
  intro k k' hkk'
  rw [Function.onFun, Set.disjoint_left]
  intro x hx hx'
  apply hkk'
  funext i
  exact int_eq_of_floor_bounds (t := x i - a i) hh (by linarith [(hx i).1])
    (by linarith [(hx i).2]) (by linarith [(hx' i).1]) (by linarith [(hx' i).2])

/-- Every point lies in the cube indexed by the floors of its rescaled coordinates. -/
theorem mem_gridCell_floor (a : Fin d → ℝ) {h : ℝ} (hh : 0 < h) (x : HilbertVec d) :
    x ∈ gridCell a h (fun i => ⌊(x i - a i) / h⌋) := by
  intro i
  have h1 := Int.floor_le ((x i - a i) / h)
  have h2 := Int.lt_floor_add_one ((x i - a i) / h)
  constructor
  · have := (le_div_iff₀ hh).1 h1; linarith
  · have := (div_lt_iff₀ hh).1 h2; linarith

theorem dist_le_of_mem_gridCellClosed (a : Fin d → ℝ) {h : ℝ} (hh : 0 < h) (k : Fin d → ℤ)
    {x y : HilbertVec d} (hx : x ∈ gridCellClosed a h k) (hy : y ∈ gridCellClosed a h k) :
    dist x y ≤ Real.sqrt d * h := by
  rw [PiLp.dist_eq_of_L2]
  have hterm : ∀ i, dist (x i) (y i) ^ 2 ≤ h ^ 2 := by
    intro i
    rw [Real.dist_eq, sq_abs]
    have h1 := hx i; have h2 := hy i
    nlinarith
  calc Real.sqrt (∑ i, dist (x i) (y i) ^ 2) ≤ Real.sqrt (∑ _i : Fin d, h ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => hterm i)
    _ = Real.sqrt d * h := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hh.le]

/-- The boundary of a closed cube lies in the upper faces of the half-open cube. -/
theorem gridCellClosed_diff_subset (a : Fin d → ℝ) (h : ℝ) (k : Fin d → ℤ) :
    gridCellClosed a h k \ gridCell a h k ⊆
      ⋃ i, {x : HilbertVec d | x i = a i + (k i + 1) * h} := by
  rintro x ⟨hx, hnx⟩
  simp only [gridCell, mem_ofPred_eq, not_forall] at hnx
  obtain ⟨i, hi⟩ := hnx
  refine mem_iUnion.2 ⟨i, ?_⟩
  have := hx i
  by_contra hne
  exact hi ⟨this.1, lt_of_le_of_ne this.2 hne⟩

/-- Only countably many hyperplanes `{x i = c}` meet `S` in positive `μ`-measure. -/
theorem countable_bad_levels (μ : Measure (HilbertVec d)) {S : Set (HilbertVec d)}
    (hfin : μ S ≠ ⊤) (i : Fin d) :
    {c : ℝ | 0 < μ (S ∩ {x : HilbertVec d | x i = c})}.Countable := by
  have : IsFiniteMeasure (μ.restrict S) := ⟨by rwa [Measure.restrict_apply_univ, lt_top_iff_ne_top]⟩
  have hc := Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ.restrict S)
    (As := fun c : ℝ => {x : HilbertVec d | x i = c})
    (fun c => (isClosed_eq (continuous_hilbertVec_apply i) continuous_const).measurableSet)
    (fun c c' hcc' => by
      rw [Function.onFun, Set.disjoint_left]
      intro x hx hx'
      exact hcc' (hx.symm.trans hx'))
  refine hc.mono fun c hcpos => ?_
  simp only [mem_ofPred_eq] at hcpos ⊢
  rwa [Measure.restrict_apply
    (isClosed_eq (continuous_hilbertVec_apply i) continuous_const).measurableSet, inter_comm]

/-- A generic offset: every face hyperplane meets `S` in a null set. -/
theorem exists_generic_offset (μ : Measure (HilbertVec d)) {S : Set (HilbertVec d)}
    (hfin : μ S ≠ ⊤) (h : ℝ) :
    ∃ a : Fin d → ℝ, ∀ i (m : ℤ), μ (S ∩ {x : HilbertVec d | x i = a i + m * h}) = 0 := by
  have hchoice : ∀ i : Fin d, ∃ c : ℝ, ∀ m : ℤ,
      μ (S ∩ {x : HilbertVec d | x i = c + m * h}) = 0 := by
    intro i
    set B := {c : ℝ | 0 < μ (S ∩ {x : HilbertVec d | x i = c})}
    have hB := countable_bad_levels μ hfin i
    have hbad : (⋃ m : ℤ, (fun c => c - m * h) '' B).Countable :=
      countable_iUnion fun m => hB.image _
    obtain ⟨c, hc⟩ : ∃ c, c ∉ ⋃ m : ℤ, (fun c => c - m * h) '' B := by
      by_contra hall
      push Not at hall
      exact Cardinal.not_countable_real (hbad.mono fun c _ => hall c)
    refine ⟨c, fun m => ?_⟩
    by_contra hpos
    apply hc
    refine mem_iUnion.2 ⟨m, c + m * h, ?_, by ring⟩
    exact pos_iff_ne_zero.2 hpos
  choose a ha using hchoice
  exact ⟨a, ha⟩

theorem measure_inter_gridCellClosed (μ : Measure (HilbertVec d)) (S : Set (HilbertVec d))
    {a : Fin d → ℝ} {h : ℝ} (ha : ∀ i (m : ℤ), μ (S ∩ {x : HilbertVec d | x i = a i + m * h}) = 0)
    (k : Fin d → ℤ) : μ (S ∩ gridCellClosed a h k) = μ (S ∩ gridCell a h k) := by
  refine le_antisymm ?_ (measure_mono (inter_subset_inter_right _ (gridCell_subset_closed a h k)))
  have hsub : S ∩ gridCellClosed a h k ⊆ (S ∩ gridCell a h k) ∪
      ⋃ i, S ∩ {x : HilbertVec d | x i = a i + (k i + 1) * h} := by
    intro x ⟨hxS, hx⟩
    by_cases hxc : x ∈ gridCell a h k
    · exact Or.inl ⟨hxS, hxc⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.1 (gridCellClosed_diff_subset a h k ⟨hx, hxc⟩)
      exact Or.inr (mem_iUnion.2 ⟨i, hxS, hi⟩)
  have hnull : μ (⋃ i, S ∩ {x : HilbertVec d | x i = a i + (k i + 1) * h}) = 0 := by
    refine measure_iUnion_null fun i => ?_
    have := ha i (k i + 1)
    simpa using this
  calc μ (S ∩ gridCellClosed a h k) ≤ μ ((S ∩ gridCell a h k) ∪
        ⋃ i, S ∩ {x : HilbertVec d | x i = a i + (k i + 1) * h}) := measure_mono hsub
    _ ≤ μ (S ∩ gridCell a h k) + μ (⋃ i, S ∩ {x : HilbertVec d | x i = a i + (k i + 1) * h}) :=
        measure_union_le _ _
    _ = μ (S ∩ gridCell a h k) := by rw [hnull, add_zero]

/-- Finitely many cubes meet a bounded set. -/
theorem finite_gridCell_meet (a : Fin d → ℝ) {h : ℝ} (hh : 0 < h) {T : Set (HilbertVec d)}
    (hT : Bornology.IsBounded T) : {k : Fin d → ℤ | (gridCell a h k ∩ T).Nonempty}.Finite := by
  obtain ⟨R, hR⟩ := hT.subset_closedBall 0
  set A : ℝ := ∑ i, |a i|
  have hA : ∀ i, |a i| ≤ A := fun i =>
    Finset.single_le_sum (f := fun i => |a i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
  set N : ℤ := ⌈(|R| + A) / h⌉ + 1
  refine (Set.Finite.pi (t := fun _ : Fin d => Icc (-N) N) fun _ => finite_Icc _ _).subset ?_
  rintro k ⟨x, hxk, hxT⟩
  simp only [mem_pi, mem_univ, mem_Icc, forall_true_left]
  intro i
  have hxi : |x i| ≤ |R| := by
    have h1 : ‖x‖ ≤ R := by simpa using hR hxT
    have h2 : |x i| ≤ ‖x‖ := by
      have := PiLp.norm_apply_le (p := 2) x i
      simpa [Real.norm_eq_abs] using this
    exact h2.trans (h1.trans (le_abs_self R))
  have hai := hA i
  have hk1 := (hxk i).1
  have hk2 := (hxk i).2
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => abs_nonneg (a i)
  have hq : 0 ≤ (|R| + A) / h := div_nonneg (by positivity) hh.le
  have hceil := Int.le_ceil ((|R| + A) / h)
  have hb1 : (k i : ℝ) * h ≤ |R| + A := by
    have := abs_le.1 hxi; have := abs_le.1 hai; linarith
  have hb2 : -(|R| + A) < ((k i : ℝ) + 1) * h := by
    have := abs_le.1 hxi; have := abs_le.1 hai; linarith
  have hu : (k i : ℝ) ≤ (|R| + A) / h := (le_div_iff₀ hh).2 hb1
  have hl : -((|R| + A) / h) - 1 < (k i : ℝ) := by
    have : -((|R| + A) / h) < (k i : ℝ) + 1 := by
      rw [neg_lt, lt_div_iff₀ hh]; linarith
    linarith
  constructor
  · have : (-(N : ℝ)) ≤ k i := by
      have : ((N : ℤ) : ℝ) = (⌈(|R| + A) / h⌉ : ℝ) + 1 := by push_cast [N]; ring
      linarith
    exact_mod_cast this
  · have : (k i : ℝ) ≤ N := by
      have : ((N : ℤ) : ℝ) = (⌈(|R| + A) / h⌉ : ℝ) + 1 := by push_cast [N]; ring
      linarith
    exact_mod_cast this

/-- **Generic grid.** -/
theorem exists_good_grid (μ : Measure (HilbertVec d)) {S : Set (HilbertVec d)}
    (hS : IsCompact S) (hfin : μ S ≠ ⊤) {lam : ℝ} (hlam : 0 < lam) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ (J : Finset (Fin d → ℤ)) (Q Qc : (Fin d → ℤ) → Set (HilbertVec d)),
      (∀ k, MeasurableSet (Q k)) ∧ (∀ k, IsClosed (Qc k)) ∧ (∀ k, Q k ⊆ Qc k) ∧
      cthickening δ S ⊆ ⋃ k ∈ J, Q k ∧
      (∀ k ∈ J, ∃ σ ∈ S, Qc k ⊆ ball σ lam) ∧
      ∑ k ∈ J, μ (S ∩ Qc k) ≤ μ S := by
  set h : ℝ := lam / (4 * (Real.sqrt d + 1)) with hhdef
  have hsq : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hh : 0 < h := by positivity
  set δ : ℝ := lam / 4 with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨a, ha⟩ := exists_generic_offset μ hfin h
  have hTb : Bornology.IsBounded (cthickening δ S) := hS.isBounded.cthickening
  set Jset := {k : Fin d → ℤ | (gridCell a h k ∩ cthickening δ S).Nonempty}
  have hJ : Jset.Finite := finite_gridCell_meet a hh hTb
  refine ⟨δ, hδ0, hJ.toFinset, gridCell a h, gridCellClosed a h, measurableSet_gridCell a h,
    isClosed_gridCellClosed a h, gridCell_subset_closed a h, ?_, ?_, ?_⟩
  · intro x hx
    refine mem_biUnion (x := fun i => ⌊(x i - a i) / h⌋) ?_ (mem_gridCell_floor a hh x)
    exact Finset.mem_coe.2 (hJ.mem_toFinset.2 ⟨x, mem_gridCell_floor a hh x, hx⟩)
  · intro k hk
    obtain ⟨z, hzk, hzT⟩ := hJ.mem_toFinset.1 hk
    have hSne : S.Nonempty := by
      by_contra hne
      rw [not_nonempty_iff_eq_empty] at hne
      simp [hne] at hzT
    obtain ⟨σ, hσS, hσ⟩ := hS.exists_infDist_eq_dist hSne z
    have hzσ : dist z σ ≤ δ := by
      rw [← hσ]
      have h1 := mem_cthickening_iff.1 hzT
      have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
      rwa [ENNReal.toReal_ofReal hδ0.le] at h2
    refine ⟨σ, hσS, fun y hy => ?_⟩
    rw [mem_ball]
    have h1 := dist_le_of_mem_gridCellClosed a hh k hy (gridCell_subset_closed a h k hzk)
    have h2 : Real.sqrt d * h < lam / 2 := by
      rw [hhdef, mul_div_assoc']
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    calc dist y σ ≤ dist y z + dist z σ := dist_triangle _ _ _
      _ < lam := by linarith
  · calc ∑ k ∈ hJ.toFinset, μ (S ∩ gridCellClosed a h k)
        = ∑ k ∈ hJ.toFinset, μ (S ∩ gridCell a h k) :=
          Finset.sum_congr rfl fun k _ => measure_inter_gridCellClosed μ S ha k
      _ = μ (⋃ k ∈ hJ.toFinset, S ∩ gridCell a h k) := by
          rw [measure_biUnion_finset]
          · intro k _ k' _ hkk'
            exact (pairwise_disjoint_gridCell a hh hkk').mono inter_subset_right
              inter_subset_right
          · intro k _
            exact hS.isClosed.measurableSet.inter (measurableSet_gridCell a h k)
      _ ≤ μ S := measure_mono (iUnion₂_subset fun _ _ => inter_subset_left)

end PDE.IsoperimetricProof
