module

public import PDEFoundation.Analysis.Gehring.Dyadic
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Whitney selection of dyadic cubes

For an open bounded set `E ⊆ ℝ^d` and `σ ≥ 1`, a dyadic cube `Q` is *admissible* when the closed
cube with the same center and side `2σ ℓ(Q)` (i.e. `closure (2σ Q)`) lies in `E`. The maximal
admissible cubes (those whose dyadic parent is not admissible) form the Whitney family.
-/

@[expose] public section

namespace PDE.Gehring

open Set MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- Admissibility of the dyadic cube `q = (n, m)`: `closure (2σ Q) ⊆ E`. -/
def WAdm (E : Set (Vec d)) (σ : ℝ) (q : ℤ × (Fin d → ℤ)) : Prop :=
  closedCenteredAxisCube (dyadicCenter q.1 q.2) (σ * 2 ^ q.1) ⊆ E

/-- Selected (maximal admissible) cubes: admissible with non-admissible dyadic parent. -/
def WSel (E : Set (Vec d)) (σ : ℝ) (q : ℤ × (Fin d → ℤ)) : Prop :=
  WAdm E σ q ∧ ¬ WAdm E σ (q.1 + 1, dyadicParent q.2)

theorem wAdm_mono {E : Set (Vec d)} {σ : ℝ} (hσ : 1 / 2 ≤ σ) {q q' : ℤ × (Fin d → ℤ)}
    (h : DyadicSub q.1 q.2 q'.1 q'.2) (hq' : WAdm E σ q') : WAdm E σ q := by
  refine subset_trans ?_ hq'
  intro y hy i hi
  have hyi := hy i hi
  have hs := h.2 i
  have hle := dyadicSide_le_of_le h.1
  simp only [dyadicCenter, mem_Icc] at hyi ⊢
  have h3 : (σ - 1 / 2) * 2 ^ q.1 ≤ (σ - 1 / 2) * 2 ^ q'.1 :=
    mul_le_mul_of_nonneg_left hle (by linarith)
  constructor <;> nlinarith [hs.1, hs.2, hyi.1, hyi.2]

theorem exists_out_of_wSel {E : Set (Vec d)} {σ : ℝ} {q : ℤ × (Fin d → ℤ)} (h : WSel E σ q) :
    ∃ y ∈ closedCenteredAxisCube (dyadicCenter q.1 q.2) ((4 * σ + 1) * 2 ^ q.1 / 2), y ∉ E := by
  have h2 := h.2
  unfold WAdm at h2
  rw [not_subset] at h2
  obtain ⟨y, hy, hyE⟩ := h2
  refine ⟨y, fun i hi => ?_, hyE⟩
  have hyi := hy i hi
  have hs := (dyadicSub_parent q.1 q.2).2 i
  have h2 : (2 : ℝ) ^ (q.1 + 1) = 2 * 2 ^ q.1 := by
    rw [zpow_add_one₀ (by norm_num)]; ring
  have hp := dyadicSide_pos q.1
  simp only [dyadicCenter, mem_Icc] at hyi ⊢
  rw [h2] at hs hyi
  constructor <;> nlinarith [hs.1, hs.2, hyi.1, hyi.2]

/-- Every point of the bounded open set `E` lies in a selected dyadic cube. -/
theorem exists_wSel_mem {E : Set (Vec d)} (hd : 0 < d) (hE : IsOpen E)
    (hb : Bornology.IsBounded E) {σ : ℝ} (hσ : 1 ≤ σ) {x : Vec d} (hx : x ∈ E) :
    ∃ q, WSel E σ q ∧ x ∈ dyadicCube q.1 q.2 := by
  classical
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hE x hx
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Vec d)).1 hb
  let fl : ℤ → (Fin d → ℤ) := fun n i => ⌊x i / 2 ^ n⌋
  let P : ℤ → Prop := fun n => WAdm E σ (n, fl n)
  -- nonempty
  have hne : ∃ n, P n := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < ε / (σ + 1))
      (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨-(k : ℤ), fun y hy => hball ?_⟩
    have hp : (2 : ℝ) ^ (-(k : ℤ)) = (1 / 2) ^ k := by
      rw [zpow_neg, zpow_natCast, one_div, inv_pow]
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro i
    rw [Real.dist_eq]
    have hyi := hy i (mem_univ i)
    have hxi : ((fl (-(k : ℤ)) i : ℤ) : ℝ) * 2 ^ (-(k : ℤ)) ≤ x i ∧
        x i < (((fl (-(k : ℤ)) i : ℤ) : ℝ) + 1) * 2 ^ (-(k : ℤ)) :=
      mem_dyadicCube_floor (-(k : ℤ)) x i
    simp only [dyadicCenter, mem_Icc] at hyi
    have hp0 := dyadicSide_pos (-(k : ℤ))
    rw [hp] at hp0 hyi hxi
    have h3 : (σ + 1) * (1 / 2) ^ k < ε := by
      calc (σ + 1) * (1 / 2) ^ k < (σ + 1) * (ε / (σ + 1)) :=
            mul_lt_mul_of_pos_left hk (by linarith)
        _ = ε := by field_simp
    rw [abs_lt]
    constructor <;> nlinarith [hyi.1, hyi.2, hxi.1, hxi.2]
  -- bounded above
  have hbdd : ∃ B, ∀ n, P n → n ≤ B := by
    obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt R (by norm_num : (1 : ℝ) < 2)
    refine ⟨K, fun n hn => ?_⟩
    by_contra hcon
    push Not at hcon
    have hi0 : Fin d := ⟨0, hd⟩
    set c := dyadicCenter n (fl n) with hc
    have hmem : ∀ s : ℝ, |s| ≤ σ * 2 ^ n → Function.update c ⟨0, hd⟩ (c ⟨0, hd⟩ + s) ∈ E := by
      intro s hs
      apply hn
      intro i _
      by_cases hi : i = ⟨0, hd⟩
      · subst hi
        simp only [Function.update_self, mem_Icc]
        constructor <;> linarith [abs_le.1 hs]
      · simp only [Function.update_of_ne hi, mem_Icc]
        have := dyadicSide_pos n
        constructor <;> nlinarith
    have h1 := hR (hmem (σ * 2 ^ n) (by rw [abs_of_nonneg (by positivity)]))
    have h2 := hR (hmem (-(σ * 2 ^ n)) (by rw [abs_neg, abs_of_nonneg (by positivity)]))
    have h1' := (norm_le_pi_norm _ (⟨0, hd⟩ : Fin d)).trans (mem_closedBall_zero_iff.1 h1)
    have h2' := (norm_le_pi_norm _ (⟨0, hd⟩ : Fin d)).trans (mem_closedBall_zero_iff.1 h2)
    simp only [Function.update_self, Real.norm_eq_abs] at h1' h2'
    have hK2 : (2 : ℝ) ^ K ≤ 2 ^ n := by
      rw [← zpow_natCast]
      exact dyadicSide_le_of_le (by omega)
    have := abs_le.1 h1'
    have := abs_le.1 h2'
    nlinarith [dyadicSide_pos n]
  obtain ⟨n, hn, hmax⟩ := Int.exists_greatest_of_bdd hbdd hne
  refine ⟨(n, fl n), ⟨hn, ?_⟩, mem_dyadicCube_floor n x⟩
  intro hadm
  have hx2 : x ∈ dyadicCube (n + 1) (dyadicParent (fl n)) :=
    dyadicCube_subset_of_sub (dyadicSub_parent n (fl n)) (mem_dyadicCube_floor n x)
  have hfl : dyadicParent (fl n) = fl (n + 1) := by
    funext i
    exact eq_floor_of_mem_dyadicCube hx2 i
  have := hmax (n + 1) (by show WAdm E σ (n + 1, fl (n + 1)); rw [← hfl]; exact hadm)
  omega

theorem eq_of_wSel_of_mem {E : Set (Vec d)} {σ : ℝ} (hσ : 1 / 2 ≤ σ) {q1 q2 : ℤ × (Fin d → ℤ)}
    (h1 : WSel E σ q1) (h2 : WSel E σ q2) (hn : q1.1 ≤ q2.1) {x : Vec d}
    (hx1 : x ∈ dyadicCube q1.1 q1.2) (hx2 : x ∈ dyadicCube q2.1 q2.2) : q1 = q2 := by
  have hsub := dyadicSub_of_mem hn hx1 hx2
  rcases hn.eq_or_lt with heq | hlt
  · refine Prod.ext heq ?_
    funext i
    have hi := hsub.2 i
    have hp := dyadicSide_pos q2.1
    rw [← heq] at hi
    have hp1 := dyadicSide_pos q1.1
    have a : (q2.2 i : ℝ) ≤ q1.2 i := by nlinarith [hi.1, hi.2]
    have b : (q1.2 i : ℝ) ≤ q2.2 i := by nlinarith [hi.1, hi.2]
    have a' : q2.2 i ≤ q1.2 i := by exact_mod_cast a
    have b' : q1.2 i ≤ q2.2 i := by exact_mod_cast b
    omega
  · exfalso
    have hP : DyadicSub (q1.1 + 1) (dyadicParent q1.2) q2.1 q2.2 :=
      dyadicSub_of_mem (by omega)
        (dyadicCube_subset_of_sub (dyadicSub_parent q1.1 q1.2) hx1) hx2
    exact h1.2 (wAdm_mono (q := (q1.1 + 1, dyadicParent q1.2)) hσ hP h2.1)

theorem disjoint_of_wSel {E : Set (Vec d)} {σ : ℝ} (hσ : 1 / 2 ≤ σ) {q1 q2 : ℤ × (Fin d → ℤ)}
    (h1 : WSel E σ q1) (h2 : WSel E σ q2) (hne : q1 ≠ q2) :
    Disjoint (dyadicCube q1.1 q1.2) (dyadicCube q2.1 q2.2) := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  rcases le_total q1.1 q2.1 with h | h
  · exact hne (eq_of_wSel_of_mem hσ h1 h2 h hx1 hx2)
  · exact hne (eq_of_wSel_of_mem hσ h2 h1 h hx2 hx1).symm

/-- A Whitney cover of an open set `E`: a countable family of dyadic cubes with disjoint
half-open carriers covering `E`, whose `closure (2σ Q)` lies in `E` while the dyadic parent
of `Q` is not admissible, so that `closure ((4σ+1) Q)` meets the complement of `E`.

Here `Q i` is the dyadic cube of scale `scale i` (side `2 ^ scale i`) and index `index i`,
`σ Q` is the cube with the same center and side `σ · 2 ^ scale i`. -/
structure WhitneyCover (E : Set (Vec d)) (σ : ℝ) where
  /-- The (countable) index type of the selected cubes. -/
  ι : Type
  [countable : Countable ι]
  /-- The dyadic scale (`log₂` of the side) of each cube. -/
  scale : ι → ℤ
  /-- The integer lattice index of each cube. -/
  index : ι → Fin d → ℤ
  /-- The half-open dyadic cubes are pairwise disjoint. -/
  cube_disjoint : Pairwise fun i j =>
    Disjoint (dyadicCube (scale i) (index i)) (dyadicCube (scale j) (index j))
  /-- The half-open dyadic cubes cover `E`. -/
  cover : E ⊆ ⋃ i, dyadicCube (scale i) (index i)
  /-- `closure (2σ Q) ⊆ E`. -/
  closedDilate_subset : ∀ i, closedCenteredAxisCube (dyadicCenter (scale i) (index i))
    (σ * 2 ^ scale i) ⊆ E
  /-- `closure ((4σ+1) Q)` contains a point outside `E`. -/
  exists_not_mem : ∀ i, ∃ y ∈ closedCenteredAxisCube (dyadicCenter (scale i) (index i))
    ((4 * σ + 1) * 2 ^ scale i / 2), y ∉ E

attribute [instance] WhitneyCover.countable

/-- **Existence of the Whitney cover** of a bounded open set (`d ≥ 1`, `σ ≥ 1`). -/
theorem exists_whitneyCover {E : Set (Vec d)} (hd : 0 < d) (hE : IsOpen E)
    (hb : Bornology.IsBounded E) {σ : ℝ} (hσ : 1 ≤ σ) : Nonempty (WhitneyCover E σ) := by
  classical
  let S : Set (ℤ × (Fin d → ℤ)) := {q | WSel E σ q}
  refine ⟨{
    ι := S
    scale := fun i => i.1.1
    index := fun i => i.1.2
    cube_disjoint := ?_
    cover := ?_
    closedDilate_subset := fun i => i.2.1
    exists_not_mem := fun i => exists_out_of_wSel i.2 }⟩
  · intro i j hij
    exact disjoint_of_wSel (by linarith) i.2 j.2 (fun h => hij (Subtype.ext h))
  · intro x hx
    obtain ⟨q, hq, hxq⟩ := exists_wSel_mem hd hE hb hσ hx
    exact mem_iUnion.2 ⟨⟨q, hq⟩, hxq⟩

namespace WhitneyCover

variable {E : Set (Vec d)} {σ : ℝ} (W : WhitneyCover E σ)

/-- The center of the `i`-th cube. -/
noncomputable def center (i : W.ι) : Vec d := dyadicCenter (W.scale i) (W.index i)

/-- The side length `ℓ(Q_i) = 2 ^ scale i` of the `i`-th cube. -/
noncomputable def side (i : W.ι) : ℝ := 2 ^ W.scale i

/-- The open cube `Q_i`. -/
noncomputable def cube (i : W.ι) : Set (Vec d) := centeredAxisCube (W.center i) (W.side i / 2)

/-- The open dilated cube `c Q_i` (same center, side `c ℓ(Q_i)`). -/
noncomputable def dilate (c : ℝ) (i : W.ι) : Set (Vec d) :=
  centeredAxisCube (W.center i) (c * W.side i / 2)

theorem side_pos (i : W.ι) : 0 < W.side i := dyadicSide_pos _

theorem cube_eq_dilate_one (i : W.ι) : W.cube i = W.dilate 1 i := by
  simp [cube, dilate]

/-- The open cubes `Q_i` have pairwise disjoint interiors (they are pairwise disjoint). -/
theorem cube_pairwise_disjoint : Pairwise fun i j => Disjoint (W.cube i) (W.cube j) := by
  intro i j hij
  exact (W.cube_disjoint hij).mono (centeredAxisCube_subset_dyadicCube _ _)
    (centeredAxisCube_subset_dyadicCube _ _)

/-- The open dilate `c Q_i` lies in `E` as soon as `c ≤ 2σ` (in particular `σ Q_i ⊆ E`). -/
theorem dilate_subset {c : ℝ} (hc : c ≤ 2 * σ) (i : W.ι) : W.dilate c i ⊆ E := by
  refine subset_trans ?_ (W.closedDilate_subset i)
  intro y hy j _
  have h := hy j (mem_univ j)
  have hp := W.side_pos i
  simp only [center] at h
  simp only [mem_Icc, side] at h hp ⊢
  constructor <;> nlinarith [h.1, h.2]

theorem cube_subset (hσ : 1 / 2 ≤ σ) (i : W.ι) : W.cube i ⊆ E := by
  rw [cube_eq_dilate_one]
  exact W.dilate_subset (by linarith) i

theorem measurableSet_cube (i : W.ι) : MeasurableSet (W.cube i) :=
  (isOpen_centeredAxisCube _ _).measurableSet

/-- The open cubes `Q_i` cover `E` up to a null set. -/
theorem volume_diff_iUnion_cube_eq_zero : volume (E \ ⋃ i, W.cube i) = 0 := by
  refine measure_mono_null (t := ⋃ i, (dyadicCube (W.scale i) (W.index i) \ W.cube i)) ?_ ?_
  · intro x ⟨hxE, hx⟩
    obtain ⟨i, hi⟩ := mem_iUnion.1 (W.cover hxE)
    exact mem_iUnion.2 ⟨i, hi, fun h => hx (mem_iUnion.2 ⟨i, h⟩)⟩
  · refine measure_iUnion_null fun i => ?_
    have := dyadicCube_ae_subset (W.scale i) (W.index i)
    have := ae_le_set.1 this
    have h2 : W.cube i = centeredAxisCube (dyadicCenter (W.scale i) (W.index i))
        (2 ^ W.scale i / 2) := rfl
    rw [h2]
    exact this

/-- `∑ᵢ |Q_i| = |E|`. -/
theorem tsum_volume_cube (hσ : 1 / 2 ≤ σ) : ∑' i, volume (W.cube i) = volume E := by
  rw [← measure_iUnion W.cube_pairwise_disjoint W.measurableSet_cube]
  refine le_antisymm (measure_mono (iUnion_subset fun i => W.cube_subset hσ i)) ?_
  calc volume E ≤ volume ((E \ ⋃ i, W.cube i) ∪ ⋃ i, W.cube i) := measure_mono (by
        intro x hx; by_cases h : x ∈ ⋃ i, W.cube i
        · exact Or.inr h
        · exact Or.inl ⟨hx, h⟩)
    _ ≤ volume (E \ ⋃ i, W.cube i) + volume (⋃ i, W.cube i) := measure_union_le _ _
    _ = volume (⋃ i, W.cube i) := by rw [W.volume_diff_iUnion_cube_eq_zero, zero_add]

end WhitneyCover

end PDE.Gehring
