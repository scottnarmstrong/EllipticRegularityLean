module

public import PDEFoundation.Ambient.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Half-open dyadic cubes in `Vec d`

The dyadic grid used for the abstract kernel construction: the level `n : ℕ` cubes are
`cube n k = Set.pi univ (fun i => Ico (k i / 2^n) ((k i + 1) / 2^n))` with `k : Fin d → ℤ`
(side `2^{-n}`).  The index map `idx n y = ⌊2^n y⌋` sends a point to the unique level-`n` cube
containing it.  This file proves the elementary geometry (partition, volume, nestedness, the
`2^d` children) used by `KernelLimit` and `KernelExtend`.
-/

@[expose] public section

namespace PDE.NashKernelDyadic

open MeasureTheory Set

variable {d : ℕ}

/-- The half-open dyadic cube of level `n` (side `2^{-n}`) with integer index `k`. -/
noncomputable def cube (n : ℕ) (k : Fin d → ℤ) : Set (PDE.Vec d) :=
  Set.pi univ fun i => Ico ((k i : ℝ) / 2 ^ n) (((k i : ℝ) + 1) / 2 ^ n)

/-- The index of the level-`n` dyadic cube containing `y`. -/
noncomputable def idx (n : ℕ) (y : PDE.Vec d) : Fin d → ℤ := fun i => ⌊(2 : ℝ) ^ n * y i⌋

theorem mem_cube_iff {n : ℕ} {k : Fin d → ℤ} {y : PDE.Vec d} :
    y ∈ cube n k ↔ idx n y = k := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  simp only [cube, idx, mem_pi, mem_univ, true_implies, mem_Ico, funext_iff, Int.floor_eq_iff]
  refine forall_congr' fun i => ?_
  rw [div_le_iff₀ h2, lt_div_iff₀ h2, mul_comm (y i)]

theorem measurable_idx (n : ℕ) : Measurable (idx (d := d) n) := by
  refine measurable_pi_iff.mpr fun i => ?_
  exact Int.measurable_floor.comp (measurable_const.mul (measurable_pi_apply i))

theorem cube_eq_preimage (n : ℕ) (k : Fin d → ℤ) : cube n k = idx n ⁻¹' {k} := by
  ext y
  simp [mem_cube_iff]

theorem measurableSet_cube (n : ℕ) (k : Fin d → ℤ) : MeasurableSet (cube n k) := by
  rw [cube_eq_preimage]
  exact measurable_idx n (measurableSet_singleton k)

theorem volume_cube (n : ℕ) (k : Fin d → ℤ) :
    volume (cube n k) = ENNReal.ofReal (((2 : ℝ) ^ n)⁻¹ ^ d) := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [cube, Real.volume_pi_Ico]
  have : ∀ i : Fin d, ENNReal.ofReal (((k i : ℝ) + 1) / 2 ^ n - (k i : ℝ) / 2 ^ n)
      = ENNReal.ofReal ((2 : ℝ) ^ n)⁻¹ := fun i => by
    congr 1
    field_simp
    ring
  simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (inv_nonneg.mpr h2.le)]

theorem volume_cube_toReal (n : ℕ) (k : Fin d → ℤ) :
    (volume (cube n k)).toReal = ((2 : ℝ) ^ n)⁻¹ ^ d := by
  rw [volume_cube, ENNReal.toReal_ofReal (by positivity)]

theorem volume_cube_lt_top (n : ℕ) (k : Fin d → ℤ) : volume (cube n k) < ⊤ := by
  rw [volume_cube]; exact ENNReal.ofReal_lt_top

theorem idx_succ (n : ℕ) (y : PDE.Vec d) : idx n y = fun i => idx (n + 1) y i / 2 := by
  funext i
  simp only [idx]
  set a := ⌊(2 : ℝ) ^ (n + 1) * y i⌋ with ha
  have h1 : (a : ℝ) ≤ (2 : ℝ) ^ (n + 1) * y i := Int.floor_le _
  have h2 : (2 : ℝ) ^ (n + 1) * y i < a + 1 := Int.lt_floor_add_one _
  have h3 : (2 : ℝ) ^ (n + 1) * y i = 2 * ((2 : ℝ) ^ n * y i) := by ring
  rw [Int.floor_eq_iff]
  have hq : (a / 2) * 2 + a % 2 = a := Int.ediv_mul_add_emod a 2
  have hr0 : 0 ≤ a % 2 := Int.emod_nonneg a (by norm_num)
  have hr1 : a % 2 < 2 := Int.emod_lt_of_pos a (by norm_num)
  have hq' : ((a / 2 : ℤ) : ℝ) * 2 + ((a % 2 : ℤ) : ℝ) = a := by exact_mod_cast hq
  have hr0' : (0 : ℝ) ≤ ((a % 2 : ℤ) : ℝ) := by exact_mod_cast hr0
  have hr1' : ((a % 2 : ℤ) : ℝ) ≤ 1 := by exact_mod_cast (by omega : a % 2 ≤ 1)
  constructor <;> linarith

/-- A coarser index is a function of a finer index. -/
theorem exists_idx_eq {n m : ℕ} (h : n ≤ m) :
    ∃ g : (Fin d → ℤ) → (Fin d → ℤ), ∀ y : PDE.Vec d, idx n y = g (idx m y) := by
  induction m, h using Nat.le_induction with
  | base => exact ⟨id, fun _ => rfl⟩
  | succ m _ ih =>
    obtain ⟨g, hg⟩ := ih
    refine ⟨fun j => g (fun i => j i / 2), fun y => ?_⟩
    rw [hg y, idx_succ m y]

theorem cube_subset_cube_of_mem {n m : ℕ} (h : n ≤ m) {k j : Fin d → ℤ} {y : PDE.Vec d}
    (hyj : y ∈ cube m j) (hyk : y ∈ cube n k) : cube m j ⊆ cube n k := by
  obtain ⟨g, hg⟩ := exists_idx_eq (d := d) h
  rw [mem_cube_iff] at hyj hyk
  intro z hz
  rw [mem_cube_iff] at hz ⊢
  rw [hg z, hz, ← hyj, ← hg y, hyk]

/-- Dyadic cubes are nested or disjoint. -/
theorem cube_inter {n m : ℕ} {k j : Fin d → ℤ} (h : (cube n k ∩ cube m j).Nonempty) :
    ∃ n' k', cube n k ∩ cube m j = cube n' k' := by
  obtain ⟨y, hyk, hyj⟩ := h
  rcases le_total n m with hnm | hmn
  · refine ⟨m, j, ?_⟩
    exact inter_eq_right.mpr (cube_subset_cube_of_mem hnm hyj hyk)
  · refine ⟨n, k, ?_⟩
    exact inter_eq_left.mpr (cube_subset_cube_of_mem hmn hyk hyj)

theorem isPiSystem_cubes : IsPiSystem {s : Set (PDE.Vec d) | ∃ n k, s = cube n k} := by
  rintro _ ⟨n, k, rfl⟩ _ ⟨m, j, rfl⟩ h
  exact cube_inter h

/-- Distinct cubes of one level are disjoint. -/
theorem pairwise_disjoint_cube (n : ℕ) :
    Pairwise (Function.onFun Disjoint (cube (d := d) n)) := by
  intro k j hkj
  rw [Function.onFun, Set.disjoint_left]
  intro y hk hj
  exact hkj ((mem_cube_iff.mp hk).symm.trans (mem_cube_iff.mp hj))

/-- The cubes of level `n + 1` inside the cube `(n, k)`: the children. -/
def child (k : Fin d → ℤ) (ε : Fin d → Bool) : Fin d → ℤ :=
  fun i => 2 * k i + (if ε i then 1 else 0)

theorem cube_succ_eq_iUnion (n : ℕ) (k : Fin d → ℤ) :
    cube n k = ⋃ ε : Fin d → Bool, cube (n + 1) (child k ε) := by
  ext y
  simp only [mem_iUnion, mem_cube_iff]
  constructor
  · intro hy
    refine ⟨fun i => decide (idx (n + 1) y i % 2 = 1), ?_⟩
    funext i
    have h1 := congrFun (idx_succ n y) i
    have h2 : idx n y i = k i := congrFun hy i
    simp only [child]
    have := Int.ediv_mul_add_emod (idx (n + 1) y i) 2
    have h3 := Int.emod_nonneg (idx (n + 1) y i) (by norm_num : (2 : ℤ) ≠ 0)
    have h4 := Int.emod_lt_of_pos (idx (n + 1) y i) (by norm_num : (0 : ℤ) < 2)
    by_cases hc : idx (n + 1) y i % 2 = 1 <;> simp only [hc, decide_true, decide_false] <;>
      simp <;> omega
  · rintro ⟨ε, hε⟩
    funext i
    have h1 := congrFun (idx_succ n y) i
    have h2 : idx (n + 1) y i = child k ε i := congrFun hε i
    rw [h1, h2]
    simp only [child]
    by_cases hc : ε i
    · simp only [hc]; simp; omega
    · simp only [hc]; simp

theorem pairwise_disjoint_child (n : ℕ) (k : Fin d → ℤ) :
    Pairwise (Function.onFun Disjoint fun ε : Fin d → Bool => cube (n + 1) (child k ε)) := by
  intro ε ε' hne
  refine Set.disjoint_left.mpr fun y h h' => hne ?_
  have := (mem_cube_iff.mp h).symm.trans (mem_cube_iff.mp h')
  funext i
  have := congrFun this i
  simp only [child] at this
  by_cases h1 : ε i <;> by_cases h2 : ε' i <;> simp [h1, h2] at this ⊢

/-- Windows: finite unions of level-`0` cubes. -/
def win (F : Finset (Fin d → ℤ)) : Set (PDE.Vec d) := idx 0 ⁻¹' (F : Set (Fin d → ℤ))

theorem measurableSet_win (F : Finset (Fin d → ℤ)) : MeasurableSet (win F) :=
  measurable_idx 0 F.measurableSet

theorem cube_subset_win_or_disjoint {n : ℕ} (k : Fin d → ℤ) (F : Finset (Fin d → ℤ)) :
    cube n k ⊆ win F ∨ Disjoint (cube n k) (win F) := by
  obtain ⟨g, hg⟩ := exists_idx_eq (d := d) (Nat.zero_le n)
  by_cases hk : g k ∈ F
  · left
    intro y hy
    simp only [win, mem_preimage, hg y, mem_cube_iff.mp hy]
    exact hk
  · right
    refine Set.disjoint_left.mpr fun y hy hw => hk ?_
    simp only [win, mem_preimage, hg y, mem_cube_iff.mp hy] at hw
    exact hw

/-- The exhausting finite windows `[-N, N]^d` of level-`0` indices. -/
def box (N : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) (N : ℤ)

theorem volume_win_lt_top (F : Finset (Fin d → ℤ)) : volume (win F) < ⊤ := by
  classical
  have : win F = ⋃ k ∈ F, cube 0 k := by
    ext y
    simp only [win, mem_preimage, Finset.mem_coe, mem_iUnion, mem_cube_iff, exists_prop]
    exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨k, hk, h⟩ => h ▸ hk⟩
  rw [this]
  exact (measure_biUnion_finset_le _ _).trans_lt
    (ENNReal.sum_lt_top.mpr fun k _ => volume_cube_lt_top 0 k)

theorem monotone_box : Monotone (box (d := d)) := by
  intro N M h k hk
  simp only [box, Fintype.mem_piFinset, Finset.mem_Icc] at hk ⊢
  exact fun i => ⟨by have := (hk i).1; omega, by have := (hk i).2; omega⟩

theorem iUnion_win_box : ⋃ N, win (box (d := d) N) = univ := by
  refine eq_univ_of_forall fun y => ?_
  rw [mem_iUnion]
  refine ⟨∑ i, (idx 0 y i).natAbs, ?_⟩
  simp only [win, box, mem_preimage, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
  have hle : ∀ i, (idx 0 y i).natAbs ≤ ∑ i, (idx 0 y i).natAbs := fun i =>
    Finset.single_le_sum (f := fun i => (idx 0 y i).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  exact fun i => ⟨by have := hle i; omega, by have := hle i; omega⟩

theorem exists_cube_subset_win_box (n : ℕ) (k : Fin d → ℤ) :
    ∃ N, cube n k ⊆ win (box (d := d) N) := by
  obtain ⟨g, hg⟩ := exists_idx_eq (d := d) (Nat.zero_le n)
  refine ⟨∑ i, (g k i).natAbs, fun y hy => ?_⟩
  simp only [win, box, mem_preimage, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
  rw [hg y, mem_cube_iff.mp hy]
  have hle : ∀ i, (g k i).natAbs ≤ ∑ i, (g k i).natAbs := fun i =>
    Finset.single_le_sum (f := fun i => (g k i).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  exact fun i => ⟨by have := hle i; omega, by have := hle i; omega⟩

/-- Every open set is a countable union of dyadic cubes contained in it. -/
theorem isOpen_eq_iUnion_cubes {G : Set (PDE.Vec d)} (hG : IsOpen G) :
    G = ⋃ p : {p : ℕ × (Fin d → ℤ) // cube p.1 p.2 ⊆ G}, cube p.1.1 p.1.2 := by
  refine Set.Subset.antisymm (fun x hx => ?_) (iUnion_subset fun p => p.2)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hG x hx
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  have hsub : cube n (idx n x) ⊆ G := by
    refine Subset.trans (fun y hy => ?_) hball
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro i
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    have hx' := (mem_cube_iff (n := n) (k := idx n x)).mpr rfl
    simp only [cube, mem_pi, mem_univ, true_implies, mem_Ico] at hy hx'
    obtain ⟨a1, a2⟩ := hy i
    obtain ⟨b1, b2⟩ := hx' i
    rw [Real.dist_eq, abs_lt]
    have : (1 / 2 : ℝ) ^ n = ((2 : ℝ) ^ n)⁻¹ := by rw [one_div, inv_pow]
    rw [this] at hn
    have e : (((idx n x i : ℝ) + 1) / 2 ^ n) = (idx n x i : ℝ) / 2 ^ n + ((2 : ℝ) ^ n)⁻¹ := by
      field_simp
    rw [e] at a2 b2
    constructor <;> linarith
  exact mem_iUnion.mpr ⟨⟨(n, idx n x), hsub⟩, mem_cube_iff.mpr rfl⟩

theorem borel_eq_generateFrom_cubes :
    (borel (PDE.Vec d)) =
      MeasurableSpace.generateFrom {s : Set (PDE.Vec d) | ∃ n k, s = cube n k} := by
  refine le_antisymm ?_ ?_
  · refine MeasurableSpace.generateFrom_le fun G hG => ?_
    rw [isOpen_eq_iUnion_cubes hG]
    exact MeasurableSet.iUnion fun p => MeasurableSpace.measurableSet_generateFrom ⟨_, _, rfl⟩
  · refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨n, k, rfl⟩
    have := measurableSet_cube n k
    rwa [BorelSpace.measurable_eq (α := PDE.Vec d)] at this

end PDE.NashKernelDyadic
