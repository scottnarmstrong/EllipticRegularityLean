module

public import PDEFoundation.Analysis.Gehring.CubeMaximal
public import Mathlib.Data.Int.Interval

/-!
# Dyadic cubes

The dyadic cube of scale `n : ℤ` and index `m : Fin d → ℤ` is the half-open cube
`∏ᵢ [mᵢ 2ⁿ, (mᵢ + 1) 2ⁿ)`. Two dyadic cubes are nested or disjoint (`dyadicSub_of_mem`).
`DyadicSub` records the coordinatewise containment of dyadic cubes as integer-lattice data.
-/

@[expose] public section

namespace PDE.Gehring

open Set MeasureTheory
open scoped ENNReal

/-- The half-open dyadic cube of scale `n` (side `2 ^ n`) and integer index `m`. -/
def dyadicCube {d : ℕ} (n : ℤ) (m : Fin d → ℤ) : Set (Vec d) :=
  {x | ∀ i, (m i : ℝ) * 2 ^ n ≤ x i ∧ x i < ((m i : ℝ) + 1) * 2 ^ n}

/-- The center of the dyadic cube of scale `n` and index `m`. -/
noncomputable def dyadicCenter {d : ℕ} (n : ℤ) (m : Fin d → ℤ) : Vec d :=
  fun i => ((m i : ℝ) + 1 / 2) * 2 ^ n

/-- `DyadicSub n m n' m'`: the dyadic cube `(n, m)` is contained in `(n', m')`, expressed on the
integer lattice (in particular `n ≤ n'`). -/
def DyadicSub {d : ℕ} (n : ℤ) (m : Fin d → ℤ) (n' : ℤ) (m' : Fin d → ℤ) : Prop :=
  n ≤ n' ∧ ∀ i, (m' i : ℝ) * 2 ^ n' ≤ (m i : ℝ) * 2 ^ n ∧
    ((m i : ℝ) + 1) * 2 ^ n ≤ ((m' i : ℝ) + 1) * 2 ^ n'

theorem dyadicSide_pos (n : ℤ) : (0 : ℝ) < 2 ^ n := zpow_pos (by norm_num) n

theorem dyadicSide_add_nat (n : ℤ) (k : ℕ) : (2 : ℝ) ^ (n + k) = 2 ^ n * 2 ^ k := by
  rw [zpow_add₀ (by norm_num), zpow_natCast]

theorem dyadicSide_le_of_le {n n' : ℤ} (h : n ≤ n') : (2 : ℝ) ^ n ≤ 2 ^ n' :=
  zpow_le_zpow_right₀ (by norm_num) h

theorem dyadicCube_subset_of_sub {d : ℕ} {n n' : ℤ} {m m' : Fin d → ℤ}
    (h : DyadicSub n m n' m') : dyadicCube n m ⊆ dyadicCube n' m' := by
  intro x hx i
  have := hx i
  have := h.2 i
  constructor <;> linarith [this.1, this.2]

/-- Two dyadic cubes that meet are nested: the smaller-scale one lies in the larger. -/
theorem dyadicSub_of_mem {d : ℕ} {n n' : ℤ} {m m' : Fin d → ℤ} {x : Vec d} (hn : n ≤ n')
    (hx : x ∈ dyadicCube n m) (hx' : x ∈ dyadicCube n' m') : DyadicSub n m n' m' := by
  refine ⟨hn, fun i => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n' = n + k := ⟨(n' - n).toNat, by omega⟩
  obtain ⟨b1, b2⟩ := hx' i
  rw [dyadicSide_add_nat] at b1 b2 ⊢
  have hp := dyadicSide_pos n
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  obtain ⟨a1, a2⟩ := hx i
  have h1 : (m' i : ℝ) * 2 ^ k < (m i : ℝ) + 1 := by
    by_contra hcon; push Not at hcon
    nlinarith
  have h2 : (m i : ℝ) < ((m' i : ℝ) + 1) * 2 ^ k := by
    by_contra hcon; push Not at hcon
    nlinarith
  have h1' : m' i * 2 ^ k < m i + 1 := by exact_mod_cast h1
  have h2' : m i < (m' i + 1) * 2 ^ k := by exact_mod_cast h2
  have h1'' : m' i * 2 ^ k ≤ m i := by omega
  have h2'' : m i + 1 ≤ (m' i + 1) * 2 ^ k := by omega
  have h1r : (m' i : ℝ) * 2 ^ k ≤ m i := by exact_mod_cast h1''
  have h2r : (m i : ℝ) + 1 ≤ ((m' i : ℝ) + 1) * 2 ^ k := by exact_mod_cast h2''
  constructor <;> nlinarith

theorem mem_dyadicCube_floor {d : ℕ} (n : ℤ) (x : Vec d) :
    x ∈ dyadicCube n (fun i => ⌊x i / 2 ^ n⌋) := by
  intro i
  have hp := dyadicSide_pos n
  have h1 := Int.floor_le (x i / 2 ^ n)
  have h2 := Int.lt_floor_add_one (x i / 2 ^ n)
  constructor
  · calc _ ≤ x i / 2 ^ n * 2 ^ n := by gcongr
      _ = x i := by field_simp
  · calc x i = x i / 2 ^ n * 2 ^ n := by field_simp
      _ < _ := by gcongr

theorem eq_floor_of_mem_dyadicCube {d : ℕ} {n : ℤ} {m : Fin d → ℤ} {x : Vec d}
    (hx : x ∈ dyadicCube n m) (i : Fin d) : m i = ⌊x i / 2 ^ n⌋ := by
  have hp := dyadicSide_pos n
  obtain ⟨a1, a2⟩ := hx i
  rw [eq_comm, Int.floor_eq_iff]
  constructor
  · rw [le_div_iff₀ hp]; exact a1
  · rw [div_lt_iff₀ hp]; exact a2

/-- The dyadic parent index. -/
def dyadicParent {d : ℕ} (m : Fin d → ℤ) : Fin d → ℤ := fun i => m i / 2

theorem dyadicSub_parent {d : ℕ} (n : ℤ) (m : Fin d → ℤ) :
    DyadicSub n m (n + 1) (dyadicParent m) := by
  refine ⟨by omega, fun i => ?_⟩
  have h2 : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by
    rw [zpow_add_one₀ (by norm_num)]; ring
  rw [h2]
  have hp := dyadicSide_pos n
  have a : m i / 2 * 2 ≤ m i := Int.ediv_mul_le _ (by norm_num)
  have b : m i < (m i / 2 + 1) * 2 := by
    have := Int.lt_ediv_add_one_mul_self (m i) (b := 2) (by norm_num)
    linarith
  have ar : ((m i / 2 : ℤ) : ℝ) * 2 ≤ m i := by exact_mod_cast a
  have br : (m i : ℝ) + 1 ≤ (((m i / 2 : ℤ) : ℝ) + 1) * 2 := by
    have : m i + 1 ≤ (m i / 2 + 1) * 2 := by omega
    exact_mod_cast this
  unfold dyadicParent
  constructor <;> nlinarith

/-- A dyadic cube is contained in the closed centered cube of half-side `2 ^ n / 2`. -/
theorem dyadicCube_subset_closed {d : ℕ} (n : ℤ) (m : Fin d → ℤ) :
    dyadicCube n m ⊆ closedCenteredAxisCube (dyadicCenter n m) (2 ^ n / 2) := by
  intro x hx i _
  obtain ⟨a1, a2⟩ := hx i
  simp only [dyadicCenter]
  constructor <;> nlinarith [dyadicSide_pos n]

/-- The open centered cube of half-side `2 ^ n / 2` is contained in the dyadic cube. -/
theorem centeredAxisCube_subset_dyadicCube {d : ℕ} (n : ℤ) (m : Fin d → ℤ) :
    centeredAxisCube (dyadicCenter n m) (2 ^ n / 2) ⊆ dyadicCube n m := by
  intro x hx i
  obtain ⟨a1, a2⟩ := hx i (mem_univ i)
  simp only [dyadicCenter] at a1 a2
  constructor <;> nlinarith [dyadicSide_pos n]

/-- A dyadic cube coincides almost everywhere with the open centered cube. -/
theorem dyadicCube_ae_subset {d : ℕ} (n : ℤ) (m : Fin d → ℤ) :
    dyadicCube n m ≤ᵐ[volume] centeredAxisCube (dyadicCenter n m) (2 ^ n / 2) := by
  have h := (centeredAxisCube_ae_eq_closedCenteredAxisCube (dyadicCenter n m) (2 ^ n / 2))
  exact (Filter.EventuallyLE.trans (Filter.Eventually.of_forall (dyadicCube_subset_closed n m))
    h.symm.le)

end PDE.Gehring
