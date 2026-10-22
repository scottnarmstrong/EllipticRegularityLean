module

public import PDEFoundation.Euler.Defs

/-!
# Basic API for the periodic predicates of the Euler torus

Closure properties of `IsTorusPeriodic`, invariance under integer translations, and finiteness of
`eulerMeasure`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

namespace IsTorusPeriodic

variable {β : Type*} {f g : Vec 2 → β}

theorem const (c : β) : IsTorusPeriodic (fun _ : Vec 2 => c) := fun _ _ => rfl

theorem comp {γ : Type*} (h : IsTorusPeriodic f) (φ : β → γ) : IsTorusPeriodic (fun x => φ (f x)) :=
  fun i x => by dsimp only; rw [h i x]

theorem add [Add β] (hf : IsTorusPeriodic f) (hg : IsTorusPeriodic g) :
    IsTorusPeriodic (fun x => f x + g x) := fun i x => by dsimp only; rw [hf i x, hg i x]

theorem sub [Sub β] (hf : IsTorusPeriodic f) (hg : IsTorusPeriodic g) :
    IsTorusPeriodic (fun x => f x - g x) := fun i x => by dsimp only; rw [hf i x, hg i x]

theorem neg [Neg β] (hf : IsTorusPeriodic f) : IsTorusPeriodic (fun x => -f x) :=
  fun i x => by dsimp only; rw [hf i x]

theorem mul [Mul β] (hf : IsTorusPeriodic f) (hg : IsTorusPeriodic g) :
    IsTorusPeriodic (fun x => f x * g x) := fun i x => by dsimp only; rw [hf i x, hg i x]

theorem smul {α : Type*} [SMul α β] (c : α) (hf : IsTorusPeriodic f) :
    IsTorusPeriodic (fun x => c • f x) := fun i x => by dsimp only; rw [hf i x]

/-- Composition of two periodic functions in the sense of a function of the pair. -/
theorem prodMk {γ δ : Type*} {g : Vec 2 → γ} (hf : IsTorusPeriodic f) (hg : IsTorusPeriodic g)
    (φ : β → γ → δ) : IsTorusPeriodic (fun x => φ (f x) (g x)) :=
  fun i x => by dsimp only; rw [hf i x, hg i x]

/-- Translating a periodic function by any vector gives a periodic function. -/
theorem translate (hf : IsTorusPeriodic f) (a : Vec 2) :
    IsTorusPeriodic (fun x => f (x + a)) := fun i x => by
  show f (x + basisVec i + a) = f (x + a)
  rw [show x + basisVec i + a = (x + a) + basisVec i by abel]; exact hf i (x + a)

theorem sub_basisVec (hf : IsTorusPeriodic f) (i : Fin 2) (x : Vec 2) :
    f (x - basisVec i) = f x := by
  have := hf i (x - basisVec i)
  rw [sub_add_cancel] at this
  exact this.symm

/-- Periodicity under every integer multiple of a basis vector. -/
theorem add_int_smul_basisVec (hf : IsTorusPeriodic f) (i : Fin 2) (n : ℤ) (x : Vec 2) :
    f (x + (n : ℝ) • basisVec i) = f x := by
  induction n using Int.induction_on generalizing x with
  | zero => simp
  | succ n ih =>
    have : x + ((n + 1 : ℤ) : ℝ) • basisVec i = (x + (n : ℝ) • basisVec i) + basisVec i := by
      push_cast; rw [add_smul, one_smul]; abel
    rw [this, hf i]; simpa using ih x
  | pred n ih =>
    have : x + ((-(n : ℤ) - 1 : ℤ) : ℝ) • basisVec i
        = (x + ((-(n : ℤ) : ℤ) : ℝ) • basisVec i) - basisVec i := by
      push_cast; rw [sub_smul, one_smul]; abel
    rw [this, sub_basisVec hf]; exact ih x

/-- Periodicity under every vector of the integer lattice (`basisVec`-combinations). -/
theorem add_lattice (hf : IsTorusPeriodic f) (n : Fin 2 → ℤ) (x : Vec 2) :
    f (x + ∑ i, (n i : ℝ) • basisVec i) = f x := by
  rw [Fin.sum_univ_two, ← add_assoc, hf.add_int_smul_basisVec 1 (n 1),
    hf.add_int_smul_basisVec 0 (n 0)]

end IsTorusPeriodic

instance isFiniteMeasure_eulerMeasure (T : ℝ) : IsFiniteMeasure (eulerMeasure T) := by
  refine ⟨?_⟩
  unfold eulerMeasure
  rw [Measure.restrict_apply_univ]
  exact (isCompact_Icc.prod isCompact_Icc : IsCompact (torusCube ×ˢ Icc (0 : ℝ) T)).measure_lt_top

/-- `eulerMeasure` is the product of the cube measure and the time-interval measure. -/
theorem eulerMeasure_eq_prod (T : ℝ) :
    eulerMeasure T = (volume.restrict torusCube).prod (volume.restrict (Icc 0 T)) := by
  unfold eulerMeasure
  rw [Measure.prod_restrict]
  rfl

end PDE
