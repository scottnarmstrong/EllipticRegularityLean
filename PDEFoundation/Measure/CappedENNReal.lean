module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Finite real caps of extended nonnegative values

These lemmas truncate an `ℝ≥0∞` value at an `ℝ≥0` level before applying
`toReal`, so infinite values retain the correct finite-cap behavior.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

/-- The real value of `v` capped at the finite nonnegative level `N`. -/
noncomputable def cappedENNReal (v : ℝ≥0∞) (N : NNReal) : ℝ :=
  (min v (N : ℝ≥0∞)).toReal

theorem min_coe_nnreal_ne_top (v : ℝ≥0∞) (N : NNReal) :
    min v (N : ℝ≥0∞) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)

/-- Re-embedding a finite real cap recovers the literal extended-value cap. -/
@[simp]
theorem ofReal_cappedENNReal (v : ℝ≥0∞) (N : NNReal) :
    ENNReal.ofReal (cappedENNReal v N) = min v (N : ℝ≥0∞) := by
  exact ENNReal.ofReal_toReal (min_coe_nnreal_ne_top v N)

theorem cappedENNReal_nonneg (v : ℝ≥0∞) (N : NNReal) :
    0 ≤ cappedENNReal v N :=
  ENNReal.toReal_nonneg

theorem cappedENNReal_le (v : ℝ≥0∞) (N : NNReal) :
    cappedENNReal v N ≤ (N : ℝ) := by
  exact ENNReal.toReal_mono ENNReal.coe_ne_top (min_le_right _ _)

/-- A nonnegative real threshold lies below the cap exactly when it lies below
both the original extended value and the cap parameter. -/
theorem lt_cappedENNReal_iff {v : ℝ≥0∞} {N : NNReal} {t : ℝ} (ht : 0 ≤ t) :
    t < cappedENNReal v N ↔
      ENNReal.ofReal t < v ∧ t < (N : ℝ) := by
  unfold cappedENNReal
  rw [← ENNReal.ofReal_lt_iff_lt_toReal ht (min_coe_nnreal_ne_top v N),
    lt_min_iff, ENNReal.ofReal_lt_coe_iff ht]

/-- Increasing the finite cap parameter increases the capped real value. -/
theorem cappedENNReal_mono_right (v : ℝ≥0∞) :
    Monotone (cappedENNReal v) := by
  intro N M hNM
  apply ENNReal.toReal_mono (min_coe_nnreal_ne_top v M)
  exact min_le_min le_rfl (mod_cast hNM)

/-- Finite real capping preserves measurability. -/
theorem Measurable.cappedENNReal
    {α : Type*} [MeasurableSpace α] {f : α → ℝ≥0∞}
    (hf : Measurable f) (N : NNReal) :
    Measurable fun x => cappedENNReal (f x) N := by
  exact (hf.min measurable_const).ennreal_toReal

/-- Positive natural caps exhaust every extended nonnegative value, including
`⊤`. -/
theorem iSup_ofReal_cappedENNReal_nat (v : ℝ≥0∞) :
    (⨆ n : ℕ,
      ENNReal.ofReal (cappedENNReal v ((n + 1 : ℕ) : NNReal))) = v := by
  simp_rw [ofReal_cappedENNReal]
  change (⨆ n : ℕ, v ⊓ ((n + 1 : ℕ) : ℝ≥0∞)) = v
  rw [← inf_iSup_eq]
  have hsup : (⨆ n : ℕ, ((n + 1 : ℕ) : ℝ≥0∞)) = ⊤ := by
    have hmono : Monotone (fun n : ℕ => (n : ℝ≥0∞)) := by
      intro n m hnm
      exact Nat.cast_le.mpr hnm
    calc
      (⨆ n : ℕ, ((n + 1 : ℕ) : ℝ≥0∞)) =
          ⨆ n : ℕ, (n : ℝ≥0∞) := by
        exact hmono.iSup_nat_add 1
      _ = ⊤ := ENNReal.iSup_natCast
  rw [hsup, inf_top_eq]

end PDE
