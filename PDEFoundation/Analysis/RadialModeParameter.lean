module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

namespace PDE

/-- The critical planar radial mode and its exact coefficient parameter. -/
theorem radialMode_critical_parameter (p : ℝ) (hp : 2 < p) :
    let β := 1 - 2 / p
    let δ := (1 - β ^ 2) / (1 + β ^ 2)
    0 < β ∧ β < 1 ∧ 0 < δ ∧ δ < 1 ∧
      β = Real.sqrt ((1 - δ) / (1 + δ)) ∧
      δ = 2 * (p - 1) / (p ^ 2 - 2 * p + 2) ∧
      p * (1 - β) = 2 := by
  let β := 1 - 2 / p
  let δ := (1 - β ^ 2) / (1 + β ^ 2)
  have hp0 : 0 < p := lt_trans (by norm_num) hp
  have hβ0 : 0 < β := sub_pos.mpr ((div_lt_one hp0).mpr hp)
  have hβ1 : β < 1 := sub_lt_self 1 (div_pos (by norm_num) hp0)
  have hden : 0 < 1 + β ^ 2 := by positivity
  have hnum : 0 < 1 - β ^ 2 := by nlinarith only [hβ0, hβ1]
  have hδ0 : 0 < δ := div_pos hnum hden
  have hδ1 : δ < 1 := (div_lt_one hden).mpr (by nlinarith only [hβ0])
  have hratio : (1 - δ) / (1 + δ) = β ^ 2 := by
    dsimp only [δ]
    field_simp
    ring
  have hsqrt : β = Real.sqrt ((1 - δ) / (1 + δ)) := by
    rw [hratio, Real.sqrt_sq hβ0.le]
  refine ⟨hβ0, hβ1, hδ0, hδ1, hsqrt, ?_, ?_⟩
  · have hpd : p ^ 2 - 2 * p + 2 ≠ 0 := by
      have hs : 0 ≤ (p - 1) ^ 2 := sq_nonneg _
      nlinarith only [hs]
    apply (div_eq_div_iff hden.ne' hpd).mpr
    dsimp only [β]
    field_simp
    ring
  · field_simp
    ring

end PDE
