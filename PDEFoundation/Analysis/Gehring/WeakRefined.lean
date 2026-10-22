module

public import PDEFoundation.Analysis.Gehring.WeakType

/-!
# The refined weak-type bound (Lemma 4.6)

For `k ≥ 0` and `s > 0`: `|{M k > s}| ≤ (2 · 3^d / s) ∫_{k > s/2} k`.
-/

@[expose] public section

namespace PDE.Gehring

open MeasureTheory Set
open scoped ENNReal

theorem cubeAvg_le_add {d : ℕ} {k l : Vec d → ℝ} {c : Vec d} {r : ℝ} (hr : 0 < r) {a : ℝ≥0∞}
    (h : ∀ y, ‖k y‖ₑ ≤ ‖l y‖ₑ + a) : cubeAvg k c r ≤ cubeAvg l c r + a := by
  unfold cubeAvg
  have hpos := volume_closedCenteredAxisCube_pos c hr
  have hfin := volume_closedCenteredAxisCube_ne_top c r
  calc (∫⁻ y in closedCenteredAxisCube c r, ‖k y‖ₑ) / volume (closedCenteredAxisCube c r)
      ≤ ((∫⁻ y in closedCenteredAxisCube c r, ‖l y‖ₑ) +
          a * volume (closedCenteredAxisCube c r)) / volume (closedCenteredAxisCube c r) := by
        refine ENNReal.div_le_div_right ?_ _
        calc (∫⁻ y in closedCenteredAxisCube c r, ‖k y‖ₑ)
            ≤ ∫⁻ y in closedCenteredAxisCube c r, (‖l y‖ₑ + a) := lintegral_mono h
          _ ≤ _ := by
            refine (lintegral_add_right' _ aemeasurable_const).le.trans ?_
            rw [setLIntegral_const]
    _ = _ := by
        rw [ENNReal.add_div, ENNReal.mul_div_cancel_right hpos.ne' hfin]

/-- **Lemma 4.6**, indicator form (no measurability needed):
for `k ≥ 0` and `s > 0`,
`|{M k > s}| ≤ (2 · 3^d / s) ∫ k · 1_{k > s/2}`. -/
theorem volume_lt_cubeMaximal_le_indicator {d : ℕ} (hd : 0 < d) {k : Vec d → ℝ}
    (hk : ∀ y, 0 ≤ k y) {s : ℝ} (hs : 0 < s) :
    volume {x | ENNReal.ofReal s < cubeMaximal k x} ≤
      ENNReal.ofReal (2 * 3 ^ d / s) *
        ∫⁻ y, {y | s / 2 < k y}.indicator (fun y => ‖k y‖ₑ) y := by
  set k1 : Vec d → ℝ := {y | s / 2 < k y}.indicator k with hk1
  have hnorm : ∀ y, ‖k1 y‖ₑ = {y | s / 2 < k y}.indicator (fun y => ‖k y‖ₑ) y := by
    intro y
    by_cases h : s / 2 < k y <;> simp [hk1, h]
  have hpt : ∀ y, ‖k y‖ₑ ≤ ‖k1 y‖ₑ + ENNReal.ofReal (s / 2) := by
    intro y
    by_cases h : s / 2 < k y
    · simp [hk1, h]
    · push Not at h
      calc ‖k y‖ₑ = ENNReal.ofReal (k y) := by
              rw [← ofReal_norm, Real.norm_of_nonneg (hk y)]
        _ ≤ ENNReal.ofReal (s / 2) := ENNReal.ofReal_le_ofReal h
        _ ≤ _ := le_add_self
  have hsub : {x | ENNReal.ofReal s < cubeMaximal k x} ⊆
      {x | ENNReal.ofReal (s / 2) < cubeMaximal k1 x} := by
    intro x hx
    have hx : ENNReal.ofReal s < cubeMaximal k x := hx
    have hle : cubeMaximal k x ≤ cubeMaximal k1 x + ENNReal.ofReal (s / 2) := by
      rw [cubeMaximal_le_iff]
      intro c r hr hxc
      exact (cubeAvg_le_add hr hpt).trans
        (add_le_add_left (cubeAvg_le_cubeMaximal k1 hr hxc) _)
    have hs2 : ENNReal.ofReal s = ENNReal.ofReal (s / 2) + ENNReal.ofReal (s / 2) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
    have := lt_of_lt_of_le hx hle
    rw [hs2] at this
    exact (ENNReal.add_lt_add_iff_right ENNReal.ofReal_ne_top).1 this
  refine (measure_mono hsub).trans ?_
  refine (volume_lt_cubeMaximal_le hd k1 (by positivity : 0 < s / 2)).trans ?_
  simp_rw [hnorm]
  refine le_of_eq ?_
  congr 2
  field_simp

/-- **Lemma 4.6** for an a.e. measurable `k ≥ 0`:
`|{M k > s}| ≤ (2 · 3^d / s) ∫_{k > s/2} k`. -/
theorem volume_lt_cubeMaximal_le_setLIntegral {d : ℕ} (hd : 0 < d) {k : Vec d → ℝ}
    (hk : ∀ y, 0 ≤ k y) (hkm : AEMeasurable k volume) {s : ℝ} (hs : 0 < s) :
    volume {x | ENNReal.ofReal s < cubeMaximal k x} ≤
      ENNReal.ofReal (2 * 3 ^ d / s) * ∫⁻ y in {y | s / 2 < k y}, ‖k y‖ₑ := by
  refine (volume_lt_cubeMaximal_le_indicator hd hk hs).trans (le_of_eq ?_)
  rw [lintegral_indicator₀]
  exact nullMeasurableSet_lt aemeasurable_const hkm

end PDE.Gehring
