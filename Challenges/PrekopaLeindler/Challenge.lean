module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Prékopa–Leindler inequality

Challenge: the Prékopa–Leindler inequality for nonnegative integrable functions on `ℝ^d`.
-/

@[expose] public section

namespace PDE

open MeasureTheory

/-- The native coordinate model of `ℝ^d`: functions `Fin d → ℝ`, with Lebesgue measure the
product measure. -/
abbrev Vec (d : ℕ) := Fin d → ℝ

/-- Prékopa–Leindler inequality (Theorem 1.2).  Let `0 < l < 1` and let `f`, `g`, `h` be
nonnegative integrable functions on `ℝ^d` such that
`f(x)^l * g(y)^(1-l) ≤ h(l x + (1-l) y)` for all `x`, `y`.  Then
`(∫ f)^l * (∫ g)^(1-l) ≤ ∫ h`. -/
theorem prekopa_leindler (d : ℕ) {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1)
    (f g h : Vec d → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hh0 : ∀ x, 0 ≤ h x)
    (hf : Integrable f) (hg : Integrable g) (hh : Integrable h)
    (hyp : ∀ x y : Vec d, f x ^ l * g y ^ (1 - l) ≤ h (l • x + (1 - l) • y)) :
    (∫ x, f x) ^ l * (∫ x, g x) ^ (1 - l) ≤ ∫ x, h x := by
  sorry

end PDE
