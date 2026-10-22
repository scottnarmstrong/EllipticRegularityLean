module

public import PDEFoundation.FunctionalInequalities.PrekopaLeindlerProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- Prékopa–Leindler inequality (Theorem 1.2), for nonnegative integrable functions
(integrable `f`, `g`, `h`, real integrals). -/
theorem prekopa_leindler (d : ℕ) {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1)
    (f g h : Vec d → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hh0 : ∀ x, 0 ≤ h x)
    (hf : Integrable f) (hg : Integrable g) (hh : Integrable h)
    (hyp : ∀ x y : Vec d, f x ^ l * g y ^ (1 - l) ≤ h (l • x + (1 - l) • y)) :
    (∫ x, f x) ^ l * (∫ x, g x) ^ (1 - l) ≤ ∫ x, h x := by exact PDE.PrekopaLeindlerProof.result d hl0 hl1 f g h hf0 hg0 hh0 hf hg hh hyp

end PDE
