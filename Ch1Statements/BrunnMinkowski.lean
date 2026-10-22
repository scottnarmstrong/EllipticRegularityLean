module

public import PDEFoundation.FunctionalInequalities.BrunnMinkowskiProof

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal Pointwise

/-- Brunn–Minkowski inequality (Theorem 1.3), in `[0,∞]`-valued form (all volumes are
finite since `A`, `B`, `A + B` are compact). -/
theorem brunn_minkowski (d : ℕ) (hd : 0 < d) (A B : Set (Vec d))
    (hA : IsCompact A) (hB : IsCompact B) (hAne : A.Nonempty) (hBne : B.Nonempty) :
    volume A ^ ((1 : ℝ) / d) + volume B ^ ((1 : ℝ) / d) ≤ volume (A + B) ^ ((1 : ℝ) / d) := by exact PDE.BrunnMinkowskiProof.result d hd A B hA hB hAne hBne

end PDE
