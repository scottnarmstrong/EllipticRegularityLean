module

public import PDEFoundation.Sobolev.Inequalities.NashProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- The Nash inequality (Proposition 1.22). -/
theorem exists_nash_constant (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : H1Function (Set.univ : Set (Vec d)),
      Integrable u.toFun volume →
      ∫ x, u.toFun x ^ 2 ≤
        C * (∫ x, vecEuclideanNorm (u.grad x) ^ 2) ^ ((d : ℝ) / (d + 2)) *
          (∫ x, |u.toFun x|) ^ ((4 : ℝ) / (d + 2)) := by exact PDE.NashProof.result d hd

end PDE
