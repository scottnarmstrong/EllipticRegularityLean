module

public import PDEFoundation.FunctionalInequalities.CampanatoProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- Campanato characterisation of Hölder spaces (Lemma 1.19).  Let
`A = sup_{x ∈ B_{1/2}} sup_{0<r<1/4} r^{-α} ⨍_{B_r(x)} |u - (u)_{B_r(x)}|`.
(1) `A ≤ K` gives a Hölder representative on `B_{1/2}` with seminorm `≤ C α⁻¹ K`
    (`C⁻¹ α [u]_{C^{0,α}(B_{1/2})} ≤ A`, with `[u]` of the representative);
(2) a Hölder representative on `B_1` with seminorm `≤ K` gives `A ≤ C K`.
One constant `C(d)`, chosen before `α` and `u`. -/
theorem exists_campanato_characterization_constant (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      ∀ u : Vec d → ℝ, IntegrableOn u (euclideanBall (0 : Vec d) 1) →
        (∀ K : ℝ, 0 ≤ K →
          (∀ x ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ, 0 < r → r < 1 / 4 →
            r ^ (-α) * integralAverage (euclideanBall x r)
              (fun y => |u y - integralAverage (euclideanBall x r) u|) ≤ K) →
          HasEuclideanHolderRepresentativeOn (euclideanBall (0 : Vec d) (1 / 2)) u α
            (C * α⁻¹ * K)) ∧
        (∀ K : ℝ, 0 ≤ K →
          HasEuclideanHolderRepresentativeOn (euclideanBall (0 : Vec d) 1) u α K →
          ∀ x ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ, 0 < r → r < 1 / 4 →
            r ^ (-α) * integralAverage (euclideanBall x r)
              (fun y => |u y - integralAverage (euclideanBall x r) u|) ≤ C * K) := by exact PDE.CampanatoProof.result d hd

end PDE
