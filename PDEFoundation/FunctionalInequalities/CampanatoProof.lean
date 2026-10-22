module

public import PDEFoundation.Regularity.Holder
public import PDEFoundation.Sobolev.Mean
public import PDEFoundation.Geometry.EuclideanBall
public import PDEFoundation.FunctionalInequalities.Campanato.Representative

/-!
# Proof of `PDE.exists_campanato_characterization_constant` (Lemma 1.19)

`PDE.CampanatoProof.result` is the Campanato characterisation of Hölder
spaces (Lemma 1.19), with one constant `C(d)` chosen before `α` and `u`.

Part (1) telescopes the averages over the balls `B_{2^{-k} r}(x)` to a representative defined
everywhere on `B_{1/2}` (it agrees with `u` at Lebesgue points of round-ball averages) and compares
two points through a common ball.  Part (2) is the direct estimate
`⨍_{B_r(x)} |v - (v)_{B_r(x)}| ≤ K (2r)^α`.  The helper modules live in
`PDEFoundation.FunctionalInequalities.Campanato.*`.
-/

@[expose] public section

namespace PDE.CampanatoProof

open MeasureTheory

theorem result (d : ℕ) (_hd : 0 < d) :
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
              (fun y => |u y - integralAverage (euclideanBall x r) u|) ≤ C * K) := by
  have h2 : (2 : ℝ) ≤ 96 * 2 ^ d := by
    have : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
    linarith
  refine ⟨96 * 2 ^ d, by positivity, fun α hα hα1 u hu => ⟨fun K hK hA => ?_, ?_⟩⟩
  · exact exists_holder_representative_of_campanato hα hα1 hK hu hA
  · intro K hK h x hx r hr hr4
    refine (campanato_quantity_le_of_holder hα hα1 hK hu h hx hr hr4).trans ?_
    exact mul_le_mul_of_nonneg_right h2 hK

end PDE.CampanatoProof
