module

public import PDEFoundation.Monotonicity.AltCaffarelliFriedmanProof

@[expose] public section

open scoped ENNReal NNReal

namespace PDE

open MeasureTheory

/-- Alt--Caffarelli--Friedman monotonicity formula for `d ≥ 3`, with finiteness of the functional
(Theorem 2.13).  If `u₊, u₋ ∈ H¹(B_R)` are continuous, nonnegative, weakly subharmonic, vanish at
`0` and have disjoint positivity sets, then `r ↦ r⁻⁴ ∏_± ∫_{B_r} |∇u_±|² |x|^{2-d}` is monotone on
`(0, R)` and finite there. -/
theorem alt_caffarelli_friedman (d : ℕ) (hd : 3 ≤ d) (R : ℝ) (hR : 0 < R)
    (up um : H1Function (euclideanBall (0 : Vec d) R))
    (hup_cont : ContinuousOn up.toFun (euclideanBall (0 : Vec d) R))
    (hum_cont : ContinuousOn um.toFun (euclideanBall (0 : Vec d) R))
    (hup_nonneg : ∀ x ∈ euclideanBall (0 : Vec d) R, 0 ≤ up.toFun x)
    (hum_nonneg : ∀ x ∈ euclideanBall (0 : Vec d) R, 0 ≤ um.toFun x)
    (hup_sub : IsWeakDivergenceFormSubharmonicOn (fun _ => (1 : Mat d))
      (euclideanBall (0 : Vec d) R) up)
    (hum_sub : IsWeakDivergenceFormSubharmonicOn (fun _ => (1 : Mat d))
      (euclideanBall (0 : Vec d) R) um)
    (hup0 : up.toFun 0 = 0) (hum0 : um.toFun 0 = 0)
    (hdisj : ∀ x ∈ euclideanBall (0 : Vec d) R, up.toFun x * um.toFun x = 0) :
    MonotoneOn (acfFunctional up.grad um.grad) (Set.Ioo 0 R) ∧
      ∀ r ∈ Set.Ioo 0 R, acfFunctional up.grad um.grad r ≠ ⊤ :=
  PDE.AltCaffarelliFriedmanProof.result d hd R hR up um hup_cont hum_cont hup_nonneg hum_nonneg hup_sub hum_sub hup0 hum0 hdisj

end PDE
