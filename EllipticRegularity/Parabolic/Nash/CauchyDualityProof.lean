module

public import EllipticRegularity.Parabolic.Cauchy.Duality.CauchyDuality

/-!
# Proof of `PDE.cauchyDuality`

The full proof is in `EllipticRegularity.Parabolic.Cauchy.Duality`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE.Ch5NashCauchyDualityProof

theorem result (d : ℕ) (lam Lam : ℝ) (a : ParCoeffField d) (s t : ℝ) (hst : s < t)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s t)) (f g : Vec d → ℝ)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s t))
    (hu : IsCauchySolution a s t f u)
    (w : ParH1Function (univ : Set (Vec d)) (Icc s t))
    (hw : IsCauchySolution (parAdjCoeff a (s + t)) s t g w) :
    Integrable (fun x => g x * u.toFun (x, t)) volume ∧
      Integrable (fun x => f x * w.toFun (x, t)) volume ∧
      ∫ x, g x * u.toFun (x, t) = ∫ x, f x * w.toFun (x, t) :=
  PDE.Parabolic.Duality.cauchyDuality_core d lam Lam a s t hst ha f g hf hg u hu w hw

end PDE.Ch5NashCauchyDualityProof
