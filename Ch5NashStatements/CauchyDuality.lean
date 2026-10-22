module

public import EllipticRegularity.Parabolic.Nash.CauchyDualityProof

@[expose] public section

namespace PDE

open MeasureTheory Set

/-- Adjoint duality `⟨g, S(t,s) f⟩ = ⟨S*(s,t) g, f⟩` for `f, g ∈ L²`.  `u` solves the forward
problem on `[s,t]` with datum `f`; `w` solves the forward problem for the reflected transposed
coefficients `parAdjCoeff a (s + t)` with datum `g`, so `w(·,t)` is the backward adjoint solution
with terminal datum `g` evaluated at time `s`.  Both integrands are integrable. -/
theorem cauchyDuality (d : ℕ) (lam Lam : ℝ) (a : ParCoeffField d) (s t : ℝ) (hst : s < t)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s t)) (f g : Vec d → ℝ)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s t)) (hu : IsCauchySolution a s t f u)
    (w : ParH1Function (univ : Set (Vec d)) (Icc s t))
    (hw : IsCauchySolution (parAdjCoeff a (s + t)) s t g w) :
    Integrable (fun x => g x * u.toFun (x, t)) volume ∧
      Integrable (fun x => f x * w.toFun (x, t)) volume ∧
      ∫ x, g x * u.toFun (x, t) = ∫ x, f x * w.toFun (x, t) := by exact PDE.Ch5NashCauchyDualityProof.result d lam Lam a s t hst ha f g hf hg u hu w hw

end PDE
