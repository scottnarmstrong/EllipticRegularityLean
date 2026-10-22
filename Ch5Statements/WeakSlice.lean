module

public import EllipticRegularity.Parabolic.WeakSliceProof

@[expose] public section

namespace PDE

open MeasureTheory Set

/-- Lemma 5.5: weak formulation at every time. -/
theorem parabWeakSlice (d : ℕ) (lam Lam : ℝ) (U : Set (Vec d)) (hU : IsOpen U)
    (I : Set ℝ) (hI : I.OrdConnected) (a : ParCoeffField d)
    (ha : IsParabolicCoeff lam Lam a U I)
    (u : ParH1Function U I) (hu : IsParabolicWeakSolution a U I u)
    (ζ : Vec d → ℝ) (hζ : ContDiff ℝ 1 ζ) (hζc : HasCompactSupport ζ) (hζU : tsupport ζ ⊆ U)
    (s t : ℝ) (hs : s ∈ I) (ht : t ∈ I) (hst : s < t) :
    IntegrableOn (fun z : Vec d × ℝ => vecDot (matVecMul (a z) (u.grad z)) (spaceGradC1 ζ z.1))
        (U ×ˢ Ioc s t) ∧
      (∫ x in U, u.toFun (x, t) * ζ x) - (∫ x in U, u.toFun (x, s) * ζ x) =
        -∫ z in U ×ˢ Ioc s t, vecDot (matVecMul (a z) (u.grad z)) (spaceGradC1 ζ z.1) := by exact PDE.ParabWeakSliceProof.result d lam Lam U hU I hI a ha u hu ζ hζ hζc hζU s t hs ht hst

end PDE
