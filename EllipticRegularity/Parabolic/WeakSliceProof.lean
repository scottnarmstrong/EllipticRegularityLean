module

public import EllipticRegularity.Parabolic.WeakSlice.Result

/-!
# Proof of `PDE.parabWeakSlice` (Lemma 5.5)

Thin wrapper around `PDE.Parabolic.weak_slice` (full proof in
`EllipticRegularity/Parabolic/WeakSlice/Result.lean`).
-/

@[expose] public section

namespace PDE.ParabWeakSliceProof

open MeasureTheory Set

theorem result (d : ℕ) (lam Lam : ℝ) (U : Set (Vec d)) (hU : IsOpen U)
    (I : Set ℝ) (hI : I.OrdConnected) (a : ParCoeffField d)
    (ha : IsParabolicCoeff lam Lam a U I)
    (u : ParH1Function U I) (hu : IsParabolicWeakSolution a U I u)
    (ζ : Vec d → ℝ) (hζ : ContDiff ℝ 1 ζ) (hζc : HasCompactSupport ζ) (hζU : tsupport ζ ⊆ U)
    (s t : ℝ) (hs : s ∈ I) (ht : t ∈ I) (hst : s < t) :
    IntegrableOn (fun z : Vec d × ℝ => vecDot (matVecMul (a z) (u.grad z)) (spaceGradC1 ζ z.1))
        (U ×ˢ Ioc s t) ∧
      (∫ x in U, u.toFun (x, t) * ζ x) - (∫ x in U, u.toFun (x, s) * ζ x) =
        -∫ z in U ×ˢ Ioc s t, vecDot (matVecMul (a z) (u.grad z)) (spaceGradC1 ζ z.1) :=
  PDE.Parabolic.weak_slice d lam Lam U hU I hI a ha u hu ζ hζ hζc hζU s t hs ht hst

end PDE.ParabWeakSliceProof
