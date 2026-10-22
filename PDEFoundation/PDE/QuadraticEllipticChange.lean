module

public import PDEFoundation.Ambient.QuadraticMatrixConjugation
public import PDEFoundation.PDE.ConstantSkew
public import PDEFoundation.PDE.LinearChange

/-! # Weak equations under quadratic elliptic normalization -/

@[expose] public section

namespace PDE

noncomputable section

variable {d : ℕ}

/-- Remove the skew part and transport an actual weak equation through
its canonical normalizer, assuming only lower quadratic coercivity of the
given matrix. -/
theorem IsWeakDivergenceFormSolutionOn.quadraticEllipticNormalize
    {U : Set (Vec d)} {a : CoeffField d} {u : H1Function U}
    {f : Vec d → ℝ} {F : Vec d → Vec d} {A0 : Mat d}
    (hLower : ∀ xi : Vec d,
      vecNormSq xi ≤ vecDot xi (matVecMul A0 xi))
    (hu : IsWeakDivergenceFormSolutionOn a U u f F) :
    let T := ellipticNormalizer A0
    let e := quadraticEllipticNormalizerContinuousLinearEquiv hLower
    IsWeakDivergenceFormSolutionOn
      (fun y => T * (a (e.symm y) - skewPart A0) * matTranspose T)
      (e '' U) (u.compLinearEquiv e)
      (fun y => f (e.symm y))
      (fun y => matVecMul T (F (e.symm y))) := by
  let T := ellipticNormalizer A0
  have hpos : (symmPart A0).PosDef := symmPart_posDef_of_one_le hLower
  let hT : IsUnit T := ellipticNormalizer_isUnit hpos
  let e := quadraticEllipticNormalizerContinuousLinearEquiv hLower
  have hskew : matTranspose (skewPart A0) = -skewPart A0 := by
    ext i j
    simp [matTranspose, skewPart]
    ring
  have hremoved := hu.sub_const_skew hskew
  have hchanged := hremoved.linearChange T hT
  simpa only [T, e, quadraticEllipticNormalizerContinuousLinearEquiv,
    matrixContinuousLinearEquiv_apply,
    matrixContinuousLinearEquiv_symm_apply] using hchanged

end

end PDE
