module

public import PDEFoundation.Ambient.MatrixConjugation
public import PDEFoundation.PDE.ConstantSkew
public import PDEFoundation.PDE.LinearChange

/-! # Weak equations under the canonical elliptic normalization -/

@[expose] public section

namespace PDE

noncomputable section

variable {d : ℕ}

/-- Remove the skew part and transport an actual weak equation through
the canonical elliptic normalizer. -/
theorem IsWeakDivergenceFormSolutionOn.ellipticNormalize
    {U : Set (Vec d)} {a : CoeffField d} {u : H1Function U}
    {F : Vec d → Vec d} {A0 : Mat d} {Lam : ℝ}
    (hA0 : IsEllipticMatrix 1 Lam A0)
    (hu : IsWeakDivergenceFormSolutionOn a U u 0 F) :
    let e := ellipticNormalizerContinuousLinearEquiv hA0
    let T := ellipticNormalizer A0
    IsWeakDivergenceFormSolutionOn
      (fun y => T * (a (e.symm y) - skewPart A0) * matTranspose T)
      (e '' U) (u.compLinearEquiv e) 0
      (fun y => matVecMul T (F (e.symm y))) := by
  let T := ellipticNormalizer A0
  have hone : ∀ x : Vec d, vecNormSq x ≤ vecDot x (matVecMul A0 x) := by
    intro x
    simpa only [one_mul] using hA0.coercive x
  have hpos : (symmPart A0).PosDef := symmPart_posDef_of_one_le hone
  have hT : IsUnit T := ellipticNormalizer_isUnit hpos
  have hskew : matTranspose (skewPart A0) = -skewPart A0 := by
    ext i j
    simp [matTranspose, skewPart]
    ring
  have hremoved := hu.sub_const_skew hskew
  have hchanged := hremoved.linearChange T hT
  simpa only [T, ellipticNormalizerContinuousLinearEquiv,
    matrixContinuousLinearEquiv_apply,
    matrixContinuousLinearEquiv_symm_apply] using! hchanged

end

end PDE
