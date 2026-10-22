module

public import PDEFoundation.PDE.EllipticChange
public import PDEFoundation.Geometry.EuclideanBall.EllipticImage

/-! # Local weak equation in elliptically normalized coordinates -/

@[expose] public section

namespace PDE

noncomputable section

variable {d : ℕ}

/-- Restrict the canonically normalized weak equation to the round ball
inscribed in the linear image of the original ball. -/
theorem IsWeakDivergenceFormSolutionOn.ellipticNormalize_innerBall
    {a : CoeffField d} {F : Vec d → Vec d} {z : Vec d} {R : ℝ}
    (hR : 0 < R) {u : H1Function (euclideanBall z R)}
    (hsol : IsWeakDivergenceFormSolutionOn a (euclideanBall z R) u 0 F)
    {A0 : Mat d} {Lam : ℝ} (hA0 : IsEllipticMatrix 1 Lam A0) :
    let e := ellipticNormalizerContinuousLinearEquiv hA0
    let T := ellipticNormalizer A0
    let Y := euclideanBall (e z) (R / Real.sqrt Lam)
    let hY : Y ⊆ e '' euclideanBall z R :=
      euclideanBall_subset_ellipticNormalizer_image hA0 hR z
    let v := (u.compLinearEquiv e).restrict (isOpen_euclideanBall _ _) hY
    IsWeakDivergenceFormSolutionOn
      (fun y => T * (a (e.symm y) - skewPart A0) * matTranspose T)
      Y v 0 (fun y => matVecMul T (F (e.symm y))) := by
  let e := ellipticNormalizerContinuousLinearEquiv hA0
  let T := ellipticNormalizer A0
  let Y := euclideanBall (e z) (R / Real.sqrt Lam)
  have hY : Y ⊆ e '' euclideanBall z R :=
    euclideanBall_subset_ellipticNormalizer_image hA0 hR z
  have hfull := hsol.ellipticNormalize hA0
  have hImageOpen : IsOpen (e '' euclideanBall z R) :=
    e.isOpenMap _ (isOpen_euclideanBall z R)
  exact hfull.restrict hImageOpen (isOpen_euclideanBall _ _) hY

end

end PDE
