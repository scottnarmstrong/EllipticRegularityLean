module

public import PDEFoundation.Monotonicity.FriedlandHayman.Suspension.Defs

/-!
# Friedland--Hayman: lifting a function of the first `n` coordinates

For `Φ : Vec n → ℝ` of class `C¹`, the function `x ↦ Φ (projFst x)` on `Vec (n + N)` is `C¹`
and its tangential gradient quantity on the sphere is `|∇Φ|² - (y·∇Φ)²` evaluated at `y = x'`.
-/

@[expose] public section

namespace PDE.FHLane

noncomputable section

namespace Susp

/-- The projection onto the first `n` coordinates as a continuous linear map. -/
def projL (n N : ℕ) : Vec (n + N) →L[ℝ] Vec n :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Fin (n + N) => ℝ) (Fin.castAdd N i)

theorem projL_apply {n N : ℕ} (x : Vec (n + N)) : projL n N x = projFst x := rfl

theorem projL_basisVec_castAdd {n N : ℕ} (j : Fin n) :
    projL n N (basisVec (Fin.castAdd N j)) = basisVec j := by
  ext i
  simp [projL_apply, projFst, basisVec_apply, Fin.castAdd_inj]

theorem projL_basisVec_natAdd {n N : ℕ} (j : Fin N) :
    projL n N (basisVec (Fin.natAdd n j)) = 0 := by
  ext i
  simp [projL_apply, projFst, basisVec_apply]
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

theorem contDiff_comp_projFst {n N : ℕ} {Φ : Vec n → ℝ} (hΦ : ContDiff ℝ 1 Φ) :
    ContDiff ℝ 1 (fun x : Vec (n + N) => Φ (projFst x)) :=
  hΦ.comp (projL n N).contDiff

theorem classicalGradient_comp_projFst_castAdd {n N : ℕ} {Φ : Vec n → ℝ} (hΦ : ContDiff ℝ 1 Φ)
    (x : Vec (n + N)) (j : Fin n) :
    classicalGradient (fun x : Vec (n + N) => Φ (projFst x)) x (Fin.castAdd N j) =
      classicalGradient Φ (projFst x) j := by
  have h := (hΦ.differentiable (by simp) (projFst x)).hasFDerivAt.comp x
    (projL n N).hasFDerivAt
  rw [classicalGradient_apply, classicalGradient_apply]
  have h2 : HasFDerivAt (fun x : Vec (n + N) => Φ (projFst x)) _ x := h
  rw [h2.fderiv]
  simp [projL_basisVec_castAdd]

theorem classicalGradient_comp_projFst_natAdd {n N : ℕ} {Φ : Vec n → ℝ} (hΦ : ContDiff ℝ 1 Φ)
    (x : Vec (n + N)) (j : Fin N) :
    classicalGradient (fun x : Vec (n + N) => Φ (projFst x)) x (Fin.natAdd n j) = 0 := by
  have h := (hΦ.differentiable (by simp) (projFst x)).hasFDerivAt.comp x
    (projL n N).hasFDerivAt
  rw [classicalGradient_apply]
  have h2 : HasFDerivAt (fun x : Vec (n + N) => Φ (projFst x)) _ x := h
  rw [h2.fderiv]
  simp [projL_basisVec_natAdd]

/-- The tangential gradient quantity of a lifted function. -/
theorem tgn_comp_projFst {n N : ℕ} {Φ : Vec n → ℝ} (hΦ : ContDiff ℝ 1 Φ) (x : Vec (n + N)) :
    tangentialGradientNormSq (fun x : Vec (n + N) => Φ (projFst x)) x =
      vecNormSq (classicalGradient Φ (projFst x)) -
        vecDot (classicalGradient Φ (projFst x)) (projFst x) ^ 2 := by
  have h1 : vecNormSq (classicalGradient (fun x : Vec (n + N) => Φ (projFst x)) x) =
      vecNormSq (classicalGradient Φ (projFst x)) := by
    rw [vecNormSq_eq_sum_sq, vecNormSq_eq_sum_sq, Fin.sum_univ_add]
    simp only [classicalGradient_comp_projFst_castAdd hΦ, classicalGradient_comp_projFst_natAdd hΦ]
    simp
  have h2 : vecDot (classicalGradient (fun x : Vec (n + N) => Φ (projFst x)) x) x =
      vecDot (classicalGradient Φ (projFst x)) (projFst x) := by
    unfold vecDot
    rw [Fin.sum_univ_add]
    simp only [classicalGradient_comp_projFst_castAdd hΦ, classicalGradient_comp_projFst_natAdd hΦ]
    simp [projFst]
  unfold tangentialGradientNormSq
  rw [h1, h2]

end Susp

end

end PDE.FHLane
