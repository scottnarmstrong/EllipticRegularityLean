module

public import PDEFoundation.Sobolev.Trace.Extension.ShiftSmooth
public import PDEFoundation.Sobolev.Trace.Smooth.ChainRule

/-!
# Chain rule through the inverse chart map

For `G` differentiable at `φ⁻¹ x`, the Euclidean length of the gradient of `G ∘ φ⁻¹` at `x` is at
most `(2 + L)` times the model gradient length of `G` at `φ⁻¹ x`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

/-- The restriction `x ↦ x ∘ succAbove i` as a continuous linear map. -/
noncomputable def shiftProj (n : ℕ) (i : Fin (n + 1)) : Vec (n + 1) →L[ℝ] Vec n :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (i.succAbove j)

theorem shiftProj_apply (i : Fin (n + 1)) (x : Vec (n + 1)) (j : Fin n) :
    shiftProj n i x j = x (i.succAbove j) := rfl

theorem vecEuclideanNorm_shiftProj_le (i : Fin (n + 1)) (v : Vec (n + 1)) :
    vecEuclideanNorm (shiftProj n i v) ≤ vecEuclideanNorm v := by
  unfold vecEuclideanNorm
  apply Real.sqrt_le_sqrt
  simp only [vecNormSq_eq_sum_sq]
  rw [Fin.sum_univ_succAbove _ i]
  simp only [shiftProj_apply]
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- The derivative of the inverse chart map. -/
noncomputable def shiftInvDeriv (φ : GraphChart Ω) (x : Vec (n + 1)) :
    Vec (n + 1) →L[ℝ] Vec n × ℝ :=
  (shiftProj n φ.i).prod (φ.sgn • ((ContinuousLinearMap.proj φ.i) -
    (fderiv ℝ φ.γ (shiftProj n φ.i x)).comp (shiftProj n φ.i)))

theorem GraphChart.hasFDerivAt_inv (φ : GraphChart Ω) (x : Vec (n + 1)) :
    HasFDerivAt φ.inv (shiftInvDeriv φ x) x := by
  have hP : HasFDerivAt (fun y : Vec (n + 1) => shiftProj n φ.i y) (shiftProj n φ.i) x :=
    (shiftProj n φ.i).hasFDerivAt
  have hγ : HasFDerivAt φ.γ (fderiv ℝ φ.γ (shiftProj n φ.i x)) (shiftProj n φ.i x) :=
    ((φ.γ_contDiff.differentiable (by simp)) _).hasFDerivAt
  have h2 := ((hasFDerivAt_apply (𝕜 := ℝ) φ.i x).sub (hγ.comp x hP)).const_mul φ.sgn
  exact hP.prodMk h2

theorem shiftInvDeriv_apply (φ : GraphChart Ω) (x v : Vec (n + 1)) :
    shiftInvDeriv φ x v = (shiftProj n φ.i v, φ.sgn * (v φ.i -
      fderiv ℝ φ.γ (shiftProj n φ.i x) (shiftProj n φ.i v))) := by
  simp [shiftInvDeriv]

theorem fderiv_model_apply_le {G : Vec n × ℝ → ℝ} {z : Vec n × ℝ} (a : Vec n) (s : ℝ) :
    |fderiv ℝ G z (a, s)| ≤ modelGradNorm G z * (vecEuclideanNorm a + |s|) := by
  have hsplit : ((a, s) : Vec n × ℝ) = (a, 0) + s • ((0 : Vec n), (1 : ℝ)) := by
    ext <;> simp
  have h1 : fderiv ℝ G z (a, 0) = vecDot (tanGrad G z) a := by
    have := PDE.ContinuousLinearMap.apply_eq_vecDot_basisValues
      ((fderiv ℝ G z).comp (ContinuousLinearMap.inl ℝ (Vec n) ℝ)) a
    exact this
  have h2 : fderiv ℝ G z (s • ((0 : Vec n), (1 : ℝ))) = s * normDeriv G z := by
    rw [map_smul]; rfl
  have hA : vecEuclideanNorm (tanGrad G z) ≤ modelGradNorm G z := by
    unfold modelGradNorm vecEuclideanNorm
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (normDeriv G z)])
  have hB := abs_normDeriv_le_modelGradNorm G z
  rw [hsplit, map_add, h1, h2]
  refine (abs_add_le _ _).trans ?_
  have e1 := abs_vecDot_le_vecEuclideanNorm_mul (tanGrad G z) a
  have e2 : |s * normDeriv G z| ≤ modelGradNorm G z * |s| := by
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hB (abs_nonneg _)
  have e3 : vecEuclideanNorm (tanGrad G z) * vecEuclideanNorm a ≤
      modelGradNorm G z * vecEuclideanNorm a :=
    mul_le_mul_of_nonneg_right hA (vecEuclideanNorm_nonneg _)
  nlinarith

theorem shift_gradNorm_le_of_fderiv_le {H : Vec (n + 1) → ℝ} {x : Vec (n + 1)} {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ v, |fderiv ℝ H x v| ≤ C * vecEuclideanNorm v) :
    vecEuclideanNorm (classicalGradient H x) ≤ C := by
  set v := classicalGradient H x with hv
  have h1 := h v
  rw [fderiv_apply_eq_vecDot_classicalGradient] at h1
  have h2 : vecDot v v = vecEuclideanNorm v ^ 2 := (vecEuclideanNorm_sq v).symm
  rw [← hv, h2, abs_of_nonneg (by positivity)] at h1
  by_contra hlt
  replace hlt := not_le.1 hlt
  have hpos : 0 < vecEuclideanNorm v := lt_of_le_of_lt hC hlt
  nlinarith

/-- Chain rule bound through the inverse chart map. -/
theorem GraphChart.gradNorm_comp_inv_le (φ : GraphChart Ω) {G : Vec n × ℝ → ℝ}
    {x : Vec (n + 1)} (hG : DifferentiableAt ℝ G (φ.inv x)) :
    vecEuclideanNorm (classicalGradient (G ∘ φ.inv) x) ≤
      (2 + φ.L) * modelGradNorm G (φ.inv x) := by
  have hL := φ.L_nonneg
  have hM : 0 ≤ modelGradNorm G (φ.inv x) := by
    unfold modelGradNorm; exact Real.sqrt_nonneg _
  refine shift_gradNorm_le_of_fderiv_le (by positivity) fun v => ?_
  rw [fderiv_comp x hG (φ.hasFDerivAt_inv x).differentiableAt, (φ.hasFDerivAt_inv x).fderiv,
    ContinuousLinearMap.comp_apply, shiftInvDeriv_apply]
  refine (fderiv_model_apply_le _ _).trans ?_
  have hP := vecEuclideanNorm_shiftProj_le φ.i v
  have hs : |φ.sgn * (v φ.i - fderiv ℝ φ.γ (shiftProj n φ.i x) (shiftProj n φ.i v))| ≤
      (1 + φ.L) * vecEuclideanNorm v := by
    rw [abs_mul, abs_sgn, one_mul]
    refine (abs_sub _ _).trans ?_
    have e1 := abs_apply_le_vecEuclideanNorm v φ.i
    have e2 := abs_fderiv_apply_le_of_lip φ.γ_contDiff φ.L_nonneg φ.γ_lip
      (shiftProj n φ.i x) (shiftProj n φ.i v)
    nlinarith [mul_le_mul_of_nonneg_left hP hL]
  have : vecEuclideanNorm (shiftProj n φ.i v) + |φ.sgn * (v φ.i -
      fderiv ℝ φ.γ (shiftProj n φ.i x) (shiftProj n φ.i v))| ≤ (2 + φ.L) * vecEuclideanNorm v := by
    nlinarith
  calc _ ≤ modelGradNorm G (φ.inv x) * ((2 + φ.L) * vecEuclideanNorm v) :=
        mul_le_mul_of_nonneg_left this hM
    _ = _ := by ring

end PDE.TraceLane
