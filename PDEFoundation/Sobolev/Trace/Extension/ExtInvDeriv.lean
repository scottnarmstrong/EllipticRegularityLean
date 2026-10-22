module

public import PDEFoundation.Sobolev.Trace.Smooth.PullbackBound
import PDEFoundation.Sobolev.Trace.Smooth.Calculus

/-!
# Derivative of the inverse chart map and the chain rule for `F ∘ Ψ⁻¹`

For `F` differentiable on the half-space, the gradient of `F ∘ Ψ⁻¹` is bounded in the Euclidean
norm by `(n + 1)(1 + L)` times the model gradient length of `F`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

/-- Derivative of the inverse chart map. -/
theorem fderiv_graphMapInv_apply {i : Fin (n + 1)} {γ : Vec n → ℝ} {sgn : ℝ}
    (hγ : ContDiff ℝ 1 γ) (x h : Vec (n + 1)) :
    fderiv ℝ (graphMapInv i γ sgn) x h =
      (fun j => h (i.succAbove j), sgn * (h i - fderiv ℝ γ (fun j => x (i.succAbove j))
        (fun j => h (i.succAbove j)))) := by
  set ρ : Vec (n + 1) →L[ℝ] Vec n :=
    ContinuousLinearMap.pi (fun j => (ContinuousLinearMap.proj (i.succAbove j) :
      Vec (n + 1) →L[ℝ] ℝ)) with hρ
  have h1 : HasFDerivAt (fun x : Vec (n + 1) => fun j => x (i.succAbove j)) ρ x := ρ.hasFDerivAt
  have hγd : DifferentiableAt ℝ γ (fun j => x (i.succAbove j)) := (hγ.differentiable (by simp)) _
  have h2 : HasFDerivAt (fun x : Vec (n + 1) => sgn * (x i - γ (fun j => x (i.succAbove j))))
      (sgn • ((ContinuousLinearMap.proj i : Vec (n + 1) →L[ℝ] ℝ) -
        (fderiv ℝ γ (fun j => x (i.succAbove j))).comp ρ)) x :=
    ((hasFDerivAt_apply (𝕜 := ℝ) i x).sub (hγd.hasFDerivAt.comp x h1)).const_mul sgn
  have h3 := h1.prodMk h2
  have h4 : HasFDerivAt (graphMapInv i γ sgn) _ x := h3
  rw [h4.fderiv]
  rfl

/-- Crude bound of a directional derivative on the half-space by the model gradient length. -/
theorem abs_fderiv_model_apply_le {F : Vec n × ℝ → ℝ} {z : Vec n × ℝ}
    (u : Vec n) (s : ℝ) :
    |fderiv ℝ F z (u, s)| ≤ modelGradNorm F z * ((∑ j, |u j|) + |s|) := by
  set L := fderiv ℝ F z with hL
  set L1 : Vec n →L[ℝ] ℝ := L.comp (ContinuousLinearMap.inl ℝ (Vec n) ℝ) with hL1
  have hdec : ((u, s) : Vec n × ℝ) = (u, 0) + s • ((0 : Vec n), (1 : ℝ)) := by
    ext <;> simp
  have h1 : L (u, s) = L1 u + s * L (0, 1) := by
    rw [hdec, map_add, map_smul, smul_eq_mul]
    rfl
  have h2 : L1 u = ∑ j, L1 (basisVec j) * u j := by
    have := PDE.ContinuousLinearMap.apply_eq_vecDot_basisValues L1 u
    rw [this]; rfl
  have hM0 : 0 ≤ modelGradNorm F z := Real.sqrt_nonneg _
  have h3 : ∀ j, |L1 (basisVec j)| ≤ modelGradNorm F z := fun j => by
    have : L1 (basisVec j) = tanGrad F z j := rfl
    rw [this]
    unfold modelGradNorm
    refine Real.abs_le_sqrt ?_
    have := sq_apply_le_vecNormSq (tanGrad F z) j
    nlinarith [sq_nonneg (normDeriv F z)]
  have h4 : |L (0, 1)| ≤ modelGradNorm F z := by
    have : L (0, 1) = normDeriv F z := rfl
    rw [this]
    unfold modelGradNorm
    refine Real.abs_le_sqrt ?_
    nlinarith [vecNormSq_nonneg (tanGrad F z)]
  rw [h1, h2]
  calc |∑ j, L1 (basisVec j) * u j + s * L (0, 1)|
      ≤ |∑ j, L1 (basisVec j) * u j| + |s * L (0, 1)| := abs_add_le _ _
    _ ≤ (∑ j, |L1 (basisVec j)| * |u j|) + |s| * |L (0, 1)| := by
        gcongr
        · refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
          simp [abs_mul]
        · rw [abs_mul]
    _ ≤ (∑ j, modelGradNorm F z * |u j|) + |s| * modelGradNorm F z := by
        gcongr with j _
        exact h3 j
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- Directional derivatives of `F ∘ Ψ⁻¹` along coordinate directions. -/
theorem abs_classicalGradient_comp_inv_le (φ : GraphChart Ω) {F : Vec n × ℝ → ℝ}
    {x : Vec (n + 1)} (hF : DifferentiableAt ℝ F (φ.inv x)) (k : Fin (n + 1)) :
    |classicalGradient (F ∘ φ.inv) x k| ≤ (1 + φ.L) * modelGradNorm F (φ.inv x) := by
  have hinv : DifferentiableAt ℝ φ.inv x :=
    ((contDiff_graphMapInv (i := φ.i) (sgn := φ.sgn) φ.γ_contDiff).differentiable (by simp)) x
  rw [classicalGradient_apply, fderiv_comp x hF hinv, ContinuousLinearMap.comp_apply]
  have hD := fderiv_graphMapInv_apply (i := φ.i) (sgn := φ.sgn) φ.γ_contDiff x (basisVec k)
  have hDinv : fderiv ℝ φ.inv x (basisVec k) = _ := hD
  rw [hDinv]
  refine (abs_fderiv_model_apply_le _ _).trans ?_
  set h : Vec (n + 1) := basisVec k with hh
  set S1 : ℝ := ∑ j, |h (φ.i.succAbove j)| with hS1
  have hsum : |h φ.i| + S1 = 1 := by
    have : ∑ m, |h m| = 1 := by
      rw [Finset.sum_eq_single k]
      · simp [hh, basisVec_apply]
      · intro b _ hb
        simp [hh, basisVec_apply, hb]
      · simp
    rw [Fin.sum_univ_succAbove _ φ.i] at this
    linarith
  have hS1nn : 0 ≤ S1 := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hγ := abs_fderiv_apply_le_of_lip φ.γ_contDiff φ.L_nonneg φ.γ_lip
    (fun j => x (φ.i.succAbove j)) (fun j => h (φ.i.succAbove j))
  have hnorm := vecEuclideanNorm_le_sum_abs (fun j => h (φ.i.succAbove j))
  have hs : |φ.sgn * (h φ.i - fderiv ℝ φ.γ (fun j => x (φ.i.succAbove j))
      (fun j => h (φ.i.succAbove j)))| ≤ |h φ.i| + φ.L * S1 := by
    rw [abs_mul, abs_sgn, one_mul]
    refine (abs_sub _ _).trans ?_
    have := mul_le_mul_of_nonneg_left hnorm φ.L_nonneg
    linarith
  have hM0 : 0 ≤ modelGradNorm F (φ.inv x) := Real.sqrt_nonneg _
  have hL := φ.L_nonneg
  have hS1le : S1 ≤ 1 := by linarith [abs_nonneg (h φ.i)]
  have hfin : S1 + |φ.sgn * (h φ.i - fderiv ℝ φ.γ (fun j => x (φ.i.succAbove j))
      (fun j => h (φ.i.succAbove j)))| ≤ 1 + φ.L := by
    nlinarith [mul_le_mul_of_nonneg_left hS1le hL]
  calc _ ≤ modelGradNorm F (φ.inv x) * (1 + φ.L) := mul_le_mul_of_nonneg_left hfin hM0
    _ = _ := mul_comm _ _

/-- The Euclidean gradient length of `F ∘ Ψ⁻¹`. -/
theorem vecEuclideanNorm_classicalGradient_comp_inv_le (φ : GraphChart Ω) {F : Vec n × ℝ → ℝ}
    {x : Vec (n + 1)} (hF : DifferentiableAt ℝ F (φ.inv x)) :
    vecEuclideanNorm (classicalGradient (F ∘ φ.inv) x) ≤
      ((n : ℝ) + 1) * ((1 + φ.L) * modelGradNorm F (φ.inv x)) := by
  refine (vecEuclideanNorm_le_sum_abs _).trans ?_
  calc ∑ k, |classicalGradient (F ∘ φ.inv) x k|
      ≤ ∑ _k : Fin (n + 1), (1 + φ.L) * modelGradNorm F (φ.inv x) :=
        Finset.sum_le_sum fun k _ => abs_classicalGradient_comp_inv_le φ hF k
    _ = _ := by simp

end PDE.TraceLane
