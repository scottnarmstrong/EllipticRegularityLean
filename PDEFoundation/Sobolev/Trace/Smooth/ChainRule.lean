module

public import PDEFoundation.Sobolev.Trace.Smooth.Pullback

/-!
# Chain rule for the model gradient

For `F` differentiable at `Ψ z`, the model gradient of `F ∘ Ψ` at `z` is bounded by
`(n (1 + L) + 1) |∇F (Ψ z)|`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

theorem abs_sgn (φ : GraphChart Ω) : |φ.sgn| = 1 := by
  have := sq_abs φ.sgn
  rw [φ.sgn_sq] at this
  nlinarith [abs_nonneg φ.sgn]

theorem normDeriv_comp_le (φ : GraphChart Ω) {F : Vec (n + 1) → ℝ} {z : Vec n × ℝ}
    (hF : DifferentiableAt ℝ F (φ.map z)) :
    |normDeriv (F ∘ φ.map) z| ≤ vecEuclideanNorm (classicalGradient F (φ.map z)) := by
  have hφ : DifferentiableAt ℝ φ.map z := (φ.contDiff_map.differentiable (by simp)) z
  unfold normDeriv
  rw [fderiv_comp z hF hφ, ContinuousLinearMap.comp_apply]
  refine (abs_fderiv_apply_le_vecEuclideanNorm_gradient_mul F _ _).trans ?_
  have h1 : fderiv ℝ φ.map z (0, 1) =
      Fin.insertNth (α := fun _ => ℝ) φ.i φ.sgn (0 : Vec n) := by
    refine (fderiv_graphMap_apply (i := φ.i) (γ := φ.γ) (sgn := φ.sgn) φ.γ_contDiff z
      (0, 1)).trans ?_
    simp only [map_zero, zero_add, mul_one]
  have h2 : vecEuclideanNorm (fderiv ℝ φ.map z (0, 1)) ≤ 1 := by
    rw [h1]
    refine (vecEuclideanNorm_insertNth_le _ _).trans ?_
    have : vecEuclideanNorm (0 : Vec n) = 0 := vecEuclideanNorm_eq_zero_iff.2 rfl
    rw [this, abs_sgn]; norm_num
  calc _ ≤ vecEuclideanNorm (classicalGradient F (φ.map z)) * 1 :=
        mul_le_mul_of_nonneg_left h2 (vecEuclideanNorm_nonneg _)
    _ = _ := mul_one _

theorem abs_tanGrad_comp_le (φ : GraphChart Ω) {F : Vec (n + 1) → ℝ} {z : Vec n × ℝ}
    (hF : DifferentiableAt ℝ F (φ.map z)) (k : Fin n) :
    |tanGrad (F ∘ φ.map) z k| ≤ (1 + φ.L) * vecEuclideanNorm (classicalGradient F (φ.map z)) := by
  have hφ : DifferentiableAt ℝ φ.map z := (φ.contDiff_map.differentiable (by simp)) z
  unfold tanGrad
  rw [fderiv_comp z hF hφ, ContinuousLinearMap.comp_apply]
  refine (abs_fderiv_apply_le_vecEuclideanNorm_gradient_mul F _ _).trans ?_
  have h1 : fderiv ℝ φ.map z (basisVec k, 0) =
      Fin.insertNth (α := fun _ => ℝ) φ.i (fderiv ℝ φ.γ z.1 (basisVec k)) (basisVec k) := by
    refine (fderiv_graphMap_apply (i := φ.i) (γ := φ.γ) (sgn := φ.sgn) φ.γ_contDiff z
      (basisVec k, 0)).trans ?_
    simp only [mul_zero, add_zero]
  have h2 : vecEuclideanNorm (fderiv ℝ φ.map z (basisVec k, 0)) ≤ 1 + φ.L := by
    rw [h1]
    refine (vecEuclideanNorm_insertNth_le _ _).trans ?_
    have := abs_fderiv_apply_le_of_lip φ.γ_contDiff φ.L_nonneg φ.γ_lip z.1 (basisVec k)
    rw [vecEuclideanNorm_basisVec] at this ⊢
    linarith
  calc _ ≤ vecEuclideanNorm (classicalGradient F (φ.map z)) * (1 + φ.L) :=
        mul_le_mul_of_nonneg_left h2 (vecEuclideanNorm_nonneg _)
    _ = _ := mul_comm _ _

theorem modelGradNorm_comp_le (φ : GraphChart Ω) {F : Vec (n + 1) → ℝ} {z : Vec n × ℝ}
    (hF : DifferentiableAt ℝ F (φ.map z)) :
    modelGradNorm (F ∘ φ.map) z ≤
      ((n : ℝ) * (1 + φ.L) + 1) * vecEuclideanNorm (classicalGradient F (φ.map z)) := by
  set G := vecEuclideanNorm (classicalGradient F (φ.map z)) with hG
  have hG0 : 0 ≤ G := vecEuclideanNorm_nonneg _
  have hL := φ.L_nonneg
  have ha : vecEuclideanNorm (tanGrad (F ∘ φ.map) z) ≤ n * ((1 + φ.L) * G) := by
    refine (vecEuclideanNorm_le_sum_abs _).trans ?_
    calc ∑ k, |tanGrad (F ∘ φ.map) z k| ≤ ∑ _k : Fin n, (1 + φ.L) * G :=
          Finset.sum_le_sum fun k _ => abs_tanGrad_comp_le φ hF k
      _ = _ := by simp
  have hb := normDeriv_comp_le φ hF
  unfold modelGradNorm
  have hdef : vecNormSq (tanGrad (F ∘ φ.map) z) = vecEuclideanNorm (tanGrad (F ∘ φ.map) z) ^ 2 :=
    (vecEuclideanNorm_sq _).symm
  rw [hdef]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have ha0 := vecEuclideanNorm_nonneg (tanGrad (F ∘ φ.map) z)
  have hb' : normDeriv (F ∘ φ.map) z ^ 2 ≤ G ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_nonneg hn (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + φ.L) hG0)]

end PDE.TraceLane
