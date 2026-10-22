module

public import EllipticRegularity.Schauder.C1alphaProof

/-! # Local boundedness of gradients with Hölder data -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Hölder coefficients and forcing give an essentially bounded Euclidean
gradient on the half ball. The small Schauder scale is selected internally. -/
theorem memLp_top_vecEuclideanNorm_grad_halfBall_of_holder
    {d : ℕ} (hd : 0 < d) {Λ α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (a : CoeffField d) (F : Vec d → Vec d)
    (hell : ∀ x ∈ euclideanBall (0 : Vec d) 1,
      IsEllipticMatrix 1 Λ (a x))
    (ha : ∃ K : ℝ, 0 ≤ K ∧
      EuclideanMatrixHolderSeminormLE (euclideanBall (0 : Vec d) 1) a α K)
    (hF : ∃ K : ℝ, 0 ≤ K ∧
      EuclideanFieldHolderSeminormLE (euclideanBall (0 : Vec d) 1) F α K)
    (u : H1Function (euclideanBall (0 : Vec d) 1))
    (hsol : IsWeakDivergenceFormSolutionOn a
      (euclideanBall (0 : Vec d) 1) u 0 F) :
    MemLp (fun x => vecEuclideanNorm (u.grad x)) ∞
      (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) := by
  obtain ⟨C, hC, hschauder⟩ := SchauderC1Proof.result hd (Λ := Λ)
  let K := euclideanMatrixHolderSeminormOn
    (euclideanBall (0 : Vec d) 1) a α ha
  have hK : 0 ≤ K := euclideanMatrixHolderSeminormOn_nonneg ha
  let T := C⁻¹ * α * (1 - α)
  have hT : 0 < T := by
    dsimp only [T]
    exact mul_pos (mul_pos (inv_pos.mpr hC) hα0) (sub_pos.mpr hα1)
  let q := (T / (K + 1)) ^ (1 / α)
  have hKone : 0 < K + 1 := by linarith
  have hq : 0 < q := by
    dsimp only [q]
    exact Real.rpow_pos_of_pos (div_pos hT hKone) _
  let r₀ := min (1 / 4 : ℝ) q
  have hr₀ : 0 < r₀ := lt_min (by norm_num) hq
  have hr₀fourth : r₀ ≤ 1 / 4 := min_le_left _ _
  have hr₀q : r₀ ≤ q := min_le_right _ _
  have hqpow : q ^ α = T / (K + 1) := by
    dsimp only [q]
    rw [← Real.rpow_mul (div_nonneg hT.le hKone.le)]
    rw [show 1 / α * α = 1 by field_simp, Real.rpow_one]
  have hrpow : r₀ ^ α ≤ q ^ α :=
    Real.rpow_le_rpow hr₀.le hr₀q hα0.le
  have hsmall : r₀ ^ α * K ≤ C⁻¹ * α * (1 - α) := by
    change r₀ ^ α * K ≤ T
    calc
      r₀ ^ α * K ≤ q ^ α * K :=
        mul_le_mul_of_nonneg_right hrpow hK
      _ = T / (K + 1) * K := by rw [hqpow]
      _ ≤ T := by
        have hdiv : 0 ≤ T / (K + 1) := (div_pos hT hKone).le
        have heq : T / (K + 1) * (K + 1) = T := by field_simp
        calc
          T / (K + 1) * K ≤ T / (K + 1) * (K + 1) := by
            exact mul_le_mul_of_nonneg_left (by linarith) hdiv
          _ = T := heq
  let hresult := hschauder (α := α) hα0 hα1 (r₀ := r₀) hr₀ hr₀fourth
    a F hell ha hF hsmall u hsol
  exact hresult.choose_spec.choose_spec.choose

end

end PDE
