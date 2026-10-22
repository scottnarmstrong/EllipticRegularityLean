module

public import PDEFoundation.PDE.OneDimensionalGradientInterior
public import PDEFoundation.Regularity.FieldLpInfinity
public import PDEFoundation.Regularity.FieldHolderSeminorm

/-! # The one-dimensional interior Schauder estimate -/

@[expose] public section

namespace PDE

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

/-- The quantitative interior Schauder estimate in dimension one. -/
theorem exists_schauderC1alpha_constant_oneDimensional {Λ : ℝ} :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ}, 0 < α → α < 1 →
      ∀ {r₀ : ℝ}, 0 < r₀ → r₀ ≤ 1 / 4 →
      ∀ (a : CoeffField 1) (F : Vec 1 → Vec 1),
      (∀ x ∈ euclideanBall (0 : Vec 1) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ ha : ∃ K : ℝ, 0 ≤ K ∧
        EuclideanMatrixHolderSeminormLE (euclideanBall (0 : Vec 1) 1) a α K,
      ∀ hF : ∃ K : ℝ, 0 ≤ K ∧
        EuclideanFieldHolderSeminormLE (euclideanBall (0 : Vec 1) 1) F α K,
      r₀ ^ α * euclideanMatrixHolderSeminormOn
          (euclideanBall (0 : Vec 1) 1) a α ha ≤
        C⁻¹ * α * (1 - α) →
      ∀ u : H1Function (euclideanBall (0 : Vec 1) 1),
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec 1) 1) u 0 F →
      ∃ G : Vec 1 → Vec 1,
      ∃ hG : ∃ K : ℝ, 0 ≤ K ∧
        EuclideanFieldHolderSeminormLE
          (euclideanBall (0 : Vec 1) (1 / 2)) G α K,
      ∃ hgrad : MemLp (fun x => vecEuclideanNorm (u.grad x)) ∞
        (volumeOn (euclideanBall (0 : Vec 1) (1 / 2))),
      G =ᵐ[volumeOn (euclideanBall (0 : Vec 1) (1 / 2))] u.grad ∧
      euclideanFieldLpNormOn (euclideanBall (0 : Vec 1) (1 / 2)) ∞ u.grad hgrad +
          r₀ ^ α * euclideanFieldHolderSeminormOn
            (euclideanBall (0 : Vec 1) (1 / 2)) G α hG ≤
        (C / α ^ 2) * (r₀ ^ (-(1 : ℝ) / 2) *
          Real.sqrt (integralAverage (euclideanBall (0 : Vec 1) 1)
            (fun x => vecNormSq (u.grad x))) +
          r₀ ^ α / (1 - α) *
            euclideanFieldHolderSeminormOn
              (euclideanBall (0 : Vec 1) 1) F α hF) := by
  let C : ℝ := 8 * (1 + |Λ|)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro α hα hα1 r₀ hr₀ hr₀le a F hell ha hF hsmall u hsol
  let Ka := euclideanMatrixHolderSeminormOn (euclideanBall (0 : Vec 1) 1) a α ha
  let KF := euclideanFieldHolderSeminormOn (euclideanBall (0 : Vec 1) 1) F α hF
  have hKa : 0 ≤ Ka := euclideanMatrixHolderSeminormOn_nonneg ha
  have hKF : 0 ≤ KF := euclideanFieldHolderSeminormOn_nonneg hF
  have haKa : EuclideanMatrixHolderSeminormLE
      (euclideanBall (0 : Vec 1) 1) a α Ka :=
    euclideanMatrixHolderSeminormOn_bound ha
  have hFKF : EuclideanFieldHolderSeminormLE
      (euclideanBall (0 : Vec 1) 1) F α KF :=
    euclideanFieldHolderSeminormOn_bound hF
  let M := Real.sqrt (integralAverage (euclideanBall (0 : Vec 1) 1)
    (fun x => vecNormSq (u.grad x)))
  let X := r₀ ^ (-(1 / 2 : ℝ)) * M
  let Y := r₀ ^ α * KF
  let B := Λ * X + Y
  have hM : 0 ≤ M := Real.sqrt_nonneg _
  have hX : 0 ≤ X := mul_nonneg (Real.rpow_nonneg hr₀.le _) hM
  have hY : 0 ≤ Y := mul_nonneg (Real.rpow_nonneg hr₀.le _) hKF
  have hΛ : 1 ≤ Λ :=
    (hell 0 (center_mem_euclideanBall _ (by norm_num))).lam_le_Lam
  have hΛ0 : 0 ≤ Λ := zero_le_one.trans hΛ
  have hB : 0 ≤ B := add_nonneg (mul_nonneg hΛ0 hX) hY
  have hweight : r₀ ^ α * Ka ≤ 1 := by
    have hgap : 0 < 1 - α := sub_pos.mpr hα1
    have hαgap : α * (1 - α) ≤ 1 := by nlinarith
    have hCinv : C⁻¹ ≤ 1 := by
      have : 1 ≤ C := by dsimp [C]; linarith [abs_nonneg Λ]
      exact (inv_le_one₀ hC).2 this
    calc
      r₀ ^ α * Ka ≤ C⁻¹ * α * (1 - α) := hsmall
      _ ≤ 1 := by nlinarith [inv_nonneg.mpr hC.le]
  obtain ⟨G, hGae, hGpoint, hGholder⟩ :=
    exists_oneDimensional_gradient_interior_representative
      hr₀ hr₀le hα hKa hKF haKa hFKF hell u hsol
  have hBdef : Λ * r₀ ^ (-(1 / 2 : ℝ)) * M + KF * r₀ ^ α = B := by
    dsimp [B, X, Y]
    ring
  rw [hBdef] at hGpoint hGholder
  let hG : ∃ K : ℝ, 0 ≤ K ∧ EuclideanFieldHolderSeminormLE
      (euclideanBall (0 : Vec 1) (1 / 2)) G α K :=
    ⟨KF + Ka * B, add_nonneg hKF (mul_nonneg hKa hB), hGholder⟩
  have hhalfsub : euclideanBall (0 : Vec 1) (1 / 2) ⊆
      euclideanBall (0 : Vec 1) 1 :=
    euclideanBall_mono (by norm_num) (by norm_num)
  have hgradL2 : MemVectorL2On (euclideanBall (0 : Vec 1) (1 / 2)) u.grad :=
    fun i => (u.gradMemL2 i).mono_measure
      (Measure.restrict_mono hhalfsub le_rfl)
  obtain ⟨hgrad, hlinf⟩ :=
    exists_memLp_top_euclideanFieldLpNormOn_le_of_ae_representative
      (measurableSet_euclideanBall (0 : Vec 1) (1 / 2)) hgradL2
      hGae hB hGpoint
  refine ⟨G, hG, hgrad, hGae, ?_⟩
  have hseminorm : euclideanFieldHolderSeminormOn
      (euclideanBall (0 : Vec 1) (1 / 2)) G α hG ≤ KF + Ka * B :=
    euclideanFieldHolderSeminormOn_le hG
      (add_nonneg hKF (mul_nonneg hKa hB)) hGholder
  have hleft : euclideanFieldLpNormOn
        (euclideanBall (0 : Vec 1) (1 / 2)) ∞ u.grad hgrad +
      r₀ ^ α * euclideanFieldHolderSeminormOn
        (euclideanBall (0 : Vec 1) (1 / 2)) G α hG ≤ 2 * B + Y := by
    calc
      _ ≤ B + r₀ ^ α * (KF + Ka * B) :=
        add_le_add hlinf (mul_le_mul_of_nonneg_left hseminorm
          (Real.rpow_nonneg hr₀.le _))
      _ = B + Y + (r₀ ^ α * Ka) * B := by dsimp [Y]; ring
      _ ≤ B + Y + 1 * B := by
        convert add_le_add_left (mul_le_mul_of_nonneg_right hweight hB) (B + Y)
          using 1 <;> ring
      _ = 2 * B + Y := by ring
  have hgap : 0 < 1 - α := sub_pos.mpr hα1
  have hαsq : 0 < α ^ 2 := sq_pos_of_pos hα
  have hCΛ : 2 * Λ ≤ C := by
    dsimp [C]
    linarith [le_abs_self Λ]
  have hCthree : 3 * (1 - α) ≤ C := by
    dsimp [C]
    linarith [abs_nonneg Λ]
  have hXY : 0 ≤ X + Y / (1 - α) :=
    add_nonneg hX (div_nonneg hY hgap.le)
  have hcoarse : 2 * B + Y ≤ C * (X + Y / (1 - α)) := by
    dsimp [B]
    have hxpart : 2 * Λ * X ≤ C * X :=
      mul_le_mul_of_nonneg_right hCΛ hX
    have hypart : 3 * Y ≤ C * (Y / (1 - α)) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hgap).2
      calc
        3 * Y * (1 - α) = (3 * (1 - α)) * Y := by ring
        _ ≤ C * Y := mul_le_mul_of_nonneg_right hCthree hY
    linarith
  have hscale : C ≤ C / α ^ 2 := by
    apply (le_div_iff₀ hαsq).2
    have hαsqle : α ^ 2 ≤ 1 := by nlinarith
    exact mul_le_of_le_one_right hC.le hαsqle
  calc
    _ ≤ 2 * B + Y := hleft
    _ ≤ C * (X + Y / (1 - α)) := hcoarse
    _ ≤ (C / α ^ 2) * (X + Y / (1 - α)) :=
      mul_le_mul_of_nonneg_right hscale hXY
    _ = _ := by
      dsimp [X, Y, M, KF]
      simp only [div_eq_mul_inv]
      ring_nf

end

end PDE
