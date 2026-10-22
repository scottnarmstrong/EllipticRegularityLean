module

public import EllipticRegularity.CalderonZygmund.LowExponent

/-! # Proof of `PDE.exists_calderonZygmund_identity` -/

@[expose] public section

namespace PDE.CZIdentityProof
open MeasureTheory
open scoped _root_.ENNReal
noncomputable section

theorem result
    (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (p : ℝ), 2 ≤ p →
      ∀ (a : CoeffField d),
      (∀ i j : Fin d,
        AEMeasurable (fun x => a x i j)
          (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
        IsMatrixPerturbationLE (1 / (C * p)) (a x) (1 : Mat d)) →
      ∀ (u : H1Function (euclideanBall (0 : Vec d) 1))
        (F : Vec d → Vec d),
      (∀ i : Fin d,
        AEStronglyMeasurable (fun x => F x i)
          (volumeOn (euclideanBall (0 : Vec d) 1))) →
      ∀ (hF : MemLp (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p)
          (volumeOn (euclideanBall (0 : Vec d) 1))),
      IsWeakDivergenceFormSolutionOn a
          (euclideanBall (0 : Vec d) 1) u (0 : Vec d → ℝ) F →
      MemW1p (euclideanBall (0 : Vec d) (1 / 2 : ℝ))
          (ENNReal.ofReal p) u.toFun ∧
        ∃ hgrad : MemLp (fun x => vecEuclideanNorm (u.grad x))
            (ENNReal.ofReal p)
            (volumeOn (euclideanBall (0 : Vec d) (1 / 2 : ℝ))),
          euclideanFieldLpMeanNormOn
              (euclideanBall (0 : Vec d) (1 / 2 : ℝ))
              (ENNReal.ofReal p) u.grad
              (memLp_normalizedVolumeOn_of_memLpOn hgrad
                (volume_euclideanBall_pos (0 : Vec d) (by norm_num))) ≤
            C *
              (Real.sqrt
                  (integralAverage (euclideanBall (0 : Vec d) 1)
                    (fun x => vecNormSq (u.grad x))) +
                p * euclideanFieldLpMeanNormOn
                  (euclideanBall (0 : Vec d) 1) (ENNReal.ofReal p) F
                  (memLp_normalizedVolumeOn_of_memLpOn hF
                    (volume_euclideanBall_pos (0 : Vec d) (by norm_num)))) := by
  obtain ⟨H, hH, hHigh⟩ := exists_calderonZygmund_highExponent_constants d hd
  obtain ⟨L, hL, hLow⟩ := exists_calderonZygmund_lowExponent_constants d hd
  let C : ℝ := 2 * max H L
  have hmax : 1 ≤ max H L := hH.trans (le_max_left _ _)
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hHC : H ≤ C := by
    have := le_max_left H L
    dsimp [C]
    linarith
  have h2LC : 2 * L ≤ C := by
    dsimp [C]
    exact mul_le_mul_of_nonneg_left (le_max_right H L) (by norm_num)
  have hLC : L ≤ C := by linarith only [h2LC, hL]
  refine ⟨C, hC, ?_⟩
  intro p hp a ha hclose u F hFcoord hF hsol
  have hp0 : 0 ≤ p := by linarith
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hU0 := Real.sqrt_nonneg
    (integralAverage (euclideanBall (0 : Vec d) 1) (fun x => vecNormSq (u.grad x)))
  have hNF0 : 0 ≤ euclideanFieldLpMeanNormOn (euclideanBall (0 : Vec d) 1)
      (ENNReal.ofReal p) F
      (memLp_normalizedVolumeOn_of_memLpOn hF (volume_euclideanBall_pos _ (by norm_num))) :=
    ENNReal.toReal_nonneg
  by_cases hpHigh : 4 ≤ p
  · have hcloseH : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
        IsMatrixPerturbationLE (1 / (H * p)) (a x) 1 := by
      filter_upwards [hclose] with x hx
      intro xi
      apply (hx xi).trans
      apply mul_le_mul_of_nonneg_right _ (vecEuclideanNorm_nonneg xi)
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (mul_le_mul_of_nonneg_right hHC hp0)
    obtain ⟨hW, hg, hest⟩ := hHigh p hpHigh a ha hcloseH u F hFcoord hF hsol
    refine ⟨hW, hg, hest.trans ?_⟩
    exact mul_le_mul_of_nonneg_right hHC (add_nonneg hU0 (mul_nonneg hp0 hNF0))
  · have hprod : 2 * C ≤ C * p := by
      simpa only [mul_comm C 2] using mul_le_mul_of_nonneg_left hp hC0
    have hdenBase : 4 * L ≤ 2 * C := by linarith only [h2LC]
    have hden : 4 * L ≤ C * p := hdenBase.trans hprod
    have hcloseL : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
        IsMatrixPerturbationLE (1 / (4 * L)) (a x) 1 := by
      filter_upwards [hclose] with x hx
      intro xi
      apply (hx xi).trans
      apply mul_le_mul_of_nonneg_right _ (vecEuclideanNorm_nonneg xi)
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
    obtain ⟨hW, hg, hest⟩ := hLow p hp (le_of_not_ge hpHigh) a ha hcloseL u F hFcoord hF hsol
    refine ⟨hW, hg, hest.trans ?_⟩
    have hNFmul : euclideanFieldLpMeanNormOn (euclideanBall (0 : Vec d) 1)
        (ENNReal.ofReal p) F
        (memLp_normalizedVolumeOn_of_memLpOn hF (volume_euclideanBall_pos _ (by norm_num))) ≤
        p * euclideanFieldLpMeanNormOn (euclideanBall (0 : Vec d) 1)
        (ENNReal.ofReal p) F
        (memLp_normalizedVolumeOn_of_memLpOn hF (volume_euclideanBall_pos _ (by norm_num))) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (by linarith : 1 ≤ p) hNF0
    exact (mul_le_mul_of_nonneg_right hLC (add_nonneg hU0 hNF0)).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hNFmul) hC0)

end
end PDE.CZIdentityProof
