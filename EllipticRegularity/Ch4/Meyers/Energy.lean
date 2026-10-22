module

public import EllipticRegularity.Ch4.Meyers.Sharpness

/-!
# The energy density `√(∇u · a∇u)` of the planar-type example and normalized `L^p` norms
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4Meyers

open MeasureTheory Set

variable {d : ℕ} {w : Fin d → ℝ}

theorem vecDot_matVecMul_meyersCoeff_le (hw : ∀ i, w i = 0 ∨ w i = 1) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (x ξ : Vec d) : vecDot ξ (matVecMul (meyersCoeff w Λ x) ξ) ≤ Λ * vecNormSq ξ := by
  have h0 := vecNormSq_nonneg ξ
  rcases (axisSq_nonneg hw x).eq_or_lt with hs | hs
  · rw [meyersCoeff_of_axisSq_eq_zero w Λ hs.symm]
    have : matVecMul (1 : Mat d) ξ = ξ := by funext i; simp [matVecMul, Matrix.one_apply]
    rw [this]
    change vecNormSq ξ ≤ _
    nlinarith
  · rw [meyersCoeff_eq_qmat, vecDot_matVecMul_qmat]
    have hcs : (∑ j, (w j * x j) * ξ j) ^ 2 ≤ axisSq w x * vecNormSq ξ := by
      have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => w j * x j) ξ
      rw [sum_wx_sq hw] at this
      rw [vecNormSq_eq_sum_sq]
      exact this
    have h2 : (Λ - 1) / axisSq w x * (∑ j, (w j * x j) * ξ j) ^ 2 ≤ (Λ - 1) * vecNormSq ξ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hs]
      nlinarith [mul_le_mul_of_nonneg_left hcs (by linarith : (0 : ℝ) ≤ Λ - 1)]
    nlinarith

theorem eLpMeanNormOn_lt_top_of_memLp {U : Set (Vec d)} (hpos : 0 < volume U)
    (htop : volume U < ∞) {p : ℝ≥0∞} {f : Vec d → ℝ} (hf : MemLp f p (volumeOn U)) :
    eLpMeanNormOn U p f < ∞ := by
  rw [eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn htop]
  refine ENNReal.mul_lt_top ?_ hf.eLpNorm_lt_top
  exact ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg
    (ENNReal.inv_ne_top.mpr hpos.ne')

theorem memLp_of_eLpMeanNormOn_lt_top {U : Set (Vec d)} (htop : volume U < ∞)
    {p : ℝ≥0∞} {f : Vec d → ℝ}
    (h : eLpMeanNormOn U p f < ∞) : MemLp f p (volumeOn U) := by
  rw [eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn htop] at h
  have hne : (volume U)⁻¹ ^ (1 / p).toReal ≠ 0 := by
    have : (volume U)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr htop.ne
    intro h0
    rcases ENNReal.rpow_eq_zero_iff.mp h0 with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact this h1
    · exact absurd h2 (not_lt.mpr ENNReal.toReal_nonneg)
  have hlt : eLpNorm f p (volumeOn U) < ∞ :=
    ENNReal.lt_top_of_mul_ne_top_right h.ne hne
  exact hlt

end PDE.Ch4Meyers
