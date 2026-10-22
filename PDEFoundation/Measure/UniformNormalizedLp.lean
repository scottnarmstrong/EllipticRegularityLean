module

public import PDEFoundation.Measure.MeanLpBoundTransport

/-! # Uniform comparison of normalized local `Lᵖ` norms -/

@[expose] public section

namespace PDE

open MeasureTheory Set
open scoped ENNReal

noncomputable section

theorem rpow_one_div_le_max_one_self
    (r p : ℝ) (hr : 0 ≤ r) (hp : 1 ≤ p) :
    r ^ (1 / p) ≤ max 1 r := by
  by_cases hr1 : r ≤ 1
  · exact (Real.rpow_le_one hr hr1 (by positivity)).trans (le_max_left _ _)
  · have h1r : 1 ≤ r := le_of_not_ge hr1
    exact (Real.rpow_le_self_of_one_le h1r (by
      have hp0 : 0 < p := zero_lt_one.trans_le hp
      exact (div_le_one hp0).2 hp)).trans (le_max_right _ _)

/-- A lower volume bound makes restriction to arbitrary subdomains uniformly
bounded on normalized `Lᵖ`, uniformly over every real exponent `p ≥ 2`.
The constant depends only on the outer volume and the fixed lower bound. -/
theorem exists_uniform_lpMeanNormOn_le_of_volume_lower
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (W : Set (Vec d)) (hWPos : 0 < volume W) (hWTop : volume W < ∞)
    (m : ENNReal) (hmPos : 0 < m) (hmTop : m < ∞) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (p : ℝ), 2 ≤ p → ∀ (U : Set (Vec d)), U ⊆ W → m ≤ volume U →
      ∀ (f : Vec d → E) (_hf : MemLp f (ENNReal.ofReal p) (volumeOn W)),
        MemLp f (ENNReal.ofReal p) (volumeOn U) ∧
          (eLpNorm f (ENNReal.ofReal p) (normalizedVolumeOn U)).toReal ≤
            K * (eLpNorm f (ENNReal.ofReal p) (normalizedVolumeOn W)).toReal := by
  let K : ℝ := max 1 ((volume W).toReal / m.toReal)
  refine ⟨K, le_max_left _ _, ?_⟩
  intro p hp U hUW hmU f hf
  have hp0 : 0 < p := by linarith
  have hUTop : volume U < ∞ := lt_of_le_of_lt (measure_mono hUW) hWTop
  have hUPos : 0 < volume U := hmPos.trans_le hmU
  have hmeasure : volumeOn U ≤ volumeOn W :=
    Measure.restrict_mono hUW le_rfl
  have hfU : MemLp f (ENNReal.ofReal p) (volumeOn U) := hf.mono_measure hmeasure
  refine ⟨hfU, ?_⟩
  have hmeanU := memLp_normalizedVolumeOn_of_memLpOn hfU hUPos
  have hmeanW := memLp_normalizedVolumeOn_of_memLpOn hf hWPos
  rw [show (eLpNorm f (ENNReal.ofReal p) (normalizedVolumeOn U)).toReal =
      (volume U).toReal ^ (-(1 / (ENNReal.ofReal p)).toReal) *
        (eLpNorm f (ENNReal.ofReal p) (volumeOn U)).toReal by
      simpa only [lpMeanNormOn_eq_toReal] using!
        lpMeanNormOn_eq_volume_toReal_neg_rpow_mul_eLpNorm hUPos hUTop
          (ENNReal.ofReal p) f hfU,
    show (eLpNorm f (ENNReal.ofReal p) (normalizedVolumeOn W)).toReal =
      (volume W).toReal ^ (-(1 / (ENNReal.ofReal p)).toReal) *
        (eLpNorm f (ENNReal.ofReal p) (volumeOn W)).toReal by
      simpa only [lpMeanNormOn_eq_toReal] using!
        lpMeanNormOn_eq_volume_toReal_neg_rpow_mul_eLpNorm hWPos hWTop
          (ENNReal.ofReal p) f hf]
  have hnorm : (eLpNorm f (ENNReal.ofReal p) (volumeOn U)).toReal ≤
      (eLpNorm f (ENNReal.ofReal p) (volumeOn W)).toReal := by
    exact ENNReal.toReal_mono hf.eLpNorm_lt_top.ne (eLpNorm_mono_measure f hmeasure)
  have hmReal : 0 < m.toReal := ENNReal.toReal_pos hmPos.ne' hmTop.ne
  have hvolReal : 0 < (volume U).toReal :=
    ENNReal.toReal_pos hUPos.ne' hUTop.ne
  have hWReal : 0 < (volume W).toReal :=
    ENNReal.toReal_pos hWPos.ne' hWTop.ne
  have hratio : (volume W).toReal / (volume U).toReal ≤
      (volume W).toReal / m.toReal := by
    exact div_le_div_of_nonneg_left ENNReal.toReal_nonneg hmReal
      ((ENNReal.toReal_le_toReal hmTop.ne hUTop.ne).2 hmU)
  have hpow : ((volume U).toReal) ^ (-(1 / (ENNReal.ofReal p)).toReal) ≤
      K * ((volume W).toReal) ^ (-(1 / (ENNReal.ofReal p)).toReal) := by
    have hexp : (1 / (ENNReal.ofReal p)).toReal = 1 / p := by
      simp [ENNReal.toReal_ofReal hp0.le]
    rw [hexp]
    have hratio0 : 0 ≤ (volume W).toReal / (volume U).toReal := by positivity
    have hratioPow := Real.rpow_le_rpow hratio0 hratio (by positivity : 0 ≤ 1 / p)
    have hbound := rpow_one_div_le_max_one_self
      ((volume W).toReal / m.toReal) p (by positivity) (by linarith)
    -- Rearranging the ratio estimate gives the required comparison of negative powers.
    calc
      (volume U).toReal ^ (-(1 / p)) =
          ((volume W).toReal / (volume U).toReal) ^ (1 / p) *
            (volume W).toReal ^ (-(1 / p)) := by
              rw [Real.div_rpow ENNReal.toReal_nonneg hvolReal.le,
                Real.rpow_neg hvolReal.le, Real.rpow_neg ENNReal.toReal_nonneg]
              field_simp [hWReal.ne']
      _ ≤ ((volume W).toReal / m.toReal) ^ (1 / p) *
            (volume W).toReal ^ (-(1 / p)) :=
          mul_le_mul_of_nonneg_right hratioPow (Real.rpow_nonneg ENNReal.toReal_nonneg _)
      _ ≤ K * (volume W).toReal ^ (-(1 / p)) :=
          mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  exact (mul_le_mul hpow hnorm (ENNReal.toReal_nonneg) (by positivity)).trans_eq (by ring)

end

end PDE
