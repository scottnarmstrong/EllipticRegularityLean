module

public import PDEFoundation.Measure.FiniteCoverLp
public import PDEFoundation.Measure.UniformNormalizedLp

/-! # Normalized `Lᵖ` bounds over finite covers -/

@[expose] public section

namespace PDE

open MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable section

/-- Uniform normalized bounds on a finite measurable cover glue to a normalized
bound on the target. The constant is independent of the exponent `p ≥ 2`. -/
theorem exists_uniform_eLpMeanNorm_le_of_finset_cover
    {d : ℕ} {E ι : Type*} [NormedAddCommGroup E] [DecidableEq ι]
    (s : Finset ι) (V : Set (Vec d)) (hV : MeasurableSet V)
    (hVPos : 0 < volume V) (hVTop : volume V < ∞)
    (M : ENNReal) (hMTop : M < ∞) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (p : ℝ), 2 ≤ p → ∀ (U : ι → Set (Vec d)),
      (∀ i ∈ s, MeasurableSet (U i)) →
      V ⊆ ⋃ i ∈ s, U i →
      (∀ i ∈ s, 0 < volume (U i)) →
      (∀ i ∈ s, volume (U i) < ∞) →
      (∀ i ∈ s, volume (U i) ≤ M) →
      ∀ (f : Vec d → E) (B : ℝ), 0 ≤ B →
      (∀ i ∈ s, ∃ _hf : MemLp f (ENNReal.ofReal p) (volumeOn (U i)),
        (eLpNorm f (ENNReal.ofReal p) (normalizedVolumeOn (U i))).toReal ≤ B) →
      ∃ _hfV : MemLp f (ENNReal.ofReal p) (volumeOn V),
        (eLpNorm f (ENNReal.ofReal p) (normalizedVolumeOn V)).toReal ≤ K * B := by
  let K : ℝ := s.card * max 1 M.toReal * max 1 (volume V).toReal⁻¹
  refine ⟨K, by positivity, ?_⟩
  intro p hp U hU hcover hUPos hUTop hUM f B hB hlocal
  have hp0 : 0 < p := by linarith
  have hpENN : (1 : ENNReal) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff (by positivity)]
    linarith
  choose hf hmean using hlocal
  have hglue := memLp_and_eLpNorm_le_sum_of_finset_cover hpENN f U s V
    hU hV hcover hf
  refine ⟨hglue.1, ?_⟩
  have hexp : (1 / (ENNReal.ofReal p)).toReal = 1 / p := by
    simp [ENNReal.toReal_ofReal hp0.le]
  have hexp_nonneg : 0 ≤ 1 / p := by positivity
  have hexp_le : 1 / p ≤ 1 := (div_le_one hp0).2 (by linarith)
  have hMnonneg : 0 ≤ M.toReal := ENNReal.toReal_nonneg
  have hlocalRaw : ∀ i ∈ s,
      (eLpNorm f (ENNReal.ofReal p) (volumeOn (U i))).toReal ≤
        max 1 M.toReal * B := by
    intro i hi
    have hUiReal : (volume (U i)).toReal ≤ M.toReal :=
      (ENNReal.toReal_le_toReal (hUTop i hi).ne hMTop.ne).2 (hUM i hi)
    have hpowM : (volume (U i)).toReal ^ (1 / p) ≤ max 1 M.toReal := by
      calc
        _ ≤ M.toReal ^ (1 / p) := Real.rpow_le_rpow ENNReal.toReal_nonneg hUiReal hexp_nonneg
        _ ≤ max 1 M.toReal := by
          by_cases hM : M.toReal ≤ 1
          · exact (Real.rpow_le_one hMnonneg hM hexp_nonneg).trans (le_max_left _ _)
          · exact (Real.rpow_le_self_of_one_le (le_of_not_ge hM) hexp_le).trans
              (le_max_right _ _)
    have heqRaw : eLpNorm f (ENNReal.ofReal p) (volumeOn (U i)) =
        volume (U i) ^ (1 / p) *
          eLpNorm f (ENNReal.ofReal p) (normalizedVolumeOn (U i)) := by
      simpa only [eLpNormOn, eLpMeanNormOn, hexp] using
        eLpNormOn_eq_volume_rpow_mul_eLpMeanNormOn
          (hUPos i hi) (hUTop i hi) (ENNReal.ofReal p) f
    rw [heqRaw, ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
    exact mul_le_mul hpowM (hmean i hi) (by positivity) (by positivity)
  have hrawV : (eLpNorm f (ENNReal.ofReal p) (volumeOn V)).toReal ≤
      s.card * (max 1 M.toReal * B) := by
    calc
      _ ≤ (∑ i ∈ s, eLpNorm f (ENNReal.ofReal p) (volumeOn (U i))).toReal :=
        ENNReal.toReal_mono (ne_of_lt ((ENNReal.sum_lt_top).2 (by intro i hi; exact (hf i hi).eLpNorm_lt_top))) hglue.2
      _ = ∑ i ∈ s, (eLpNorm f (ENNReal.ofReal p) (volumeOn (U i))).toReal := by
        rw [ENNReal.toReal_sum (fun i hi => (hf i hi).eLpNorm_lt_top.ne)]
      _ ≤ ∑ _i ∈ s, max 1 M.toReal * B := Finset.sum_le_sum fun i hi => hlocalRaw i hi
      _ = s.card * (max 1 M.toReal * B) := by simp
  have hVinv : (volume V).toReal ^ (-(1 / p)) ≤ max 1 (volume V).toReal⁻¹ := by
    rw [Real.rpow_neg (ENNReal.toReal_nonneg)]
    have heq : ((volume V).toReal ^ (1 / p))⁻¹ =
        (volume V).toReal⁻¹ ^ (1 / p) := by
      rw [← Real.inv_rpow (ENNReal.toReal_nonneg)]
    rw [heq]
    exact rpow_one_div_le_max_one_self _ p (by positivity) (by linarith)
  rw [show (eLpNorm f (ENNReal.ofReal p) (normalizedVolumeOn V)).toReal =
      (volume V).toReal ^ (-(1 / p)) *
        (eLpNorm f (ENNReal.ofReal p) (volumeOn V)).toReal by
    simpa only [lpMeanNormOn_eq_toReal, hexp] using!
      lpMeanNormOn_eq_volume_toReal_neg_rpow_mul_eLpNorm hVPos hVTop
        (ENNReal.ofReal p) f hglue.1]
  calc
    _ ≤ max 1 (volume V).toReal⁻¹ * (s.card * (max 1 M.toReal * B)) :=
      mul_le_mul hVinv hrawV (by positivity) (by positivity)
    _ = K * B := by simp [K]; ring

end

end PDE
