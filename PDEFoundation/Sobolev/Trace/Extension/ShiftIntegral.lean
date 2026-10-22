module

public import PDEFoundation.Sobolev.Trace.Extension.ShiftPoint
public import PDEFoundation.Sobolev.Trace.Smooth.Transfer

/-!
# Integral bounds for `shift τ - ext` on `Ω`

Pointwise bounds by `∑ⱼ Kⱼ R_{j,τ}(φⱼ⁻¹ x)` are converted into bounds for the `L^p(Ω)` integrals by
the measure preserving chart maps: `∫ |w|^p ≤ ∑ⱼ cⱼ ∫_{t>0} Q_{j,τ}`, where `Q` is the integrand of
`modelExt_tendsto_shift`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

/-- The integrand of `modelExt_tendsto_shift`. -/
noncomputable def shiftQ (F : Vec n × ℝ → ℝ) (p τ : ℝ) (z : Vec n × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (|F (z.1, z.2 + τ) - F z| ^ p) +
    ENNReal.ofReal (|normDeriv F (z.1, z.2 + τ) - normDeriv F z| ^ p) +
    ENNReal.ofReal (vecEuclideanNorm (tanGrad F (z.1, z.2 + τ) - tanGrad F z) ^ p)

theorem shift_ofReal_add3_rpow_le {p : ℝ} (hp : 1 ≤ p) {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) :
    ENNReal.ofReal ((a + b + c) ^ p) ≤ ENNReal.ofReal ((3 : ℝ) ^ (p - 1)) *
      (ENNReal.ofReal (a ^ p) + ENNReal.ofReal (b ^ p) + ENNReal.ofReal (c ^ p)) := by
  have h := shift_ofReal_sum_rpow_le (Finset.univ : Finset (Fin 3)) hp ![a, b, c]
    (fun i => by fin_cases i <;> simp [ha, hb, hc])
  simpa [Fin.sum_univ_three] using h

theorem shiftR_rpow_le (F : Vec n × ℝ → ℝ) {p : ℝ} (hp : 1 ≤ p) (τ : ℝ) (z : Vec n × ℝ) :
    ENNReal.ofReal (shiftR F τ z ^ p) ≤ ENNReal.ofReal ((3 : ℝ) ^ (p - 1)) * shiftQ F p τ z :=
  shift_ofReal_add3_rpow_le hp (abs_nonneg _) (abs_nonneg _) (vecEuclideanNorm_nonneg _)

theorem measurable_shiftQ {F : Vec n × ℝ → ℝ} (hF : Measurable F) (p τ : ℝ) :
    Measurable (shiftQ F p τ) := by
  have hs : Measurable fun z : Vec n × ℝ => (z.1, z.2 + τ) :=
    (continuous_fst.prodMk (continuous_snd.add continuous_const)).measurable
  have hnd : Measurable (normDeriv F) := measurable_fderiv_apply_const ℝ F ((0 : Vec n), (1 : ℝ))
  have htan : ∀ i : Fin n, Measurable fun z => tanGrad F z i := fun i =>
    measurable_fderiv_apply_const ℝ F (basisVec i, (0 : ℝ))
  have h1 : Measurable fun z => |F (z.1, z.2 + τ) - F z| ^ p :=
    ((continuous_abs.measurable.comp ((hF.comp hs).sub hF))).pow_const p
  have h2 : Measurable fun z => |normDeriv F (z.1, z.2 + τ) - normDeriv F z| ^ p :=
    ((continuous_abs.measurable.comp ((hnd.comp hs).sub hnd))).pow_const p
  have h3 : Measurable fun z => vecEuclideanNorm (tanGrad F (z.1, z.2 + τ) - tanGrad F z) ^ p := by
    refine ((continuous_vecEuclideanNorm n).measurable.comp ?_).pow_const p
    exact Measurable.of_eval fun i => ((htan i).comp hs).sub (htan i)
  unfold shiftQ
  exact ((ENNReal.measurable_ofReal.comp h1).add (ENNReal.measurable_ofReal.comp h2)).add
    (ENNReal.measurable_ofReal.comp h3)

theorem GraphChart.lintegral_comp_inv (φ : GraphChart Ω) (k : Vec n × ℝ → ℝ≥0∞) :
    ∫⁻ x, k (φ.inv x) = ∫⁻ z, k z := by
  have h := φ.measurePreserving_map.lintegral_comp_emb φ.homeo.measurableEmbedding
    (fun y => k (φ.inv y))
  simp only [φ.inv_map] at h
  exact h.symm

/-- Integral bound on `Ω`. -/
theorem ExtData.exists_integral_bound (D : ExtData Ω) (hΩo : IsOpen Ω) {p : ℝ} (hp : 1 < p)
    {g : Vec (n + 1) → ℝ} (hg : IsBesov Ω (1 - 1 / p) p g) (K : Fin D.A.N → ℝ)
    (hK : ∀ j, 0 ≤ K j) :
    ∃ c : Fin D.A.N → ℝ≥0∞, (∀ j, c j ≠ ⊤) ∧ ∀ τ : ℝ, ∀ w : Vec (n + 1) → ℝ,
      (∀ x ∈ Ω, |w x| ≤ ∑ j, K j * (upperHalf n).indicator
          (shiftR (modelExt n (D.flat j g)) τ) ((D.A.chart j).inv x)) →
      ∫⁻ x in Ω, ENNReal.ofReal (|w x| ^ p) ≤
        ∑ j, c j * ∫⁻ z in upperHalf n, shiftQ (modelExt n (D.flat j g)) p τ z := by
  have hp0 : 0 < p := by linarith
  refine ⟨fun j => ENNReal.ofReal ((D.A.N : ℝ) ^ (p - 1)) *
    (ENNReal.ofReal (K j ^ p) * ENNReal.ofReal ((3 : ℝ) ^ (p - 1))),
    fun j => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top), fun τ w hw => ?_⟩
  set Qi : Fin D.A.N → Vec (n + 1) → ℝ≥0∞ := fun j x => (upperHalf n).indicator
    (shiftQ (modelExt n (D.flat j g)) p τ) ((D.A.chart j).inv x) with hQi
  have hQm : ∀ j, Measurable (Qi j) := fun j =>
    ((measurable_shiftQ (measurable_modelExt_of_locallyIntegrable
      (D.locallyIntegrable_flat j hp hg)) p τ).indicator
      (shift_measurableSet_upperHalf n)).comp (D.A.chart j).contDiff_inv.continuous.measurable
  have hpt : ∀ x ∈ Ω, ENNReal.ofReal (|w x| ^ p) ≤ ENNReal.ofReal ((D.A.N : ℝ) ^ (p - 1)) *
      ∑ j, ENNReal.ofReal (K j ^ p) * (ENNReal.ofReal ((3 : ℝ) ^ (p - 1)) * Qi j x) := by
    intro x hx
    set r : Fin D.A.N → ℝ := fun j => (upperHalf n).indicator
      (shiftR (modelExt n (D.flat j g)) τ) ((D.A.chart j).inv x) with hr
    have hr0 : ∀ j, 0 ≤ r j := fun j => by
      by_cases hz : (D.A.chart j).inv x ∈ upperHalf n
      · simp only [hr, indicator_of_mem hz]; exact shiftR_nonneg _ _ _
      · simp [hr, indicator_of_notMem hz]
    have h1 := shift_ofReal_sum_rpow_le (Finset.univ : Finset (Fin D.A.N)) hp.le
      (fun j => K j * r j) (fun j => mul_nonneg (hK j) (hr0 j))
    rw [Finset.card_univ, Fintype.card_fin] at h1
    refine (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (abs_nonneg _) (hw x hx) hp0.le)).trans
      (h1.trans (mul_le_mul' le_rfl (Finset.sum_le_sum fun j _ => ?_)))
    rw [Real.mul_rpow (hK j) (hr0 j), ENNReal.ofReal_mul (Real.rpow_nonneg (hK j) _)]
    refine mul_le_mul' le_rfl ?_
    by_cases hz : (D.A.chart j).inv x ∈ upperHalf n
    · simp only [hr, hQi, indicator_of_mem hz]
      exact shiftR_rpow_le _ hp.le τ _
    · simp [hr, hQi, indicator_of_notMem hz, Real.zero_rpow hp0.ne']
  calc ∫⁻ x in Ω, ENNReal.ofReal (|w x| ^ p)
      ≤ ∫⁻ x in Ω, ENNReal.ofReal ((D.A.N : ℝ) ^ (p - 1)) *
          ∑ j, ENNReal.ofReal (K j ^ p) * (ENNReal.ofReal ((3 : ℝ) ^ (p - 1)) * Qi j x) :=
        setLIntegral_mono' hΩo.measurableSet hpt
    _ ≤ ∫⁻ x, ENNReal.ofReal ((D.A.N : ℝ) ^ (p - 1)) *
          ∑ j, ENNReal.ofReal (K j ^ p) * (ENNReal.ofReal ((3 : ℝ) ^ (p - 1)) * Qi j x) :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal ((D.A.N : ℝ) ^ (p - 1)) *
          ∑ j, ENNReal.ofReal (K j ^ p) * (ENNReal.ofReal ((3 : ℝ) ^ (p - 1)) *
            ∫⁻ x, Qi j x) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_finsetSum' _ fun j _ =>
            (((hQm j).const_mul (ENNReal.ofReal ((3 : ℝ) ^ (p - 1)))).const_mul
              (ENNReal.ofReal (K j ^ p))).aemeasurable]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have : ∫⁻ x, Qi j x = ∫⁻ z in upperHalf n, shiftQ (modelExt n (D.flat j g)) p τ z := by
          simp only [hQi]
          rw [(D.A.chart j).lintegral_comp_inv (fun z => (upperHalf n).indicator
            (shiftQ (modelExt n (D.flat j g)) p τ) z),
            lintegral_indicator (shift_measurableSet_upperHalf n)]
        rw [this]
        ring

end PDE.TraceLane
