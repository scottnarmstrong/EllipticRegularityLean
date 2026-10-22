module

public import PDEFoundation.Analysis.Gehring.AbsorbNumerics

/-!
# The truncated absorption inequality (Lemma 4.6)

For `d ≥ 2`, `A ≥ 1`, `ε ≤ 1/(8 G A)`, and `I_L = ∫ g min(g,L)^ε`:
`I_L < ∞` and `I_L ≤ (1/8) I_L + B N_σ ∫ h V_L^ε`.
-/

@[expose] public section

namespace PDE.Gehring

open MeasureTheory Set
open scoped ENNReal

variable {d : ℕ}

theorem truncMoment_lt_top {g : Vec d → ℝ} (hg0 : ∀ x, 0 ≤ g x) (hg : Integrable g volume)
    {ε L : ℝ} (hε : 0 ≤ ε) : truncMoment g L ε < ∞ := by
  have h1 : truncMoment g L ε ≤ ENNReal.ofReal L ^ ε * ∫⁻ x, ENNReal.ofReal (g x) := by
    unfold truncMoment
    rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hε ENNReal.ofReal_ne_top)]
    refine lintegral_mono fun x => ?_
    calc ENNReal.ofReal (g x) * (min (ENNReal.ofReal (g x)) (ENNReal.ofReal L)) ^ ε
        ≤ ENNReal.ofReal (g x) * ENNReal.ofReal L ^ ε := by
          gcongr; exact min_le_right _ _
      _ = _ := mul_comm _ _
  refine lt_of_le_of_lt h1 (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hε
    ENNReal.ofReal_ne_top) ?_)
  rw [← ofReal_integral_eq_lintegral_ofReal hg (Filter.Eventually.of_forall hg0)]
  exact ENNReal.ofReal_lt_top

/-- Measurability of `t ↦ ∫_{S_t} w` for a measurable `S ⊆ ℝ × ℝ^d`. -/
theorem measurable_lintegral_slice {S : Set (ℝ × Vec d)} (hS : MeasurableSet S)
    {w : Vec d → ℝ≥0∞} (hw : Measurable w) :
    Measurable fun t : ℝ => ∫⁻ x in {x | (t, x) ∈ S}, w x := by
  classical
  have : ∀ t : ℝ, ∫⁻ x in {x | (t, x) ∈ S}, w x =
      ∫⁻ x, (S.indicator (fun q : ℝ × Vec d => w q.2)) (t, x) := by
    intro t
    rw [show {x | (t, x) ∈ S} = Prod.mk t ⁻¹' S from rfl,
      ← lintegral_indicator (measurable_prodMk_left hS)]
    refine lintegral_congr fun x => ?_
    by_cases h : (t, x) ∈ S <;> simp [h]
  simp_rw [this]
  exact Measurable.lintegral_prod_right' ((hw.comp measurable_snd).indicator hS)

open Classical in
/-- **Truncated absorption.** -/
theorem absorption (hd : 2 ≤ d) {g h : Vec d → ℝ} (hg0 : ∀ x, 0 ≤ g x) (hh0 : ∀ x, 0 ≤ h x)
    (hgm : Measurable g) (hg : Integrable g volume) (hc : HasCompactSupport g)
    (hh : LocallyIntegrable h volume)
    {σ A B ε L : ℝ} (hσ : σ = 2 ∨ σ = 4) (hA : 1 ≤ A) (hB : 0 ≤ B) (hε : 0 < ε)
    (hεA : ε ≤ 1 / (8 * gehringG d * A)) (hL : 0 < L)
    (hrh : ∀ (z : Vec d) (r : ℝ), 0 < r → GehringRH d σ A B g h z r) :
    truncMoment g L ε ≤ ENNReal.ofReal (1 / 8) * truncMoment g L ε +
      ENNReal.ofReal (B * gehringN σ d) *
        ∫⁻ x, ENNReal.ofReal (h x) * (truncV g L x) ^ ε := by
  have hd0 : 0 < d := by omega
  have hθ := gehringTheta_pos hd0
  have hθ1 := gehringTheta_lt_one d
  have hc0 := gehringC_pos d
  set c := gehringC d with hcdef
  set θ := gehringTheta d with hθdef
  set b := 1 - θ + ε with hb
  have hA0 : 0 ≤ A := by linarith
  -- the three layer identities
  have hI : truncMoment g L ε =
      ∫⁻ t in Ioo 0 L, ENNReal.ofReal (ε * t ^ (ε - 1)) * ∫⁻ x in {x | t < g x},
        ENNReal.ofReal (g x) := by
    have := lintegral_layer (Φ := fun x => ENNReal.ofReal (g x))
      (w := fun x => ENNReal.ofReal (g x))
      (ENNReal.measurable_ofReal.comp hgm).aemeasurable
      (ENNReal.measurable_ofReal.comp hgm).aemeasurable hε hL
    unfold truncMoment
    rw [← this]
    refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    have hset : {x | ENNReal.ofReal t < ENNReal.ofReal (g x)} = {x | t < g x} := by
      ext x
      show ENNReal.ofReal t < ENNReal.ofReal (g x) ↔ t < g x
      rw [ENNReal.ofReal_lt_ofReal_iff']
      exact ⟨fun h => h.1, fun h => ⟨h, ht.1.trans h⟩⟩
    rw [hset]
  have hVm : Measurable (gehringV g) := by
    have hlsc : LowerSemicontinuous (cubeMaximal fun y => g y ^ gehringTheta d) :=
      lowerSemicontinuous_iff_isOpen_preimage.2 fun s => isOpen_lt_cubeMaximal _ s
    exact hlsc.measurable.pow_const _
  have hH : ∫⁻ t in Ioo 0 L, ENNReal.ofReal (ε * t ^ (ε - 1)) *
      ∫⁻ x in gehringE g t, ENNReal.ofReal (h x) =
      ∫⁻ x, ENNReal.ofReal (h x) * (truncV g L x) ^ ε :=
    lintegral_layer (Φ := gehringV g) (w := fun x => ENNReal.ofReal (h x)) hVm.aemeasurable
      (ENNReal.measurable_ofReal.comp_aemeasurable hh.aestronglyMeasurable.aemeasurable) hε hL
  have hSg : MeasurableSet {q : ℝ × Vec d | c * q.1 < g q.2} :=
    measurableSet_lt (measurable_fst.const_mul c) (hgm.comp measurable_snd)
  have hw : Measurable fun y => ENNReal.ofReal (g y ^ θ) :=
    ENNReal.measurable_ofReal.comp (hgm.pow_const _)
  have hJm : Measurable fun t : ℝ => ∫⁻ y in {y | c * t < g y}, ENNReal.ofReal (g y ^ θ) :=
    measurable_lintegral_slice hSg hw
  have hκ : Measurable fun t : ℝ => ENNReal.ofReal (t ^ (ε - θ)) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
  have hpt : ∀ t ∈ Ioo (0 : ℝ) L, ENNReal.ofReal (ε * t ^ (ε - 1)) *
      ∫⁻ x in {x | t < g x}, ENNReal.ofReal (g x) ≤
      ENNReal.ofReal (ε * gehringD d * A) * (ENNReal.ofReal (t ^ (ε - θ)) *
        ∫⁻ y in {y | c * t < g y}, ENNReal.ofReal (g y ^ θ)) +
      ENNReal.ofReal (B * gehringN σ d) * (ENNReal.ofReal (ε * t ^ (ε - 1)) *
        ∫⁻ x in gehringE g t, ENNReal.ofReal (h x)) := by
    intro t ht
    have htail := tail_global hd0 hg0 hh0 hg hc hh hσ hA0 hB ht.1 hrh
    have key : ENNReal.ofReal (ε * t ^ (ε - 1)) * ENNReal.ofReal (gehringD d * A * t ^ (1 - θ)) =
        ENNReal.ofReal (ε * gehringD d * A) * ENNReal.ofReal (t ^ (ε - θ)) := by
      have hD := gehringD_pos d
      rw [← ENNReal.ofReal_mul (by have := ht.1; positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have : t ^ (ε - θ) = t ^ (ε - 1) * t ^ (1 - θ) := by
        rw [← Real.rpow_add ht.1]; congr 1; ring
      rw [this]; ring
    calc ENNReal.ofReal (ε * t ^ (ε - 1)) * ∫⁻ x in {x | t < g x}, ENNReal.ofReal (g x)
        ≤ ENNReal.ofReal (ε * t ^ (ε - 1)) *
          (ENNReal.ofReal (gehringD d * A * t ^ (1 - θ)) *
            (∫⁻ y in {y | c * t < g y}, ENNReal.ofReal (g y ^ θ)) +
          ENNReal.ofReal (B * gehringN σ d) * ∫⁻ x in gehringE g t, ENNReal.ofReal (h x)) := by
          gcongr
      _ = (ENNReal.ofReal (ε * t ^ (ε - 1)) * ENNReal.ofReal (gehringD d * A * t ^ (1 - θ))) *
            (∫⁻ y in {y | c * t < g y}, ENNReal.ofReal (g y ^ θ)) +
          ENNReal.ofReal (B * gehringN σ d) * (ENNReal.ofReal (ε * t ^ (ε - 1)) *
            ∫⁻ x in gehringE g t, ENNReal.ofReal (h x)) := by ring
      _ = _ := by rw [key]; ring
  have hcore := core_bound hd0 hg0 hgm hε hL
  have hβ := beta_le hd hA hε hεA
  calc truncMoment g L ε
      = ∫⁻ t in Ioo 0 L, ENNReal.ofReal (ε * t ^ (ε - 1)) * ∫⁻ x in {x | t < g x},
        ENNReal.ofReal (g x) := hI
    _ ≤ ∫⁻ t in Ioo 0 L, (ENNReal.ofReal (ε * gehringD d * A) * (ENNReal.ofReal (t ^ (ε - θ)) *
        ∫⁻ y in {y | c * t < g y}, ENNReal.ofReal (g y ^ θ)) +
      ENNReal.ofReal (B * gehringN σ d) * (ENNReal.ofReal (ε * t ^ (ε - 1)) *
        ∫⁻ x in gehringE g t, ENNReal.ofReal (h x))) := setLIntegral_mono' measurableSet_Ioo hpt
    _ = ENNReal.ofReal (ε * gehringD d * A) * (∫⁻ t in Ioo 0 L, (ENNReal.ofReal (t ^ (ε - θ)) *
        ∫⁻ y in {y | c * t < g y}, ENNReal.ofReal (g y ^ θ))) +
      ENNReal.ofReal (B * gehringN σ d) * ∫⁻ t in Ioo 0 L, (ENNReal.ofReal (ε * t ^ (ε - 1)) *
        ∫⁻ x in gehringE g t, ENNReal.ofReal (h x)) := by
        rw [lintegral_add_left, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact (measurable_const.mul (hκ.mul hJm))
    _ ≤ ENNReal.ofReal (ε * gehringD d * A) * (ENNReal.ofReal (c ^ (-b) / b) *
        truncMoment g L ε) +
      ENNReal.ofReal (B * gehringN σ d) * ∫⁻ x, ENNReal.ofReal (h x) * (truncV g L x) ^ ε := by
        rw [hH]
        gcongr
    _ = ENNReal.ofReal (ε * gehringD d * A * (c ^ (-b) / b)) * truncMoment g L ε +
      ENNReal.ofReal (B * gehringN σ d) * ∫⁻ x, ENNReal.ofReal (h x) * (truncV g L x) ^ ε := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by have := gehringD_pos d; positivity)]
    _ ≤ _ := by
        gcongr

end PDE.Gehring
