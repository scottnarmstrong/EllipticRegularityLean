module

public import PDEFoundation.Analysis.Gehring.LocalTail
public import PDEFoundation.Analysis.Gehring.Global

/-!
# The localized truncated absorption (Lemma 4.6)

For `g` vanishing outside `B_R`, with `I_L(D) = ∫_D g min(g,L)^ε`:
`I_L(B_ρ) ≤ T^ε ∫ g + (1/8) I_L(B_R) + B N_σ ∫ h V_L^ε`, `T = T_{ρ,R}`.
-/

@[expose] public section

namespace PDE.Gehring

open MeasureTheory Set
open scoped ENNReal

variable {d : ℕ}

open Classical in
/-- **Localized truncated absorption.** Layer-cake integration of `local_tail` over the levels
`t ∈ (0, L)`, the levels `t < T_{ρ,R}` being bounded trivially. -/
theorem local_truncated (hd : 2 ≤ d) {g h : Vec d → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (hh0 : ∀ x, 0 ≤ h x) (hgm : Measurable g) (hg : Integrable g volume)
    (hc : HasCompactSupport g) (hh : LocallyIntegrable h volume)
    {σ A B ρ R m ε L : ℝ} (hσ : σ = 2 ∨ σ = 4) (hA : 1 ≤ A) (hB : 0 ≤ B) (hε : 0 < ε)
    (hεA : ε ≤ 1 / (8 * gehringG d * A)) (hL : 0 < L) (hρ : 0 < ρ) (hρR : ρ < R) (hR : R ≤ 1)
    (hsupp : ∀ x, x ∉ euclideanBall (0 : Vec d) R → g x = 0)
    (hm : 0 < m) (hmg : integralAverage (euclideanBall (0 : Vec d) 1) g ≤ m)
    (hrh : ∀ (z : Vec d) (r : ℝ), 0 < r → centeredAxisCube z (σ * r) ⊆ euclideanBall (0 : Vec d) R →
      GehringRH d σ A B g h z r) :
    ∫⁻ x in euclideanBall (0 : Vec d) ρ,
        ENNReal.ofReal (g x) * (min (ENNReal.ofReal (g x)) (ENNReal.ofReal L)) ^ ε ≤
      ENNReal.ofReal (((3 * Real.sqrt d / (R - ρ)) ^ (d + 1) * m) ^ ε) *
          (∫⁻ x, ENNReal.ofReal (g x)) +
        ENNReal.ofReal (1 / 8) * truncMoment g L ε +
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
  set Bρ := euclideanBall (0 : Vec d) ρ with hBρ
  have hBρm : MeasurableSet Bρ := (isOpen_euclideanBall _ _).measurableSet
  set T : ℝ := (3 * Real.sqrt d / (R - ρ)) ^ (d + 1) * m with hTdef
  have hδ : 0 < R - ρ := by linarith
  have hdR : (0 : ℝ) < d := Nat.cast_pos.2 hd0
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 hdR
  have hTpos : 0 < T := by rw [hTdef]; positivity
  set M : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (g x) with hMdef
  -- layer identity for the restricted moment
  have hwm : Measurable (Bρ.indicator fun x => ENNReal.ofReal (g x)) :=
    (ENNReal.measurable_ofReal.comp hgm).indicator hBρm
  have hlay := lintegral_layer (Φ := fun x => ENNReal.ofReal (g x))
    (w := Bρ.indicator fun x => ENNReal.ofReal (g x))
    (ENNReal.measurable_ofReal.comp hgm).aemeasurable hwm.aemeasurable hε hL
  have hLHS : ∫⁻ x, (Bρ.indicator fun x => ENNReal.ofReal (g x)) x *
      (min (ENNReal.ofReal (g x)) (ENNReal.ofReal L)) ^ ε =
      ∫⁻ x in Bρ, ENNReal.ofReal (g x) * (min (ENNReal.ofReal (g x)) (ENNReal.ofReal L)) ^ ε := by
    rw [← lintegral_indicator hBρm]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ Bρ <;> simp [hx]
  rw [← hLHS, ← hlay]
  have hinner : ∀ t ∈ Ioo (0 : ℝ) L, ∫⁻ x in {x | ENNReal.ofReal t < ENNReal.ofReal (g x)},
      (Bρ.indicator fun x => ENNReal.ofReal (g x)) x =
      ∫⁻ x in {x | t < g x} ∩ Bρ, ENNReal.ofReal (g x) := by
    intro t ht
    have hset : {x | ENNReal.ofReal t < ENNReal.ofReal (g x)} = {x | t < g x} := by
      ext x
      show ENNReal.ofReal t < ENNReal.ofReal (g x) ↔ t < g x
      rw [ENNReal.ofReal_lt_ofReal_iff']
      exact ⟨fun h => h.1, fun h => ⟨h, ht.1.trans h⟩⟩
    rw [hset, lintegral_indicator hBρm, Measure.restrict_restrict hBρm, inter_comm]
  -- the pieces
  have hVm := measurable_gehringV g
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
  have hpt : ∀ t ∈ Ioo (0 : ℝ) L,
      ENNReal.ofReal (ε * t ^ (ε - 1)) * ∫⁻ x in {x | t < g x} ∩ Bρ, ENNReal.ofReal (g x) ≤
      (Iio T).indicator (fun t : ℝ => ENNReal.ofReal (ε * t ^ (ε - 1)) * M) t +
        (ENNReal.ofReal (ε * gehringD d * A) * (ENNReal.ofReal (t ^ (ε - θ)) *
          ∫⁻ y in {y | c * t < g y}, ENNReal.ofReal (g y ^ θ)) +
        ENNReal.ofReal (B * gehringN σ d) * (ENNReal.ofReal (ε * t ^ (ε - 1)) *
          ∫⁻ x in gehringE g t, ENNReal.ofReal (h x))) := by
    intro t ht
    by_cases hTt : t < T
    · rw [Set.indicator_of_mem (show t ∈ Iio T from hTt)]
      refine le_trans ?_ le_self_add
      gcongr
      exact setLIntegral_le_lintegral _ _
    · rw [Set.indicator_of_notMem (show t ∉ Iio T from hTt), zero_add]
      have htail := local_tail hd0 hg0 hh0 hg hc hh hσ hA0 hB hρ hρR hR hsupp hm hmg
        (not_lt.1 hTt) hrh
      have key : ENNReal.ofReal (ε * t ^ (ε - 1)) *
          ENNReal.ofReal (gehringD d * A * t ^ (1 - θ)) =
          ENNReal.ofReal (ε * gehringD d * A) * ENNReal.ofReal (t ^ (ε - θ)) := by
        have hD := gehringD_pos d
        rw [← ENNReal.ofReal_mul (by have := ht.1; positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have : t ^ (ε - θ) = t ^ (ε - 1) * t ^ (1 - θ) := by
          rw [← Real.rpow_add ht.1]; congr 1; ring
        rw [this]; ring
      calc ENNReal.ofReal (ε * t ^ (ε - 1)) * ∫⁻ x in {x | t < g x} ∩ Bρ, ENNReal.ofReal (g x)
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
  have hind : ∫⁻ t in Ioo 0 L, (Iio T).indicator
      (fun t : ℝ => ENNReal.ofReal (ε * t ^ (ε - 1)) * M) t ≤ ENNReal.ofReal (T ^ ε) * M := by
    have hm1 : Measurable fun t : ℝ => ENNReal.ofReal (ε * t ^ (ε - 1)) * M :=
      (ENNReal.measurable_ofReal.comp (measurable_const.mul
        (measurable_id.pow_const _))).mul_const _
    rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
    calc ∫⁻ t in Iio T ∩ Ioo 0 L, ENNReal.ofReal (ε * t ^ (ε - 1)) * M
        ≤ ∫⁻ t in Ioo 0 T, ENNReal.ofReal (ε * t ^ (ε - 1)) * M := by
          refine lintegral_mono_set ?_
          intro t ht
          exact ⟨ht.2.1, ht.1⟩
      _ = ENNReal.ofReal (T ^ ε) * M := by
          have hpe : ∀ t : ℝ, ENNReal.ofReal (ε * t ^ (ε - 1)) =
              ENNReal.ofReal ε * ENNReal.ofReal (t ^ (ε - 1)) := fun t =>
            ENNReal.ofReal_mul hε.le
          simp_rw [hpe]
          have hfm : Measurable fun t : ℝ => ENNReal.ofReal ε * ENNReal.ofReal (t ^ (ε - 1)) :=
            measurable_const.mul (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _))
          rw [lintegral_mul_const M hfm]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_Ioo_rpow (by linarith) hTpos.le, ← ENNReal.ofReal_mul hε.le,
            show ε - 1 + 1 = ε by ring, mul_div_cancel₀ _ hε.ne']
  calc ∫⁻ t in Ioo 0 L, ENNReal.ofReal (ε * t ^ (ε - 1)) *
        ∫⁻ x in {x | ENNReal.ofReal t < ENNReal.ofReal (g x)},
          (Bρ.indicator fun x => ENNReal.ofReal (g x)) x
      = ∫⁻ t in Ioo 0 L, ENNReal.ofReal (ε * t ^ (ε - 1)) *
          ∫⁻ x in {x | t < g x} ∩ Bρ, ENNReal.ofReal (g x) := by
        refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
        rw [hinner t ht]
    _ ≤ ∫⁻ t in Ioo 0 L, ((Iio T).indicator
          (fun t : ℝ => ENNReal.ofReal (ε * t ^ (ε - 1)) * M) t +
        (ENNReal.ofReal (ε * gehringD d * A) * (ENNReal.ofReal (t ^ (ε - θ)) *
          ∫⁻ y in {y | c * t < g y}, ENNReal.ofReal (g y ^ θ)) +
        ENNReal.ofReal (B * gehringN σ d) * (ENNReal.ofReal (ε * t ^ (ε - 1)) *
          ∫⁻ x in gehringE g t, ENNReal.ofReal (h x)))) := setLIntegral_mono' measurableSet_Ioo hpt
    _ = (∫⁻ t in Ioo 0 L, (Iio T).indicator
          (fun t : ℝ => ENNReal.ofReal (ε * t ^ (ε - 1)) * M) t) +
        (ENNReal.ofReal (ε * gehringD d * A) * (∫⁻ t in Ioo 0 L, (ENNReal.ofReal (t ^ (ε - θ)) *
          ∫⁻ y in {y | c * t < g y}, ENNReal.ofReal (g y ^ θ))) +
        ENNReal.ofReal (B * gehringN σ d) * (∫⁻ t in Ioo 0 L, (ENNReal.ofReal (ε * t ^ (ε - 1)) *
          ∫⁻ x in gehringE g t, ENNReal.ofReal (h x)))) := by
        have hm1 : Measurable fun t : ℝ => (Iio T).indicator
            (fun t : ℝ => ENNReal.ofReal (ε * t ^ (ε - 1)) * M) t :=
          ((ENNReal.measurable_ofReal.comp (measurable_const.mul
            (measurable_id.pow_const _))).mul_const _).indicator measurableSet_Iio
        have hm2 : Measurable fun t : ℝ => ENNReal.ofReal (ε * gehringD d * A) *
            (ENNReal.ofReal (t ^ (ε - θ)) *
              ∫⁻ y in {y | c * t < g y}, ENNReal.ofReal (g y ^ θ)) :=
          measurable_const.mul (hκ.mul hJm)
        rw [lintegral_add_left hm1, lintegral_add_left hm2,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (T ^ ε) * M + (ENNReal.ofReal (ε * gehringD d * A) *
          (ENNReal.ofReal (c ^ (-b) / b) * truncMoment g L ε) +
        ENNReal.ofReal (B * gehringN σ d) * ∫⁻ x, ENNReal.ofReal (h x) * (truncV g L x) ^ ε) := by
        rw [hH]
        gcongr
    _ = ENNReal.ofReal (T ^ ε) * M +
          ENNReal.ofReal (ε * gehringD d * A * (c ^ (-b) / b)) * truncMoment g L ε +
        ENNReal.ofReal (B * gehringN σ d) * ∫⁻ x, ENNReal.ofReal (h x) * (truncV g L x) ^ ε := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by have := gehringD_pos d; positivity), add_assoc]
    _ ≤ _ := by
        gcongr

end PDE.Gehring
