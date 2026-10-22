/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.WeakSlice.DuBoisReymond
public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.Convex.Measure

/-! # Smooth ramps at Lebesgue points

The smooth ramps `ε⁻¹ ρ((τ - (b + κ ε))/ε)` of `WeakSlice.Ramp` approximate a Dirac mass at `b`
when tested against a function having `b` as a Lebesgue point (in the strong sense along windows of
length `ε` shifted by `κ ε`). This replaces the continuity assumption of `tendsto_ramp_avg`.
-/

@[expose] public section

namespace PDE.Parabolic.Chain.Super

open MeasureTheory Set Filter Topology PDE.Parabolic.WeakSlice

/-- `b` is a strong Lebesgue point of `m`, along windows `[b + κ ε, b + κ ε + ε]` with `|κ| ≤ 2`. -/
def IsLebPt (m : ℝ → ℝ) (b : ℝ) : Prop :=
  ∀ κ : ℝ, |κ| ≤ 2 →
    Tendsto (fun ε : ℝ => ε⁻¹ * ∫ τ in Icc (b + κ * ε) (b + κ * ε + ε), |m τ - m b|)
      (𝓝[>] 0) (𝓝 0)

/-- Almost every point is a strong Lebesgue point of a locally integrable function. -/
theorem ae_isLebPt {m : ℝ → ℝ} (hm : LocallyIntegrable m volume) :
    ∀ᵐ b, IsLebPt m b := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume hm 6] with b hb
  intro κ hκ
  have hδ : Tendsto (fun ε : ℝ => ε / 2) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun ε : ℝ => ε / 2) (𝓝 0) (𝓝 (0 / 2)) :=
        (continuous_id.div_const 2).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε using half_pos (show (0 : ℝ) < ε from hε)
  have hmem : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      b ∈ Metric.closedBall (b + (κ + 1 / 2) * ε) (6 * (ε / 2)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    rw [Metric.mem_closedBall, Real.dist_eq]
    have h1 : |κ + 1 / 2| ≤ 5 / 2 := by
      calc |κ + 1 / 2| ≤ |κ| + |(1 / 2 : ℝ)| := abs_add_le _ _
        _ ≤ 5 / 2 := by rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; linarith
    have : b - (b + (κ + 1 / 2) * ε) = -((κ + 1 / 2) * ε) := by ring
    rw [this, abs_neg, abs_mul, abs_of_pos hε']
    nlinarith [abs_nonneg (κ + 1 / 2)]
  have h := hb (ι := ℝ) (l := 𝓝[>] 0) (fun ε => b + (κ + 1 / 2) * ε) (fun ε => ε / 2) hδ hmem
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : 0 < ε := hε
  have hball : Metric.closedBall (b + (κ + 1 / 2) * ε) (ε / 2) =
      Icc (b + κ * ε) (b + κ * ε + ε) := by
    rw [Real.closedBall_eq_Icc]
    congr 1 <;> ring
  rw [hball, setAverage_eq, Real.volume_real_Icc_of_le (by linarith)]
  simp only [Real.norm_eq_abs, smul_eq_mul]
  congr 1
  · congr 1; ring

theorem integral_ramp_scaled {ε : ℝ} (hε : 0 < ε) (c : ℝ) :
    ∫ τ, ε⁻¹ * rampDeriv ((τ - c) / ε) = 1 := by
  rw [← integral_add_left_eq_self (fun τ => ε⁻¹ * rampDeriv ((τ - c) / ε)) c]
  simp only [add_sub_cancel_left]
  rw [integral_const_mul]
  have h : ∫ x : ℝ, rampDeriv (ε⁻¹ * x) = ε := by
    rw [Measure.integral_comp_mul_left (fun y => rampDeriv y) ε⁻¹]
    simp [integral_rampDeriv, abs_of_pos hε]
  have h2 : (fun x : ℝ => rampDeriv (x / ε)) = fun x => rampDeriv (ε⁻¹ * x) := by
    ext x; simp [div_eq_inv_mul]
  rw [h2, h]
  field_simp

theorem exists_abs_rampDeriv_le : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |rampDeriv x| ≤ M := by
  have hcs : HasCompactSupport rampDeriv :=
    HasCompactSupport.of_support_subset_isCompact (K := Icc (0 : ℝ) 1) isCompact_Icc
      fun x hx => by
        by_contra h
        exact hx (rampDeriv_eq_zero_of_notMem h)
  obtain ⟨M, hM⟩ := rampDeriv_continuous.bounded_above_of_compact_support hcs
  exact ⟨M, (norm_nonneg _).trans (hM 0), fun x => by simpa [Real.norm_eq_abs] using hM x⟩

theorem ramp_eq_zero_of_notMem {ε : ℝ} (hε : 0 < ε) {c τ : ℝ} (hτ : τ ∉ Icc c (c + ε)) :
    rampDeriv ((τ - c) / ε) = 0 := by
  refine rampDeriv_eq_zero_of_notMem ?_
  intro hh
  apply hτ
  refine ⟨?_, ?_⟩
  · have := hh.1; rw [le_div_iff₀ hε] at this; linarith
  · have := hh.2; rw [div_le_iff₀ hε] at this; linarith

theorem continuous_ramp (ε c : ℝ) :
    Continuous fun τ : ℝ => ε⁻¹ * rampDeriv ((τ - c) / ε) :=
  continuous_const.mul (rampDeriv_continuous.comp ((continuous_id.sub continuous_const).div_const ε))

theorem integrable_mul_ramp {m : ℝ → ℝ} {A B ε c : ℝ} (hε : 0 < ε)
    (hm : IntegrableOn m (Icc A B)) (hwin : Icc c (c + ε) ⊆ Icc A B) :
    Integrable fun τ => m τ * (ε⁻¹ * rampDeriv ((τ - c) / ε)) := by
  have h2 := (hm.mono_set hwin).mul_continuousOn (continuous_ramp ε c).continuousOn
    isCompact_Icc
  refine h2.integrable_of_forall_notMem_eq_zero fun τ hτ => ?_
  simp [ramp_eq_zero_of_notMem hε hτ]

/-- The smooth ramp at a strong Lebesgue point tends to evaluation. -/
theorem tendsto_ramp_of_isLebPt {m : ℝ → ℝ} {b : ℝ} (hb : IsLebPt m b) {r : ℝ} (hr : 0 < r)
    (hint : IntegrableOn m (Icc (b - r) (b + r))) {κ : ℝ} (hκ : |κ| ≤ 2) :
    Tendsto (fun ε : ℝ => ∫ τ, m τ * (ε⁻¹ * rampDeriv ((τ - (b + κ * ε)) / ε)))
      (𝓝[>] 0) (𝓝 (m b)) := by
  obtain ⟨M, hM0, hM⟩ := exists_abs_rampDeriv_le
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε ≤ r / 3 := by
    filter_upwards [Ioc_mem_nhdsGT (by linarith : (0 : ℝ) < r / 3)] with ε hε using hε
  set E : ℝ → ℝ := fun ε => ∫ τ, (m τ - m b) * (ε⁻¹ * rampDeriv ((τ - (b + κ * ε)) / ε))
    with hE
  have hwin : ∀ ε : ℝ, 0 < ε → ε ≤ r / 3 →
      Icc (b + κ * ε) (b + κ * ε + ε) ⊆ Icc (b - r) (b + r) := by
    intro ε hε hεr τ hτ
    have h1 : |κ * ε| ≤ 2 * ε := by
      rw [abs_mul, abs_of_pos hε]; exact mul_le_mul_of_nonneg_right hκ hε.le
    have h2 := abs_le.1 h1
    constructor <;> linarith [hτ.1, hτ.2, h2.1, h2.2]
  have hmwint : ∀ ε : ℝ, 0 < ε → ε ≤ r / 3 →
      Integrable fun τ => (m τ - m b) * (ε⁻¹ * rampDeriv ((τ - (b + κ * ε)) / ε)) := by
    intro ε hε hεr
    have h1 : IntegrableOn (fun τ => m τ - m b) (Icc (b + κ * ε) (b + κ * ε + ε)) :=
      (hint.mono_set (hwin ε hε hεr)).sub (integrableOn_const (by simp))
    have h2 := h1.mul_continuousOn (continuous_ramp ε (b + κ * ε)).continuousOn isCompact_Icc
    refine h2.integrable_of_forall_notMem_eq_zero fun τ hτ => ?_
    simp [ramp_eq_zero_of_notMem hε hτ]
  have hE0 : Tendsto E (𝓝[>] 0) (𝓝 0) := by
    have hbound : Tendsto (fun ε : ℝ => M * (ε⁻¹ *
        ∫ τ in Icc (b + κ * ε) (b + κ * ε + ε), |m τ - m b|)) (𝓝[>] 0) (𝓝 (M * 0)) :=
      (hb κ hκ).const_mul M
    rw [mul_zero] at hbound
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hev] with ε ⟨hε, hεr⟩
    set c := b + κ * ε with hc
    have hmint : IntegrableOn (fun τ => |m τ - m b|) (Icc c (c + ε)) :=
      ((hint.mono_set (hwin ε hε hεr)).sub (integrableOn_const (by simp))).abs
    have hmajor : Integrable ((Icc c (c + ε)).indicator
        (fun τ => M * ε⁻¹ * |m τ - m b|)) :=
      (integrable_indicator_iff measurableSet_Icc).2 (hmint.const_mul _)
    calc ‖E ε‖ ≤ ∫ τ, (Icc c (c + ε)).indicator (fun τ => M * ε⁻¹ * |m τ - m b|) τ := by
          refine norm_integral_le_of_norm_le hmajor (Eventually.of_forall fun τ => ?_)
          by_cases hτ : τ ∈ Icc c (c + ε)
          · rw [indicator_of_mem hτ, Real.norm_eq_abs, abs_mul, abs_mul,
              abs_of_pos (inv_pos.2 hε)]
            calc |m τ - m b| * (ε⁻¹ * |rampDeriv ((τ - c) / ε)|)
                ≤ |m τ - m b| * (ε⁻¹ * M) :=
                  mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_left (hM _) (inv_pos.2 hε).le) (abs_nonneg _)
              _ = M * ε⁻¹ * |m τ - m b| := by ring
          · rw [indicator_of_notMem hτ]
            have h0 : rampDeriv ((τ - (b + κ * ε)) / ε) = 0 := ramp_eq_zero_of_notMem hε hτ
            simp [h0]
      _ = M * (ε⁻¹ * ∫ τ in Icc c (c + ε), |m τ - m b|) := by
          rw [integral_indicator measurableSet_Icc, integral_const_mul]
          ring
  have heq : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ∫ τ, m τ * (ε⁻¹ * rampDeriv ((τ - (b + κ * ε)) / ε)) = m b + E ε := by
    filter_upwards [hev] with ε ⟨hε, hεr⟩
    have hw1 : Integrable fun τ : ℝ => ε⁻¹ * rampDeriv ((τ - (b + κ * ε)) / ε) := by
      refine (continuous_ramp ε (b + κ * ε)).integrable_of_hasCompactSupport ?_
      refine HasCompactSupport.of_support_subset_isCompact (K := Icc (b + κ * ε) (b + κ * ε + ε))
        isCompact_Icc fun τ hτ => ?_
      by_contra h
      exact hτ (by simp [ramp_eq_zero_of_notMem hε h])
    have hsplit : (fun τ => m τ * (ε⁻¹ * rampDeriv ((τ - (b + κ * ε)) / ε))) =
        fun τ => (m τ - m b) * (ε⁻¹ * rampDeriv ((τ - (b + κ * ε)) / ε)) +
          m b * (ε⁻¹ * rampDeriv ((τ - (b + κ * ε)) / ε)) := by
      ext τ; ring
    rw [hsplit, integral_add (hmwint ε hε hεr) (hw1.const_mul _), integral_const_mul,
      integral_ramp_scaled hε]
    simp only [hE]
    ring
  have := (tendsto_const_nhds (x := m b)).add hE0
  rw [add_zero] at this
  exact this.congr' (heq.mono fun ε h => h.symm)

theorem isLebPt_of_indicator {m : ℝ → ℝ} {p q b : ℝ} (hp : p < b) (hq : b < q)
    (h : IsLebPt ((Icc p q).indicator m) b) : IsLebPt m b := by
  intro κ hκ
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ 3 * ε ≤ min (b - p) (q - b) := by
    have hpos : 0 < min (b - p) (q - b) / 3 :=
      by have := lt_min (sub_pos.2 hp) (sub_pos.2 hq); linarith
    filter_upwards [Ioc_mem_nhdsGT hpos] with ε hε
    exact ⟨hε.1, by linarith [hε.2]⟩
  refine (h κ hκ).congr' ?_
  filter_upwards [hev] with ε ⟨hε, hε3⟩
  have h1 := (le_min_iff.1 hε3).1
  have h2 := (le_min_iff.1 hε3).2
  have hk : |κ * ε| ≤ 2 * ε := by
    rw [abs_mul, abs_of_pos hε]; exact mul_le_mul_of_nonneg_right hκ hε.le
  have hk' := abs_le.1 hk
  have hsub : Icc (b + κ * ε) (b + κ * ε + ε) ⊆ Icc p q := by
    intro τ hτ
    constructor <;> linarith [hτ.1, hτ.2, hk'.1, hk'.2]
  have hbmem : b ∈ Icc p q := ⟨hp.le, hq.le⟩
  congr 1
  refine setIntegral_congr_fun measurableSet_Icc fun τ hτ => ?_
  simp only [indicator_of_mem (hsub hτ), indicator_of_mem hbmem]

/-- A function integrable on compact subintervals of an interval `I` has a strong Lebesgue point at
almost every point of `I` (and is integrable on a neighbourhood of each of its interior points). -/
theorem exists_null_set_isLebPt {I : Set ℝ} (hI : I.OrdConnected) {m : ℝ → ℝ}
    (hm : ∀ p ∈ I, ∀ q ∈ I, IntegrableOn m (Icc p q)) :
    ∃ N : Set ℝ, volume N = 0 ∧ ∀ b ∈ I, b ∉ N →
      IsLebPt m b ∧ ∃ r : ℝ, 0 < r ∧ IntegrableOn m (Icc (b - r) (b + r)) := by
  let P : ℚ × ℚ → Prop := fun pq => ((pq.1 : ℝ) < pq.2) ∧ Icc (pq.1 : ℝ) pq.2 ⊆ I
  let g : ℚ × ℚ → ℝ → ℝ := fun pq => (Icc (pq.1 : ℝ) pq.2).indicator m
  have hg : ∀ pq, P pq → LocallyIntegrable (g pq) volume := by
    intro pq hpq
    have hp : (pq.1 : ℝ) ∈ I := hpq.2 ⟨le_rfl, hpq.1.le⟩
    have hq : (pq.2 : ℝ) ∈ I := hpq.2 ⟨hpq.1.le, le_rfl⟩
    exact ((integrable_indicator_iff measurableSet_Icc).2 (hm _ hp _ hq)).locallyIntegrable
  have hae : ∀ pq : ℚ × ℚ, ∀ᵐ b : ℝ, P pq → IsLebPt (g pq) b := by
    intro pq
    by_cases hpq : P pq
    · filter_upwards [ae_isLebPt (hg pq hpq)] with b hb _ using hb
    · exact Eventually.of_forall fun b h => absurd h hpq
  have hall := ae_all_iff.2 hae
  have hN0 : volume {b : ℝ | ¬ ∀ pq : ℚ × ℚ, P pq → IsLebPt (g pq) b} = 0 := ae_iff.1 hall
  have hconv : Convex ℝ I := hI.convex
  have hfr : volume (I \ interior I) = 0 :=
    measure_mono_null (fun x hx => (show x ∈ frontier I from ⟨subset_closure hx.1, hx.2⟩))
      (Convex.addHaar_frontier volume hconv)
  refine ⟨{b : ℝ | ¬ ∀ pq : ℚ × ℚ, P pq → IsLebPt (g pq) b} ∪ (I \ interior I),
    measure_union_null hN0 hfr, ?_⟩
  intro b hbI hbN
  have hbint : b ∈ interior I := by
    by_contra h; exact hbN (Or.inr ⟨hbI, h⟩)
  have hbN0 : ∀ pq : ℚ × ℚ, P pq → IsLebPt (g pq) b := by
    by_contra h; exact hbN (Or.inl h)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior b hbint
  obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show b - ε < b by linarith)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show b < b + ε by linarith)
  have hPpq : P (p, q) := by
    refine ⟨hp2.trans hq1, fun τ hτ => interior_subset (hball ?_)⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hτ.1, hτ.2]
  have hlp : IsLebPt m b := isLebPt_of_indicator hp2 hq1 (hbN0 (p, q) hPpq)
  refine ⟨hlp, min (b - p) (q - b), lt_min (sub_pos.2 hp2) (sub_pos.2 hq1), ?_⟩
  have hpI : (p : ℝ) ∈ I := hPpq.2 ⟨le_rfl, hPpq.1.le⟩
  have hqI : (q : ℝ) ∈ I := hPpq.2 ⟨hPpq.1.le, le_rfl⟩
  refine (hm _ hpI _ hqI).mono_set ?_
  intro τ hτ
  have h1 := min_le_left (b - (p : ℝ)) ((q : ℝ) - b)
  have h2 := min_le_right (b - (p : ℝ)) ((q : ℝ) - b)
  constructor <;> linarith [hτ.1, hτ.2]

end PDE.Parabolic.Chain.Super
