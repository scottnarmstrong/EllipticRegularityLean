/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.Energy.Limits
public import Mathlib.MeasureTheory.Function.UniformIntegrable

/-! # Weighted convergence in measure on finite cylinders -/

@[expose] public section

namespace PDE.Parabolic.Chain

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- Products of strongly `L²`-convergent sequences converge strongly in `L¹`. -/
theorem tendsto_eLpNorm_mul_sub_one_of_L2
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {F G : ℕ → X → ℝ} {F₀ G₀ : X → ℝ}
    (hF : ∀ n, MemLp (F n) 2 μ) (hG : ∀ n, MemLp (G n) 2 μ)
    (hF₀ : MemLp F₀ 2 μ) (hG₀ : MemLp G₀ 2 μ)
    (hFl : Tendsto (fun n => eLpNorm (F n - F₀) 2 μ) atTop (𝓝 0))
    (hGl : Tendsto (fun n => eLpNorm (G n - G₀) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm ((fun x => F n x * G n x) -
      (fun x => F₀ x * G₀ x)) 1 μ) atTop (𝓝 0) := by
  have hGclose : ∀ᶠ n in atTop, eLpNorm (G n - G₀) 2 μ ≤ 1 :=
    hGl.eventually (eventually_le_nhds (by norm_num))
  let M : ℝ≥0∞ := 1 + eLpNorm G₀ 2 μ
  have hMtop : M ≠ ∞ := ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hG₀.eLpNorm_lt_top.ne⟩
  have hGbound : ∀ᶠ n in atTop, eLpNorm (G n) 2 μ ≤ M := by
    filter_upwards [hGclose] with n hn
    have hadd : eLpNorm (G n) 2 μ ≤ eLpNorm (G n - G₀) 2 μ + eLpNorm G₀ 2 μ := by
      have heq : G n = (G n - G₀) + G₀ := by ext x; simp
      calc
        eLpNorm (G n) 2 μ = eLpNorm ((G n - G₀) + G₀) 2 μ :=
          congrArg (fun f => eLpNorm f 2 μ) heq
        _ ≤ eLpNorm (G n - G₀) 2 μ + eLpNorm G₀ 2 μ :=
          eLpNorm_add_le (f := G n - G₀) (g := G₀) (p := (2 : ℝ≥0∞)) (by norm_num)
    exact hadd.trans (by
      calc
        eLpNorm (G n - G₀) 2 μ + eLpNorm G₀ 2 μ =
            eLpNorm G₀ 2 μ + eLpNorm (G n - G₀) 2 μ := add_comm _ _
        _ ≤ eLpNorm G₀ 2 μ + 1 := add_le_add (le_rfl) hn
        _ = M := by simp [M, add_comm])
  have hfirst : Tendsto
      (fun n => eLpNorm (F n - F₀) 2 μ * eLpNorm (G n) 2 μ) atTop (𝓝 0) := by
    have hconst := ENNReal.Tendsto.const_mul hFl (Or.inr hMtop)
    have hconst' : Tendsto (fun n => M * eLpNorm (F n - F₀) 2 μ) atTop (𝓝 0) := by
      simpa using hconst
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hconst'
      (Eventually.of_forall fun n => by positivity) ?_
    filter_upwards [hGbound] with n hn
    calc
      eLpNorm (F n - F₀) 2 μ * eLpNorm (G n) 2 μ ≤
          eLpNorm (F n - F₀) 2 μ * M :=
        mul_le_mul_of_nonneg_left hn (by positivity)
      _ = M * eLpNorm (F n - F₀) 2 μ := mul_comm _ _
  have hsecond : Tendsto
      (fun n => eLpNorm F₀ 2 μ * eLpNorm (G n - G₀) 2 μ) atTop (𝓝 0) := by
    have hconst := ENNReal.Tendsto.const_mul hGl (Or.inr hF₀.eLpNorm_lt_top.ne)
    simpa using hconst
  have hsum : Tendsto
      (fun n => eLpNorm (F n - F₀) 2 μ * eLpNorm (G n) 2 μ +
        eLpNorm F₀ 2 μ * eLpNorm (G n - G₀) 2 μ) atTop (𝓝 0) := by
    simpa using hfirst.add hsecond
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun n => by positivity) ?_
  filter_upwards with n
  have hsplit : (fun x => F n x * G n x - F₀ x * G₀ x) =
      (fun x => (F n x - F₀ x) * G n x) + (fun x => F₀ x * (G n x - G₀ x)) := by
    funext x
    simp only [Pi.add_apply]
    ring
  have hsplitAE : ((fun x => F n x * G n x) - (fun x => F₀ x * G₀ x)) =ᵐ[μ]
      ((fun x => (F n x - F₀ x) * G n x) + (fun x => F₀ x * (G n x - G₀ x))) := by
    filter_upwards with x
    exact congrFun hsplit x
  change eLpNorm ((fun x => F n x * G n x) - (fun x => F₀ x * G₀ x)) 1 μ ≤ _
  rw [eLpNorm_congr_ae hsplitAE]
  have hadd : eLpNorm
      ((fun x => (F n x - F₀ x) * G n x) + (fun x => F₀ x * (G n x - G₀ x)))
      (1 : ℝ≥0∞) μ ≤
        eLpNorm (fun x => (F n x - F₀ x) * G n x) 1 μ +
          eLpNorm (fun x => F₀ x * (G n x - G₀ x)) 1 μ :=
    eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 1)
  refine hadd.trans (add_le_add ?_ ?_)
  · have hmul := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (p := (2 : ℝ≥0∞))
      (q := (2 : ℝ≥0∞)) (r := (1 : ℝ≥0∞))
      (fun x y : ℝ => x * y) 1 continuous_mul
      ((hF n).sub hF₀).aestronglyMeasurable (hG n).aestronglyMeasurable ?_
    · simpa using hmul
    · filter_upwards with x
      simp [Real.norm_eq_abs]
  · have hmul := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (p := (2 : ℝ≥0∞))
      (q := (2 : ℝ≥0∞)) (r := (1 : ℝ≥0∞))
      (fun x y : ℝ => x * y) 1 continuous_mul
      hF₀.aestronglyMeasurable ((hG n).sub hG₀).aestronglyMeasurable ?_
    · simpa using hmul
    · filter_upwards with x
      simp [Real.norm_eq_abs]

/-- A uniformly bounded coefficient converging to zero in measure can be
multiplied by a fixed integrable weight inside an integral. This is the
Vitali step needed for nonlinear coefficients multiplying products of two
`L²` fields. -/
theorem tendsto_integral_bounded_mul_of_tendstoInMeasure
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    (c : ℕ → X → ℝ) (w : X → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hcMeas : ∀ n, AEStronglyMeasurable (c n) μ)
    (hcBound : ∀ n, ∀ᵐ x ∂μ, |c n x| ≤ C)
    (hcZero : TendstoInMeasure μ c atTop 0) (hw : Integrable w μ) :
    Tendsto (fun n => ∫ x, c n x * w x ∂μ) atTop (𝓝 0) := by
  have hwC : Integrable (fun x => C * w x) μ := hw.const_mul C
  have hwCmem : MemLp (fun x => C * w x) 1 μ := memLp_one_iff_integrable.2 hwC
  have hconstant : UnifIntegrable (fun _ : ℕ => fun x => C * w x) 1 μ :=
    unifIntegrable_const (by norm_num) (by norm_num) hwCmem
  have hprodUI : UnifIntegrable (fun n x => c n x * w x) 1 μ := by
    apply hconstant.ae_mono (fun n => (hcMeas n).mul hw.aestronglyMeasurable)
    intro n
    filter_upwards [hcBound n] with x hx
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm, ENNReal.coe_le_coe]
    have hh : ‖c n x * w x‖ ≤ ‖C * w x‖ := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right hx (abs_nonneg (w x))
    exact_mod_cast hh
  have hprodMeas : TendstoInMeasure μ (fun n x => c n x * w x) atTop 0 := by
    apply (exists_seq_tendstoInMeasure_atTop_iff
      (fun n => (hcMeas n).mul hw.aestronglyMeasurable)).2
    intro ns hns
    obtain ⟨ms, hms, hcae⟩ := (hcZero.comp hns.tendsto_atTop).exists_seq_tendsto_ae
    refine ⟨ms, hms, ?_⟩
    filter_upwards [hcae] with x hx
    have hmul := hx.mul_const (w x)
    simpa using hmul
  have hL1 : Tendsto (fun n => eLpNorm ((fun x => c n x * w x) - 0) 1 μ) atTop
      (𝓝 0) :=
    (tendstoInMeasure_iff_tendsto_Lp_finite (by norm_num) ENNReal.one_ne_top
      (fun n => memLp_one_iff_integrable.2
        (hw.bdd_mul (hcMeas n) (c := C)
          ((hcBound n).mono (fun x hx => by
            simpa only [Real.norm_eq_abs] using hx))))
      (memLp_one_iff_integrable.2 (integrable_zero _ _ _))).mp
      ⟨hprodMeas, hprodUI⟩
  have hInt : ∀ n, Integrable (fun x => c n x * w x) μ :=
    fun n => hw.bdd_mul (hcMeas n) (c := C) ((hcBound n).mono (fun x hx => by
      simpa only [Real.norm_eq_abs] using hx))
  have hIntegral := tendsto_integral_of_L1' (f := (fun _ : X => (0 : ℝ)))
    (Eventually.of_forall hInt) hL1
  simpa using hIntegral

/-- A uniformly bounded multiplier preserves strong `L¹` convergence to zero
inside an integral. -/
theorem tendsto_integral_bounded_mul_of_tendsto_eLpNorm_one
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (c : ℕ → X → ℝ) (g : ℕ → X → ℝ) {C : ℝ} (_hC : 0 ≤ C)
    (hcMeas : ∀ n, AEStronglyMeasurable (c n) μ)
    (hcBound : ∀ n, ∀ᵐ x ∂μ, |c n x| ≤ C)
    (hg : ∀ n, Integrable (g n) μ)
    (hgl : Tendsto (fun n => eLpNorm (g n) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, c n x * g n x ∂μ) atTop (𝓝 0) := by
  have hprodLp : ∀ n, MemLp (fun x => c n x * g n x) 1 μ := by
    intro n
    exact memLp_one_iff_integrable.2 <| (hg n).bdd_mul (hcMeas n) (c := C)
      ((hcBound n).mono fun x hx => by simpa only [Real.norm_eq_abs] using hx)
  have hprodNorm : Tendsto
      (fun n => eLpNorm (fun x => c n x * g n x) 1 μ) atTop (𝓝 0) := by
    have hupper : Tendsto
        (fun n => ENNReal.ofReal C * eLpNorm (g n) 1 μ) atTop (𝓝 0) := by
      have hconst : Tendsto (fun n => ENNReal.ofReal C * eLpNorm (g n) 1 μ) atTop
          (𝓝 (ENNReal.ofReal C * 0)) :=
        ENNReal.Tendsto.const_mul hgl (Or.inr ENNReal.ofReal_ne_top)
      simpa using hconst
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
      (Eventually.of_forall fun _ => by positivity) ?_
    exact Eventually.of_forall fun n =>
      eLpNorm_le_mul_eLpNorm_of_ae_le_mul ((hcMeas n).mul (hg n).aestronglyMeasurable)
        ((hcBound n).mono fun x hx => by
          change |c n x * g n x| ≤ C * |g n x|
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right hx (abs_nonneg (g n x))) 1
  have hInt : ∀ n, Integrable (fun x => c n x * g n x) μ :=
    fun n => memLp_one_iff_integrable.1 (hprodLp n)
  have hL1 : Tendsto
      (fun n => eLpNorm ((fun x => c n x * g n x) - (fun _ : X => (0 : ℝ))) 1 μ)
      atTop (𝓝 0) := by
    convert hprodNorm using 1
    funext n
    congr 1
    funext x
    simp
  simpa using tendsto_integral_of_L1' (l := atTop) (f := (fun _ : X => (0 : ℝ)))
    (Eventually.of_forall hInt) hL1

/-- Multiplication by a fixed measurable function preserves convergence in
measure on a finite measure space. -/
theorem tendstoInMeasure_mul_fixed {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {f : ℕ → X → ℝ} {f₀ w : X → ℝ}
    (hf : TendstoInMeasure μ f atTop f₀)
    (hfm : ∀ n, AEStronglyMeasurable (f n) μ)
    (hwm : AEStronglyMeasurable w μ) :
    TendstoInMeasure μ (fun n x => f n x * w x) atTop (fun x => f₀ x * w x) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff (fun n => (hfm n).mul hwm)).2
  intro ns hns
  obtain ⟨ms, hms, hfae⟩ := (hf.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hfae] with x hx
  simpa using hx.mul_const (w x)

/-! The next lemma packages the coefficient, product, and Vitali steps used
when passing nonlinear mollified energy identities to the H¹ limit. -/

/-- Integrals of a convergent bounded coefficient times a product of two
strongly `L²`-convergent sequences converge to the expected product integral. -/
theorem tendsto_integral_coeff_mul_product_of_L2
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    (c : ℕ → X → ℝ) (c₀ : X → ℝ) {F G : ℕ → X → ℝ} {F₀ G₀ : X → ℝ}
    {C : ℝ} (hC : 0 ≤ C) (hcBound : ∀ n, ∀ᵐ x ∂μ, |c n x| ≤ C)
    (hc₀Bound : ∀ᵐ x ∂μ, |c₀ x| ≤ C)
    (hc : ∀ n, AEStronglyMeasurable (c n) μ) (hc₀ : AEStronglyMeasurable c₀ μ)
    (hcLim : TendstoInMeasure μ c atTop c₀)
    (hF : ∀ n, MemLp (F n) 2 μ) (hG : ∀ n, MemLp (G n) 2 μ)
    (hF₀ : MemLp F₀ 2 μ) (hG₀ : MemLp G₀ 2 μ)
    (hFl : Tendsto (fun n => eLpNorm (F n - F₀) 2 μ) atTop (𝓝 0))
    (hGl : Tendsto (fun n => eLpNorm (G n - G₀) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, c n x * F n x * G n x ∂μ) atTop
      (𝓝 (∫ x, c₀ x * F₀ x * G₀ x ∂μ)) := by
  let P : ℕ → X → ℝ := fun n x => F n x * G n x
  let P₀ : X → ℝ := fun x => F₀ x * G₀ x
  have hPmem : ∀ n, MemLp (P n) 1 μ := by
    intro n
    apply memLp_one_iff_integrable.2
    simpa [P] using (PDE.Parabolic.Energy.integrable_weight_mul
      (w := fun _ : X => (1 : ℝ)) (M := 1) aestronglyMeasurable_const
      (Filter.Eventually.of_forall fun _ => by simp) (hF n) (hG n))
  have hP₀mem : MemLp P₀ 1 μ := by
    apply memLp_one_iff_integrable.2
    simpa [P₀] using (PDE.Parabolic.Energy.integrable_weight_mul
      (w := fun _ : X => (1 : ℝ)) (M := 1) aestronglyMeasurable_const
      (Filter.Eventually.of_forall fun _ => by simp) hF₀ hG₀)
  have hPl : Tendsto (fun n => eLpNorm (P n - P₀) 1 μ) atTop (𝓝 0) :=
    tendsto_eLpNorm_mul_sub_one_of_L2 hF hG hF₀ hG₀ hFl hGl
  have hres : Tendsto (fun n => ∫ x, c n x * (P n x - P₀ x) ∂μ) atTop (𝓝 0) :=
    tendsto_integral_bounded_mul_of_tendsto_eLpNorm_one c
      (fun n x => P n x - P₀ x) hC hc
      hcBound
      (fun n => memLp_one_iff_integrable.1 ((hPmem n).sub hP₀mem)) hPl
  have hcDiffBound : ∀ n, ∀ᵐ x ∂μ, |c n x - c₀ x| ≤ 2 * C := by
    intro n
    filter_upwards [hcBound n, hc₀Bound] with x hx hx₀
    calc
      |c n x - c₀ x| ≤ |c n x| + |c₀ x| := abs_sub _ _
      _ ≤ C + C := add_le_add hx hx₀
      _ = 2 * C := by ring
  have hcDiffMeas : TendstoInMeasure μ (fun n x => c n x - c₀ x) atTop 0 := by
    apply (exists_seq_tendstoInMeasure_atTop_iff
      (fun n => (hc n).sub hc₀)).2
    intro ns hns
    obtain ⟨ms, hms, hcae⟩ := (hcLim.comp hns.tendsto_atTop).exists_seq_tendsto_ae
    refine ⟨ms, hms, ?_⟩
    filter_upwards [hcae] with x hx
    simpa using hx.sub_const (c₀ x)
  have hcoef : Tendsto (fun n => ∫ x, (c n x - c₀ x) * P₀ x ∂μ) atTop (𝓝 0) :=
    tendsto_integral_bounded_mul_of_tendstoInMeasure
      (fun n x => c n x - c₀ x) P₀ (C := 2 * C) (by positivity)
      (fun n => (hc n).sub hc₀) hcDiffBound hcDiffMeas
      (memLp_one_iff_integrable.1 hP₀mem)
  have hresInt : ∀ n, Integrable (fun x => c n x * (P n x - P₀ x)) μ := by
    intro n
    exact (memLp_one_iff_integrable.1 ((hPmem n).sub hP₀mem)).bdd_mul (hc n)
      (c := C) ((hcBound n).mono fun x hx => by
        simpa only [Real.norm_eq_abs] using hx)
  have hcoefInt : ∀ n, Integrable (fun x => (c n x - c₀ x) * P₀ x) μ := by
    intro n
    exact (memLp_one_iff_integrable.1 hP₀mem).bdd_mul ((hc n).sub hc₀)
      (c := 2 * C) ((hcDiffBound n).mono fun x hx => by
        simpa only [Real.norm_eq_abs] using hx)
  have htargetInt : ∀ n, Integrable (fun x => c n x * P n x) μ := by
    intro n
    exact (memLp_one_iff_integrable.1 (hPmem n)).bdd_mul (hc n) (c := C)
      ((hcBound n).mono fun x hx => by
        simpa only [Real.norm_eq_abs] using hx)
  have hlimitInt : Integrable (fun x => c₀ x * P₀ x) μ := by
    exact (memLp_one_iff_integrable.1 hP₀mem).bdd_mul hc₀ (c := C)
      (hc₀Bound.mono fun x hx => by simpa only [Real.norm_eq_abs] using hx)
  have hdecomp (n : ℕ) :
      (∫ x, c n x * P n x ∂μ) - ∫ x, c₀ x * P₀ x ∂μ =
        (∫ x, c n x * (P n x - P₀ x) ∂μ) +
          ∫ x, (c n x - c₀ x) * P₀ x ∂μ := by
    rw [← integral_sub (htargetInt n) hlimitInt,
      ← integral_add (hresInt n) (hcoefInt n)]
    apply integral_congr_ae (Eventually.of_forall fun x => ?_)
    ring
  have hdiff : Tendsto
      (fun n => (∫ x, c n x * P n x ∂μ) - ∫ x, c₀ x * P₀ x ∂μ) atTop (𝓝 0) := by
    simpa using (hres.add hcoef).congr'
      (Eventually.of_forall fun n => (hdecomp n).symm)
  have hresult : Tendsto
      (fun n => ∫ x, c n x * P n x ∂μ) atTop (𝓝 (∫ x, c₀ x * P₀ x ∂μ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hnorm := hdiff.norm
    simpa [Real.norm_eq_abs, abs_sub_comm] using hnorm
  simpa [P, P₀, mul_assoc] using hresult

end PDE.Parabolic.Chain
