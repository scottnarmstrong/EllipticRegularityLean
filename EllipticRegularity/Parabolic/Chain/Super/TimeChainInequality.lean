/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # One-dimensional chain inequality for a continuous supersolution curve

If `v` is continuous with `v τ₂ - v τ₁ ≥ ∫_{τ₁}^{τ₂} D` for all `τ₁ ≤ τ₂`, `F' ≥ 0` and `ψ ≥ 0` is
a `C¹` compactly supported weight, then `∫ F(v) ψ' + F'(v) ψ D ≤ 0`. The proof first treats a
continuous `D` through Steklov averages and then passes to integrable `D` by `L¹` density.
-/

@[expose] public section

namespace PDE.Parabolic.Chain.Super

open MeasureTheory Set Filter Topology intervalIntegral

/-- The primitive `x ↦ ∫_0^x f`. -/
noncomputable def prim (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y in (0 : ℝ)..x, f y

/-- The Steklov average `(1/h) ∫_τ^{τ+h} f`, written through the primitive. -/
noncomputable def steklov (f : ℝ → ℝ) (h τ : ℝ) : ℝ := (prim f (τ + h) - prim f τ) / h

theorem hasDerivAt_prim {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (prim f) (f x) x :=
  (hf.integral_hasStrictDerivAt 0 x).hasDerivAt

theorem prim_sub {f : ℝ → ℝ} (hf : Continuous f) (a b : ℝ) :
    prim f b - prim f a = ∫ y in a..b, f y := by
  unfold prim
  exact integral_interval_sub_left (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)

theorem steklov_hasDerivAt {f : ℝ → ℝ} (hf : Continuous f) (h τ : ℝ) :
    HasDerivAt (steklov f h) ((f (τ + h) - f τ) / h) τ := by
  unfold steklov
  have h1 : HasDerivAt (fun τ => prim f (τ + h)) (f (τ + h)) τ :=
    (hasDerivAt_prim hf (τ + h)).comp_add_const τ h
  exact (h1.sub (hasDerivAt_prim hf τ)).div_const h

theorem steklov_continuous {f : ℝ → ℝ} (hf : Continuous f) (h : ℝ) :
    Continuous (steklov f h) :=
  continuous_iff_continuousAt.2 fun τ => (steklov_hasDerivAt hf h τ).continuousAt

theorem steklov_eq_integral {f : ℝ → ℝ} (hf : Continuous f) (h τ : ℝ) :
    steklov f h τ = (∫ y in τ..τ + h, f y) / h := by
  unfold steklov
  rw [prim_sub hf]

theorem steklov_tendsto {f : ℝ → ℝ} (hf : Continuous f) (τ : ℝ) :
    Tendsto (fun h => steklov f h τ) (𝓝[>] 0) (𝓝 (f τ)) := by
  have := (hasDerivAt_prim hf τ).tendsto_slope_zero_right
  refine this.congr fun h => ?_
  simp only [steklov, smul_eq_mul]
  ring

theorem abs_steklov_le {f : ℝ → ℝ} (hf : Continuous f) {h τ M : ℝ} (hh : 0 < h)
    (hM : ∀ y ∈ Icc τ (τ + h), |f y| ≤ M) : |steklov f h τ| ≤ M := by
  rw [steklov_eq_integral hf, abs_div, abs_of_pos hh, div_le_iff₀ hh]
  have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := τ) (b := τ + h)
    (f := f) (C := M) (fun y hy => by
      rw [Real.norm_eq_abs]
      exact hM y (by rw [uIoc_of_le (by linarith)] at hy; exact ⟨hy.1.le, hy.2⟩))
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ τ + h - τ)] at h1
  linarith

section

variable {v D ψ F : ℝ → ℝ}

/-- The chain inequality for a fixed Steklov parameter. -/
theorem chain_ineq_steklov (hv : Continuous v) (hD : Continuous D)
    (hmono : ∀ τ1 τ2, τ1 ≤ τ2 → ∫ σ in τ1..τ2, D σ ≤ v τ2 - v τ1)
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (hψ0 : ∀ τ, 0 ≤ ψ τ)
    (hF : ContDiff ℝ 1 F) (hF0 : ∀ r, 0 ≤ deriv F r) {h : ℝ} (hh : 0 < h) :
    ∫ τ, (F (steklov v h τ) * deriv ψ τ +
      deriv F (steklov v h τ) * ψ τ * steklov D h τ) ≤ 0 := by
  set V := steklov v h with hVdef
  have hVc : Continuous V := steklov_continuous hv h
  have hDc : Continuous (steklov D h) := steklov_continuous hD h
  have hF'c : Continuous (deriv F) := hF.continuous_deriv le_rfl
  have hψ'c : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  have hψcont : Continuous ψ := hψ.continuous
  have hFd : ∀ x, HasDerivAt F (deriv F x) x := fun x =>
    (hF.differentiable one_ne_zero x).hasDerivAt
  have hψd : ∀ x, HasDerivAt ψ (deriv ψ x) x := fun x =>
    (hψ.differentiable one_ne_zero x).hasDerivAt
  let W' : ℝ → ℝ := fun τ => F (V τ) * deriv ψ τ +
    deriv F (V τ) * ψ τ * ((v (τ + h) - v τ) / h)
  have hWd : ∀ τ, HasDerivAt (fun τ => F (V τ) * ψ τ) (W' τ) τ := by
    intro τ
    have := ((hFd (V τ)).comp τ (steklov_hasDerivAt hv h τ)).mul (hψd τ)
    refine this.congr_deriv ?_
    simp only [W', Function.comp_apply]
    ring
  have hsupp : ∀ x, x ∉ tsupport ψ → ψ x = 0 ∧ deriv ψ x = 0 := fun x hx =>
    ⟨image_eq_zero_of_notMem_tsupport hx,
      image_eq_zero_of_notMem_tsupport (fun h' => hx (tsupport_deriv_subset h'))⟩
  have hWc : Continuous fun τ => F (V τ) * ψ τ :=
    (hF.continuous.comp hVc).mul hψcont
  have hWcs : HasCompactSupport fun τ => F (V τ) * ψ τ :=
    HasCompactSupport.intro hψc.isCompact fun x hx => by
      simp [(hsupp x hx).1]
  have hW'c : Continuous W' := by
    have h1 : Continuous fun τ => (v (τ + h) - v τ) / h :=
      ((hv.comp (continuous_id.add continuous_const)).sub hv).div_const h
    exact ((hF.continuous.comp hVc).mul hψ'c).add
      (((hF'c.comp hVc).mul hψcont).mul h1)
  have hW'cs : HasCompactSupport W' :=
    HasCompactSupport.intro hψc.isCompact fun x hx => by
      simp [W', (hsupp x hx).1, (hsupp x hx).2]
  have hzero : ∫ τ, W' τ = 0 :=
    integral_eq_zero_of_hasDerivAt_of_integrable hWd
      (hW'c.integrable_of_hasCompactSupport hW'cs)
      (hWc.integrable_of_hasCompactSupport hWcs)
  rw [← hzero]
  have hLc : Continuous fun τ => F (V τ) * deriv ψ τ +
      deriv F (V τ) * ψ τ * steklov D h τ :=
    ((hF.continuous.comp hVc).mul hψ'c).add (((hF'c.comp hVc).mul hψcont).mul hDc)
  have hLcs : HasCompactSupport fun τ => F (V τ) * deriv ψ τ +
      deriv F (V τ) * ψ τ * steklov D h τ :=
    HasCompactSupport.intro hψc.isCompact fun x hx => by
      simp [(hsupp x hx).1, (hsupp x hx).2]
  refine integral_mono (hLc.integrable_of_hasCompactSupport hLcs)
    (hW'c.integrable_of_hasCompactSupport hW'cs) fun τ => ?_
  have hD1 : steklov D h τ ≤ (v (τ + h) - v τ) / h := by
    rw [steklov_eq_integral hD]
    exact div_le_div_of_nonneg_right (hmono τ (τ + h) (by linarith)) hh.le
  have hnn : 0 ≤ deriv F (V τ) * ψ τ := mul_nonneg (hF0 _) (hψ0 _)
  simp only [W']
  have := mul_le_mul_of_nonneg_left hD1 hnn
  linarith

/-- The chain inequality for a continuous `D`. -/
theorem chain_ineq_continuous (hv : Continuous v) (hD : Continuous D)
    (hmono : ∀ τ1 τ2, τ1 ≤ τ2 → ∫ σ in τ1..τ2, D σ ≤ v τ2 - v τ1)
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (hψ0 : ∀ τ, 0 ≤ ψ τ)
    (hF : ContDiff ℝ 1 F) (hF0 : ∀ r, 0 ≤ deriv F r) :
    ∫ τ, (F (v τ) * deriv ψ τ + deriv F (v τ) * ψ τ * D τ) ≤ 0 := by
  have hF'c : Continuous (deriv F) := hF.continuous_deriv le_rfl
  have hψ'c : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  have hψcont : Continuous ψ := hψ.continuous
  have hsupp : ∀ x, x ∉ tsupport ψ → ψ x = 0 ∧ deriv ψ x = 0 := fun x hx =>
    ⟨image_eq_zero_of_notMem_tsupport hx,
      image_eq_zero_of_notMem_tsupport (fun h' => hx (tsupport_deriv_subset h'))⟩
  set K := tsupport ψ with hK
  have hKc : IsCompact K := hψc.isCompact
  have : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
  have hvanish : ∀ (G : ℝ → ℝ), (∀ x, x ∉ K → G x = 0) →
      ∫ τ, G τ = ∫ τ in K, G τ := fun G hG =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero hG).symm
  -- the integrand
  let f : ℝ → ℝ → ℝ := fun h τ => F (steklov v h τ) * deriv ψ τ +
    deriv F (steklov v h τ) * ψ τ * steklov D h τ
  let f0 : ℝ → ℝ := fun τ => F (v τ) * deriv ψ τ + deriv F (v τ) * ψ τ * D τ
  have hfvan : ∀ h, ∀ x, x ∉ K → f h x = 0 := fun h x hx => by
    simp [f, (hsupp x hx).1, (hsupp x hx).2]
  have hf0van : ∀ x, x ∉ K → f0 x = 0 := fun x hx => by
    simp [f0, (hsupp x hx).1, (hsupp x hx).2]
  -- bounds
  obtain ⟨R, hR⟩ := hKc.isBounded.subset_closedBall (0 : ℝ)
  obtain ⟨Mv, hMv⟩ := (isCompact_Icc (a := -R) (b := R + 1)).exists_bound_of_continuousOn
    hv.continuousOn
  obtain ⟨MD, hMD⟩ := (isCompact_Icc (a := -R) (b := R + 1)).exists_bound_of_continuousOn
    hD.continuousOn
  obtain ⟨MF, hMF⟩ := (isCompact_Icc (a := -Mv) (b := Mv)).exists_bound_of_continuousOn
    hF.continuous.continuousOn
  obtain ⟨MF', hMF'⟩ := (isCompact_Icc (a := -Mv) (b := Mv)).exists_bound_of_continuousOn
    hF'c.continuousOn
  obtain ⟨Mψ, hMψ⟩ := hKc.exists_bound_of_continuousOn hψcont.continuousOn
  obtain ⟨Mψ', hMψ'⟩ := hKc.exists_bound_of_continuousOn hψ'c.continuousOn
  have hKR : ∀ τ ∈ K, τ ∈ Icc (-R) R := fun τ hτ => by
    have := hR hτ
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le] at this
    exact this
  have hlim : Tendsto (fun h => ∫ τ in K, f h τ) (𝓝[>] 0) (𝓝 (∫ τ in K, f0 τ)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun _ => MF * Mψ' + MF' * Mψ * MD) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun h => ?_
      refine Continuous.aestronglyMeasurable ?_
      have hVc : Continuous (steklov v h) := steklov_continuous hv h
      have hDc : Continuous (steklov D h) := steklov_continuous hD h
      exact ((hF.continuous.comp hVc).mul hψ'c).add (((hF'c.comp hVc).mul hψcont).mul hDc)
    · filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with h hh
      refine (ae_restrict_iff' hKc.measurableSet).2 (Eventually.of_forall fun τ hτ => ?_)
      have hτR := hKR τ hτ
      have hVb : |steklov v h τ| ≤ Mv := abs_steklov_le hv hh.1 fun y hy =>
        by simpa [Real.norm_eq_abs] using hMv y ⟨by linarith [hy.1, hτR.1], by linarith [hy.2, hτR.2, hh.2]⟩
      have hDb : |steklov D h τ| ≤ MD := abs_steklov_le hD hh.1 fun y hy =>
        by simpa [Real.norm_eq_abs] using hMD y ⟨by linarith [hy.1, hτR.1], by linarith [hy.2, hτR.2, hh.2]⟩
      have hVmem : steklov v h τ ∈ Icc (-Mv) Mv := abs_le.1 hVb
      have h1 : |F (steklov v h τ)| ≤ MF := by
        simpa [Real.norm_eq_abs] using hMF _ hVmem
      have h2 : |deriv F (steklov v h τ)| ≤ MF' := by
        simpa [Real.norm_eq_abs] using hMF' _ hVmem
      have h3 : |ψ τ| ≤ Mψ := by simpa [Real.norm_eq_abs] using hMψ τ hτ
      have h4 : |deriv ψ τ| ≤ Mψ' := by simpa [Real.norm_eq_abs] using hMψ' τ hτ
      rw [Real.norm_eq_abs]
      simp only [f]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]
        exact mul_le_mul h1 h4 (abs_nonneg _) ((abs_nonneg _).trans h1)
      · rw [abs_mul, abs_mul]
        exact mul_le_mul (mul_le_mul h2 h3 (abs_nonneg _) ((abs_nonneg _).trans h2)) hDb
          (abs_nonneg _) (mul_nonneg ((abs_nonneg _).trans h2) ((abs_nonneg _).trans h3))
    · exact integrable_const _
    · refine Eventually.of_forall fun τ => ?_
      have hV := steklov_tendsto hv τ
      have hDt := steklov_tendsto hD τ
      exact (((hF.continuous.tendsto (v τ)).comp hV).mul_const _).add
        ((((hF'c.tendsto (v τ)).comp hV).mul_const _).mul hDt)
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∫ τ in K, f h τ ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    rw [← hvanish (f h) (hfvan h)]
    exact chain_ineq_steklov hv hD hmono hψ hψc hψ0 hF hF0 hh
  have := le_of_tendsto hlim hev
  rwa [← hvanish f0 hf0van] at this

theorem abs_intervalIntegral_le_integral_abs {f : ℝ → ℝ} (hf : Integrable f) (a b : ℝ) :
    |∫ x in a..b, f x| ≤ ∫ x, |f x| := by
  have key : ∀ a b : ℝ, a ≤ b → |∫ x in a..b, f x| ≤ ∫ x, |f x| := by
    intro a b hab
    rw [integral_of_le hab]
    calc |∫ x in Ioc a b, f x| = ‖∫ x in Ioc a b, f x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ x in Ioc a b, ‖f x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x, ‖f x‖ :=
        setIntegral_le_integral hf.norm (Eventually.of_forall fun x => norm_nonneg _)
      _ = ∫ x, |f x| := by simp only [Real.norm_eq_abs]
  rcases le_total a b with h | h
  · exact key a b h
  · rw [integral_symm, abs_neg]
    exact key b a h

theorem pointwise_chain_error {a a' b b' p q d e η C1 C2 M : ℝ}
    (ha : |a - a'| ≤ C1 * η) (hb : |b - b'| ≤ C2 * η) (hb' : |b'| ≤ C1) (hp : |p| ≤ M) :
    a * q + b * p * d ≤ a' * q + b' * p * e +
      (C1 * η * |q| + C2 * η * M * |d| + C1 * M * |d - e|) := by
  have hid : a * q + b * p * d = a' * q + b' * p * e +
      ((a - a') * q + p * ((b - b') * d + b' * (d - e))) := by ring
  have h1 : |(a - a') * q| ≤ C1 * η * |q| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right ha (abs_nonneg _)
  have h2 : |p * ((b - b') * d + b' * (d - e))| ≤ M * (C2 * η * |d| + C1 * |d - e|) := by
    rw [abs_mul]
    refine mul_le_mul hp ?_ (abs_nonneg _) ((abs_nonneg _).trans hp)
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_right hb' (abs_nonneg _)
  have h3 := le_abs_self ((a - a') * q)
  have h4 := le_abs_self (p * ((b - b') * d + b' * (d - e)))
  have h5 : M * (C2 * η * |d| + C1 * |d - e|) = C2 * η * M * |d| + C1 * M * |d - e| := by ring
  rw [hid]
  linarith

/-- The chain inequality for an integrable `D`, by approximating `D` in `L¹` by continuous
compactly supported functions and correcting `v` by the primitives. -/
theorem chain_ineq (hv : Continuous v) (hD : Integrable D)
    (hmono : ∀ τ1 τ2, τ1 ≤ τ2 → ∫ σ in τ1..τ2, D σ ≤ v τ2 - v τ1)
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (hψ0 : ∀ τ, 0 ≤ ψ τ)
    (hF : ContDiff ℝ 2 F) (hF0 : ∀ r, 0 ≤ deriv F r)
    (hF'bound : ∃ C : NNReal, ∀ s, |deriv F s| ≤ C)
    (hF''bound : ∃ C : NNReal, ∀ s, |deriv (deriv F) s| ≤ C) :
    ∫ τ, (F (v τ) * deriv ψ τ + deriv F (v τ) * ψ τ * D τ) ≤ 0 := by
  obtain ⟨C1, hC1⟩ := hF'bound
  obtain ⟨C2, hC2⟩ := hF''bound
  have hF1 : ContDiff ℝ 1 (deriv F) := by
    have := hF.iterate_deriv' 1 1
    simpa using this
  have hFd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hF'd : Differentiable ℝ (deriv F) := hF1.differentiable one_ne_zero
  have hLipF : LipschitzWith C1 F :=
    lipschitzWith_of_nnnorm_deriv_le hFd fun x => by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs]; exact hC1 x
  have hLipF' : LipschitzWith C2 (deriv F) :=
    lipschitzWith_of_nnnorm_deriv_le hF'd fun x => by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs]; exact hC2 x
  have hF'c : Continuous (deriv F) := hF1.continuous
  have hψ'c : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  have hψcont : Continuous ψ := hψ.continuous
  have hψ'cs : HasCompactSupport (deriv ψ) := hψc.deriv
  have hψ'int : Integrable (deriv ψ) := hψ'c.integrable_of_hasCompactSupport hψ'cs
  obtain ⟨Mψ, hMψ⟩ := hψcont.bounded_above_of_compact_support hψc
  have hMψ0 : 0 ≤ Mψ := (norm_nonneg _).trans (hMψ 0)
  have hψb : ∀ τ, |ψ τ| ≤ Mψ := fun τ => by simpa [Real.norm_eq_abs] using hMψ τ
  set A : ℝ := C1 * (∫ τ, |deriv ψ τ|) + C2 * Mψ * (∫ τ, |D τ|) + C1 * Mψ with hA
  have hA0 : 0 ≤ A := by
    have h1 : 0 ≤ ∫ τ, |deriv ψ τ| := integral_nonneg fun _ => abs_nonneg _
    have h2 : 0 ≤ ∫ τ, |D τ| := integral_nonneg fun _ => abs_nonneg _
    positivity
  have key : ∀ η : ℝ, 0 < η → ∫ τ, (F (v τ) * deriv ψ τ + deriv F (v τ) * ψ τ * D τ) ≤ A * η := by
    intro η hη
    obtain ⟨g, hgcs, hgD, hgc, hgint⟩ := hD.exists_hasCompactSupport_integral_sub_le hη
    have hEv : Continuous fun τ => ∫ y in (0 : ℝ)..τ, D y :=
      continuous_primitive (fun a b => hD.intervalIntegrable) 0
    have hEg : Continuous fun τ => ∫ y in (0 : ℝ)..τ, g y :=
      continuous_primitive (fun a b => hgint.intervalIntegrable) 0
    set vt : ℝ → ℝ := fun τ => v τ - (∫ y in (0 : ℝ)..τ, D y) + (∫ y in (0 : ℝ)..τ, g y) with hvt
    have hvtc : Continuous vt := (hv.sub hEv).add hEg
    have hvtmono : ∀ τ1 τ2, τ1 ≤ τ2 → ∫ σ in τ1..τ2, g σ ≤ vt τ2 - vt τ1 := by
      intro τ1 τ2 h12
      have e1 := integral_interval_sub_left (a := (0 : ℝ)) (b := τ2) (c := τ1) (μ := volume)
        (f := D) hD.intervalIntegrable hD.intervalIntegrable
      have e2 := integral_interval_sub_left (a := (0 : ℝ)) (b := τ2) (c := τ1) (μ := volume)
        (f := g) hgint.intervalIntegrable hgint.intervalIntegrable
      have := hmono τ1 τ2 h12
      simp only [hvt]
      linarith
    have hdiff : ∀ τ, |vt τ - v τ| ≤ η := by
      intro τ
      have : vt τ - v τ = ∫ y in (0 : ℝ)..τ, (g y - D y) := by
        simp only [hvt]
        rw [integral_sub hgint.intervalIntegrable hD.intervalIntegrable]
        ring
      rw [this]
      refine (abs_intervalIntegral_le_integral_abs (hgint.sub hD) 0 τ).trans ?_
      refine le_trans (le_of_eq ?_) hgD
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [Real.norm_eq_abs]
      exact abs_sub_comm _ _
    have hJ := chain_ineq_continuous hvtc hgc hvtmono hψ hψc hψ0 (hF.of_le (by norm_num)) hF0
    -- integrability of the pieces
    have hf0int : Integrable fun τ => F (v τ) * deriv ψ τ + deriv F (v τ) * ψ τ * D τ := by
      have h1 : Integrable fun τ => F (v τ) * deriv ψ τ :=
        ((hF.continuous.comp hv).mul hψ'c).integrable_of_hasCompactSupport
          (HasCompactSupport.mul_left hψ'cs)
      have hw : Continuous fun τ => deriv F (v τ) * ψ τ := (hF'c.comp hv).mul hψcont
      have hws : HasCompactSupport fun τ => deriv F (v τ) * ψ τ := HasCompactSupport.mul_left hψc
      obtain ⟨Cw, hCw⟩ := hw.bounded_above_of_compact_support hws
      have h2 : Integrable fun τ => deriv F (v τ) * ψ τ * D τ :=
        hD.bdd_mul hw.aestronglyMeasurable (Eventually.of_forall hCw)
      exact h1.add h2
    have hJint : Integrable fun τ => F (vt τ) * deriv ψ τ + deriv F (vt τ) * ψ τ * g τ := by
      have h1 : Integrable fun τ => F (vt τ) * deriv ψ τ :=
        ((hF.continuous.comp hvtc).mul hψ'c).integrable_of_hasCompactSupport
          (HasCompactSupport.mul_left hψ'cs)
      have hw : Continuous fun τ => deriv F (vt τ) * ψ τ := (hF'c.comp hvtc).mul hψcont
      have hws : HasCompactSupport fun τ => deriv F (vt τ) * ψ τ := HasCompactSupport.mul_left hψc
      obtain ⟨Cw, hCw⟩ := hw.bounded_above_of_compact_support hws
      have h2 : Integrable fun τ => deriv F (vt τ) * ψ τ * g τ :=
        hgint.bdd_mul hw.aestronglyMeasurable (Eventually.of_forall hCw)
      exact h1.add h2
    have hBint : Integrable fun τ => C1 * η * |deriv ψ τ| + C2 * η * Mψ * |D τ| +
        C1 * Mψ * |D τ - g τ| :=
      ((hψ'int.abs.const_mul _).add (hD.abs.const_mul _)).add ((hD.sub hgint).abs.const_mul _)
    have hmain : ∫ τ, (F (v τ) * deriv ψ τ + deriv F (v τ) * ψ τ * D τ) ≤
        ∫ τ, ((F (vt τ) * deriv ψ τ + deriv F (vt τ) * ψ τ * g τ) +
          (C1 * η * |deriv ψ τ| + C2 * η * Mψ * |D τ| + C1 * Mψ * |D τ - g τ|)) := by
      refine integral_mono hf0int (hJint.add hBint) fun τ => ?_
      have hFa : |F (v τ) - F (vt τ)| ≤ C1 * η := by
        have := hLipF.dist_le_mul (v τ) (vt τ)
        rw [Real.dist_eq, Real.dist_eq] at this
        have h2 : |v τ - vt τ| ≤ η := by rw [abs_sub_comm]; exact hdiff τ
        exact this.trans (by simpa using mul_le_mul_of_nonneg_left h2 C1.coe_nonneg)
      have hFb : |deriv F (v τ) - deriv F (vt τ)| ≤ C2 * η := by
        have := hLipF'.dist_le_mul (v τ) (vt τ)
        rw [Real.dist_eq, Real.dist_eq] at this
        have h2 : |v τ - vt τ| ≤ η := by rw [abs_sub_comm]; exact hdiff τ
        exact this.trans (by simpa using mul_le_mul_of_nonneg_left h2 C2.coe_nonneg)
      exact pointwise_chain_error hFa hFb (hC1 _) (hψb τ)
    rw [integral_add hJint hBint] at hmain
    have hB : ∫ τ, (C1 * η * |deriv ψ τ| + C2 * η * Mψ * |D τ| + C1 * Mψ * |D τ - g τ|) ≤
        A * η := by
      have i1 : Integrable fun τ => C1 * η * |deriv ψ τ| := hψ'int.abs.const_mul _
      have i2 : Integrable fun τ => C2 * η * Mψ * |D τ| := hD.abs.const_mul _
      have i3 : Integrable fun τ => C1 * Mψ * |D τ - g τ| := (hD.sub hgint).abs.const_mul _
      have i12 : Integrable fun τ => C1 * η * |deriv ψ τ| + C2 * η * Mψ * |D τ| := i1.add i2
      have e : ∫ τ, (C1 * η * |deriv ψ τ| + C2 * η * Mψ * |D τ| + C1 * Mψ * |D τ - g τ|) =
          (C1 * η) * (∫ τ, |deriv ψ τ|) + (C2 * η * Mψ) * (∫ τ, |D τ|) +
            (C1 * Mψ) * (∫ τ, |D τ - g τ|) := by
        rw [integral_add i12 i3, integral_add i1 i2, MeasureTheory.integral_const_mul,
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      have hdg : ∫ τ, |D τ - g τ| ≤ η := by
        refine le_trans (le_of_eq ?_) hgD
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [Real.norm_eq_abs]
      have h3 := mul_le_mul_of_nonneg_left hdg (by positivity : 0 ≤ (C1 : ℝ) * Mψ)
      rw [e]
      simp only [hA]
      nlinarith [h3]
    linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have := key (ε / (A + 1)) (by positivity)
  have h2 : A * (ε / (A + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  linarith

theorem projIcc_coe {s t : ℝ} (h : s ≤ t) (τ : ℝ) :
    (projIcc s t h τ : ℝ) = max s (min t τ) := rfl

theorem integral_indicator_Ioc_eq {s t : ℝ} (hst : s ≤ t) {D : ℝ → ℝ} {τ1 τ2 : ℝ}
    (h12 : τ1 ≤ τ2) :
    ∫ σ in τ1..τ2, (Ioc s t).indicator D σ =
      ∫ σ in (projIcc s t hst τ1 : ℝ)..(projIcc s t hst τ2 : ℝ), D σ := by
  rw [intervalIntegral.integral_of_le h12, setIntegral_indicator measurableSet_Ioc,
    intervalIntegral.integral_of_le (by
      simp only [projIcc_coe]
      exact max_le_max le_rfl (min_le_min le_rfl h12))]
  have hset : Ioc τ1 τ2 ∩ Ioc s t =
      Ioc (max s (min t τ1)) (max s (min t τ2)) := by
    ext z
    simp only [mem_inter_iff, mem_Ioc, max_lt_iff, min_lt_iff, le_max_iff, le_min_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨h3, Or.inr h1⟩, Or.inr ⟨h4, h2⟩⟩
    · rintro ⟨⟨hs, hor⟩, hr⟩
      rcases hr with hr | ⟨hr1, hr2⟩
      · exact absurd hs (not_lt.2 hr)
      · rcases hor with hor | hor
        · exact absurd hr1 (not_le.2 hor)
        · exact ⟨⟨hor, hr2⟩, hs, hr1⟩
  rw [hset]
  rfl

/-- The chain inequality on a compact interval, for a weight vanishing outside `(s,t)`. -/
theorem chain_ineq_Icc {s t : ℝ} (hst : s ≤ t) (hv : ContinuousOn v (Icc s t))
    (hD : IntegrableOn D (Ioc s t))
    (hmono : ∀ τ1 τ2, s ≤ τ1 → τ1 ≤ τ2 → τ2 ≤ t → ∫ σ in τ1..τ2, D σ ≤ v τ2 - v τ1)
    (hψ : ContDiff ℝ 1 ψ) (hψt : ∀ τ, τ ∉ Ioo s t → ψ τ = 0) (hψ0 : ∀ τ, 0 ≤ ψ τ)
    (hF : ContDiff ℝ 2 F) (hF0 : ∀ r, 0 ≤ deriv F r)
    (hF'bound : ∃ C : NNReal, ∀ s, |deriv F s| ≤ C)
    (hF''bound : ∃ C : NNReal, ∀ s, |deriv (deriv F) s| ≤ C) :
    ∫ τ in Ioc s t, (F (v τ) * deriv ψ τ + deriv F (v τ) * ψ τ * D τ) ≤ 0 := by
  let vb : ℝ → ℝ := fun τ => v (projIcc s t hst τ : ℝ)
  let Db : ℝ → ℝ := (Ioc s t).indicator D
  have hvb : Continuous vb :=
    hv.comp_continuous continuous_projIcc.subtype_val (fun τ => (projIcc s t hst τ).2)
  have hDb : Integrable Db := (integrable_indicator_iff measurableSet_Ioc).2 hD
  have hmonob : ∀ τ1 τ2, τ1 ≤ τ2 → ∫ σ in τ1..τ2, Db σ ≤ vb τ2 - vb τ1 := by
    intro τ1 τ2 h12
    rw [integral_indicator_Ioc_eq hst h12]
    have hp : (projIcc s t hst τ1 : ℝ) ≤ (projIcc s t hst τ2 : ℝ) := by
      simp only [projIcc_coe]
      exact max_le_max le_rfl (min_le_min le_rfl h12)
    exact hmono _ _ (projIcc s t hst τ1).2.1 hp (projIcc s t hst τ2).2.2
  have hsupp : Function.support ψ ⊆ Icc s t := fun τ hτ =>
    Ioo_subset_Icc_self (by_contra fun h => hτ (hψt τ h))
  have hψc : HasCompactSupport ψ :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  have hts : tsupport ψ ⊆ Icc s t := closure_minimal hsupp isClosed_Icc
  have hmain := chain_ineq hvb hDb hmonob hψ hψc hψ0 hF hF0 hF'bound hF''bound
  have hvan : ∀ τ, τ ∉ Icc s t →
      F (vb τ) * deriv ψ τ + deriv F (vb τ) * ψ τ * Db τ = 0 := by
    intro τ hτ
    have h1 : ψ τ = 0 := image_eq_zero_of_notMem_tsupport fun h => hτ (hts h)
    have h2 : deriv ψ τ = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hτ (hts (tsupport_deriv_subset h))
    simp [h1, h2]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvan,
    integral_Icc_eq_integral_Ioc] at hmain
  refine le_of_eq_of_le (setIntegral_congr_fun measurableSet_Ioc fun τ hτ => ?_) hmain
  have hτ' : τ ∈ Icc s t := Ioc_subset_Icc_self hτ
  have hvτ : vb τ = v τ := by simp only [vb, projIcc_of_mem _ hτ']
  have hDτ : Db τ = D τ := by simp only [Db, indicator_of_mem hτ]
  simp only [hvτ, hDτ]

end

end PDE.Parabolic.Chain.Super
