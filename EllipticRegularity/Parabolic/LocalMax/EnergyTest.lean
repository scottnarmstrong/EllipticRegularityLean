/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.LocalMax.Renormalization
public import EllipticRegularity.Parabolic.LocalMax.EnergyLebesgue

/-! # Test functions `η² χ(t)` for the power energy estimate

The time ramp `χ_{t₁,h}` and the test function `η² χ` together with their derivatives.
-/

@[expose] public section

namespace PDE.Parabolic.LocalMax

open MeasureTheory Set Filter Topology PDE PDE.Parabolic.Chain PDE.Parabolic.WeakSlice

/-- The time ramp: `1` for `t ≤ t₁ - h`, `0` for `t ≥ t₁`. -/
noncomputable def timeRamp (t₁ h t : ℝ) : ℝ := 1 - Real.smoothTransition ((t - t₁ + h) / h)

theorem timeRamp_contDiff (t₁ h : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (timeRamp t₁ h) := by
  unfold timeRamp
  exact contDiff_const.sub (Real.smoothTransition.contDiff.comp (by fun_prop))

theorem timeRamp_nonneg (t₁ h t : ℝ) : 0 ≤ timeRamp t₁ h t := by
  unfold timeRamp
  linarith [Real.smoothTransition.le_one ((t - t₁ + h) / h)]

theorem timeRamp_le_one (t₁ h t : ℝ) : timeRamp t₁ h t ≤ 1 := by
  unfold timeRamp
  linarith [Real.smoothTransition.nonneg ((t - t₁ + h) / h)]

theorem timeRamp_eq_zero {t₁ h t : ℝ} (hh : 0 < h) (ht : t₁ ≤ t) : timeRamp t₁ h t = 0 := by
  unfold timeRamp
  rw [Real.smoothTransition.one_of_one_le, sub_self]
  rw [le_div_iff₀ hh]; linarith

theorem timeRamp_eq_one {t₁ h t : ℝ} (hh : 0 < h) (ht : t ≤ t₁ - h) : timeRamp t₁ h t = 1 := by
  unfold timeRamp
  rw [Real.smoothTransition.zero_of_nonpos, sub_zero]
  rw [div_nonpos_iff]; right; exact ⟨by linarith, hh.le⟩

theorem deriv_timeRamp (t₁ h t : ℝ) :
    deriv (timeRamp t₁ h) t = -rampKernel t₁ h t := by
  have hd : HasDerivAt (fun t : ℝ => (t - t₁ + h) / h) h⁻¹ t := by
    simpa using ((hasDerivAt_id t).sub_const t₁ |>.add_const h).div_const h
  have h2 := (rampDeriv_hasDerivAt ((t - t₁ + h) / h)).comp t hd
  have h3 : HasDerivAt (timeRamp t₁ h) (-(rampDeriv ((t - t₁ + h) / h) * h⁻¹)) t :=
    ((hasDerivAt_const t (1 : ℝ)).sub h2).congr_deriv (by ring)
  rw [h3.deriv, rampKernel]
  have : (t - t₁ + h) / h = (t - (t₁ - h)) / h := by ring
  rw [this]; ring

variable {d : ℕ}

/-- The test function `η² χ(t)`. -/
def rampTest (η : Vec d × ℝ → ℝ) (χ : ℝ → ℝ) (z : Vec d × ℝ) : ℝ := η z ^ 2 * χ z.2

theorem rampTest_contDiff {η : Vec d × ℝ → ℝ} {χ : ℝ → ℝ} (hη : ContDiff ℝ 1 η)
    (hχ : ContDiff ℝ 1 χ) : ContDiff ℝ 1 (rampTest η χ) :=
  (hη.pow 2).mul (hχ.comp contDiff_snd)

theorem parTimeDeriv_snd_comp {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) (z : Vec d × ℝ) :
    parTimeDeriv (fun w : Vec d × ℝ => χ w.2) z = deriv χ z.2 := by
  have := (hχ.differentiable one_ne_zero z.2).hasDerivAt.comp_hasFDerivAt z
    (hasFDerivAt_snd (𝕜 := ℝ) (E := Vec d) (F := ℝ) (p := z))
  have e : (fun w : Vec d × ℝ => χ w.2) = χ ∘ Prod.snd := rfl
  unfold parTimeDeriv
  rw [e, this.fderiv]
  simp

theorem parSpaceGrad_snd_comp {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) (z : Vec d × ℝ) :
    parSpaceGrad (fun w : Vec d × ℝ => χ w.2) z = 0 := by
  have := (hχ.differentiable one_ne_zero z.2).hasDerivAt.comp_hasFDerivAt z
    (hasFDerivAt_snd (𝕜 := ℝ) (E := Vec d) (F := ℝ) (p := z))
  ext i
  have e : (fun w : Vec d × ℝ => χ w.2) = χ ∘ Prod.snd := rfl
  unfold parSpaceGrad
  rw [e, this.fderiv]
  simp

theorem parTimeDeriv_sq' {η : Vec d × ℝ → ℝ} (hη : ContDiff ℝ 1 η) (z : Vec d × ℝ) :
    parTimeDeriv (fun w => η w ^ 2) z = 2 * η z * parTimeDeriv η z := by
  have := parTimeDeriv_mul hη hη z
  have e : (fun w => η w ^ 2) = fun w => η w * η w := funext fun w => sq (η w)
  rw [e, this]; ring

theorem parSpaceGrad_sq' {η : Vec d × ℝ → ℝ} (hη : ContDiff ℝ 1 η) (z : Vec d × ℝ) :
    parSpaceGrad (fun w => η w ^ 2) z = (2 * η z) • parSpaceGrad η z := by
  have := parSpaceGrad_mul hη hη z
  have e : (fun w => η w ^ 2) = fun w => η w * η w := funext fun w => sq (η w)
  rw [e, this]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem parTimeDeriv_rampTest {η : Vec d × ℝ → ℝ} {χ : ℝ → ℝ} (hη : ContDiff ℝ 1 η)
    (hχ : ContDiff ℝ 1 χ) (z : Vec d × ℝ) :
    parTimeDeriv (rampTest η χ) z =
      2 * η z * parTimeDeriv η z * χ z.2 + η z ^ 2 * deriv χ z.2 := by
  have := parTimeDeriv_mul (f := fun w => η w ^ 2) (g := fun w : Vec d × ℝ => χ w.2)
    (hη.pow 2) (hχ.comp contDiff_snd) z
  change parTimeDeriv (fun w => η w ^ 2 * χ w.2) z = _ at this
  unfold rampTest
  rw [this, parTimeDeriv_sq' hη, parTimeDeriv_snd_comp hχ]

theorem parSpaceGrad_rampTest {η : Vec d × ℝ → ℝ} {χ : ℝ → ℝ} (hη : ContDiff ℝ 1 η)
    (hχ : ContDiff ℝ 1 χ) (z : Vec d × ℝ) :
    parSpaceGrad (rampTest η χ) z = (2 * η z * χ z.2) • parSpaceGrad η z := by
  have := parSpaceGrad_mul (f := fun w => η w ^ 2) (g := fun w : Vec d × ℝ => χ w.2)
    (hη.pow 2) (hχ.comp contDiff_snd) z
  change parSpaceGrad (fun w => η w ^ 2 * χ w.2) z = _ at this
  unfold rampTest
  rw [this, parSpaceGrad_sq' hη, parSpaceGrad_snd_comp hχ]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, smul_zero, add_zero]
  ring

/-- The support of the test function. -/
theorem tsupport_rampTest_subset {η : Vec d × ℝ → ℝ} {χ : ℝ → ℝ} {Kx : Set (Vec d)}
    (hKx : IsCompact Kx) (hηx : ∀ x t, x ∉ Kx → η (x, t) = 0) {T δ t₁ : ℝ}
    (hηt : ∀ x t, t ≤ T + δ → η (x, t) = 0) (hχ0 : ∀ t, t₁ ≤ t → χ t = 0) :
    tsupport (rampTest η χ) ⊆ Kx ×ˢ Icc (T + δ) t₁ := by
  have hcl : IsClosed (Kx ×ˢ Icc (T + δ) t₁) := hKx.isClosed.prod isClosed_Icc
  refine closure_minimal ?_ hcl
  rintro ⟨x, t⟩ hz
  rw [Function.mem_support] at hz
  have hz' : η (x, t) ^ 2 * χ t ≠ 0 := hz
  have hη0 : η (x, t) ≠ 0 := fun h => hz' (by simp [h])
  have hχ1 : χ t ≠ 0 := fun h => hz' (by simp [h])
  refine ⟨?_, ?_, ?_⟩
  · by_contra hx; exact hη0 (hηx x t hx)
  · by_contra ht; exact hη0 (hηt x t (not_le.1 ht).le)
  · by_contra ht; exact hχ1 (hχ0 t (not_le.1 ht).le)

/-- The test function `η² χ` as a `ParTestFunction` on `U × (-1,0)`. -/
noncomputable def rampTestFunction {U : Set (Vec d)} {η : Vec d × ℝ → ℝ} {χ : ℝ → ℝ}
    (hη : ContDiff ℝ 1 η) (hχ : ContDiff ℝ 1 χ) {Kx : Set (Vec d)}
    (hKx : IsCompact Kx) (hKxU : Kx ⊆ U) (hηx : ∀ x t, x ∉ Kx → η (x, t) = 0) {T δ t₁ tTop : ℝ}
    (hT : -1 < T) (htTop : tTop ≤ 0) (hδ : 0 < δ) (h1 : t₁ < tTop)
    (hηt : ∀ x t, t ≤ T + δ → η (x, t) = 0) (hχ0 : ∀ t, t₁ ≤ t → χ t = 0) :
    ParTestFunction U (interior (Ioc (-1 : ℝ) 0)) where
  toFun := rampTest η χ
  contDiff := rampTest_contDiff hη hχ
  hasCompactSupport := by
    refine IsCompact.of_isClosed_subset (hKx.prod isCompact_Icc) (isClosed_tsupport _)
      (tsupport_rampTest_subset hKx hηx hηt hχ0)
  tsupport_subset := by
    refine (tsupport_rampTest_subset hKx hηx hηt hχ0).trans (prod_mono hKxU ?_)
    rw [interior_Ioc]
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

theorem tsupport_rampTest_subset_Ioo {η : Vec d × ℝ → ℝ} {χ : ℝ → ℝ} {U Kx : Set (Vec d)}
    (hKx : IsCompact Kx) (hKxU : Kx ⊆ U) (hηx : ∀ x t, x ∉ Kx → η (x, t) = 0) {T δ t₁ tTop : ℝ}
    (hδ : 0 < δ) (h1 : t₁ < tTop)
    (hηt : ∀ x t, t ≤ T + δ → η (x, t) = 0) (hχ0 : ∀ t, t₁ ≤ t → χ t = 0) :
    tsupport (rampTest η χ) ⊆ U ×ˢ Ioo T tTop :=
  (tsupport_rampTest_subset hKx hηx hηt hχ0).trans
    (prod_mono hKxU fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)

end PDE.Parabolic.LocalMax
