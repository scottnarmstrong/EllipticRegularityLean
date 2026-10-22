/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.LocalMax.EnergyRamp

/-! # The gradient part of the power energy estimate

Letting the ramp `χ_n` increase to `1` on `(T, tTop)` in the fixed-ramp inequality.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.LocalMax

open MeasureTheory Set Filter Topology PDE PDE.Parabolic.Chain

variable {d : ℕ} {U : Set (Vec d)} {Lam : ℝ} {a : ParCoeffField d}
  {u : ParH1Function U (Ioc (-1 : ℝ) 0)} {F : ℝ → ℝ} {K : ℝ} {η : Vec d × ℝ → ℝ}
  {Kx : Set (Vec d)} {T tTop δ : ℝ}

theorem ofReal_eq_two_mul_ofReal_half (x : ℝ) :
    ENNReal.ofReal x = 2 * ENNReal.ofReal (1 / 2 * x) := by
  have : x = 2 * (1 / 2 * x) := by ring
  conv_lhs => rw [this]
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

/-- The ramp inequality for the specific ramp `timeRamp (tTop - ε) ε`. -/
theorem ramp_energy_grad_fixed (H : EnergyHyp U Lam a u F K η Kx T tTop δ) {ε : ℝ}
    (hε : 0 < ε) :
    ∫⁻ z in U ×ˢ Ioo T tTop, ENNReal.ofReal (1 / 2 * deriv (deriv F) (u.toFun z) *
      vecNormSq (u.grad z) * η z ^ 2 * timeRamp (tTop - ε) ε z.2) ≤
      energyBound Lam K F u η T tTop :=
  (ramp_energy_core H (χ := timeRamp (tTop - ε) ε)
    ((timeRamp_contDiff _ _).of_le (by exact_mod_cast le_top)) (timeRamp_nonneg _ _)
    (timeRamp_le_one _ _)
    (fun t => by
      rw [deriv_timeRamp]
      exact neg_nonpos.2 (rampKernel_nonneg hε t))
    (by linarith) (fun t ht => timeRamp_eq_zero hε ht)).2

/-- The gradient estimate. -/
theorem energy_grad_estimate (H : EnergyHyp U Lam a u F K η Kx T tTop δ) :
    ∫⁻ z in U ×ˢ Ioo T tTop,
        ENNReal.ofReal (η z ^ 2 * deriv (deriv F) (u.toFun z) * vecNormSq (u.grad z)) ≤
      2 * energyBound Lam K F u η T tTop := by
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hεdef
  have hε : ∀ n, 0 < ε n := fun n => by positivity
  set Sn : ℕ → Set (Vec d × ℝ) := fun n => U ×ˢ Ioo T (tTop - 2 * ε n) with hSn
  have hmono : Monotone Sn := by
    intro n m hnm
    have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
    have : ε m ≤ ε n := by
      simp only [hεdef]
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    exact prod_mono subset_rfl (Ioo_subset_Ioo_right (by linarith))
  have hcover : U ×ˢ Ioo T tTop ⊆ ⋃ n, Sn n := by
    rintro ⟨x, t⟩ ⟨hx, ht1, ht2⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < (tTop - t) / 2 by linarith)
    exact mem_iUnion.2 ⟨n, hx, ht1, by simp only [hεdef]; linarith⟩
  calc ∫⁻ z in U ×ˢ Ioo T tTop, _
      ≤ ∫⁻ z in ⋃ n, Sn n, ENNReal.ofReal (η z ^ 2 * deriv (deriv F) (u.toFun z) *
          vecNormSq (u.grad z)) := lintegral_mono_set hcover
    _ = ⨆ n, ∫⁻ z in Sn n, ENNReal.ofReal (η z ^ 2 * deriv (deriv F) (u.toFun z) *
          vecNormSq (u.grad z)) := setLIntegral_iUnion_of_directed _ hmono.directed_le
    _ ≤ 2 * energyBound Lam K F u η T tTop := by
        refine iSup_le fun n => ?_
        have hSnm : MeasurableSet (Sn n) := H.isOpen.measurableSet.prod measurableSet_Ioo
        have hsubS : Sn n ⊆ U ×ˢ Ioo T tTop :=
          prod_mono subset_rfl (Ioo_subset_Ioo_right (by linarith [hε n]))
        have hχ1 : ∀ z ∈ Sn n, timeRamp (tTop - ε n) (ε n) z.2 = 1 := fun z hz =>
          timeRamp_eq_one (hε n) (by linarith [hz.2.2])
        calc ∫⁻ z in Sn n, ENNReal.ofReal (η z ^ 2 * deriv (deriv F) (u.toFun z) *
              vecNormSq (u.grad z))
            = ∫⁻ z in Sn n, 2 * ENNReal.ofReal (1 / 2 * deriv (deriv F) (u.toFun z) *
                vecNormSq (u.grad z) * η z ^ 2 * timeRamp (tTop - ε n) (ε n) z.2) := by
              refine setLIntegral_congr_fun hSnm fun z hz => ?_
              rw [hχ1 z hz, ofReal_eq_two_mul_ofReal_half]
              refine congrArg (fun r => 2 * ENNReal.ofReal r) ?_
              ring
          _ = 2 * ∫⁻ z in Sn n, ENNReal.ofReal (1 / 2 * deriv (deriv F) (u.toFun z) *
                vecNormSq (u.grad z) * η z ^ 2 * timeRamp (tTop - ε n) (ε n) z.2) :=
              lintegral_const_mul' _ _ (by simp)
          _ ≤ 2 * ∫⁻ z in U ×ˢ Ioo T tTop, ENNReal.ofReal (1 / 2 * deriv (deriv F) (u.toFun z) *
                vecNormSq (u.grad z) * η z ^ 2 * timeRamp (tTop - ε n) (ε n) z.2) :=
              mul_le_mul_right (lintegral_mono_set hsubS) 2
          _ ≤ 2 * energyBound Lam K F u η T tTop :=
              mul_le_mul_right (ramp_energy_grad_fixed H (hε n)) 2

end PDE.Parabolic.LocalMax
