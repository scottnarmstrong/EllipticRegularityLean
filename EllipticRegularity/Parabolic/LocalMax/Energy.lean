/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.LocalMax.EnergyGrad
public import EllipticRegularity.Parabolic.LocalMax.EnergyTime

/-! # The power energy estimate for nonnegative weak solutions

Facade for the pieces `EnergyRamp` (fixed-ramp inequality, `energyBound`), `EnergyGrad`
(gradient part) and `EnergyTime` (time-slice part).
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.LocalMax

open MeasureTheory Set PDE

theorem power_energy_estimate {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U) {Lam : ℝ}
    {a : ParCoeffField d} (ha : IsParabolicCoeff 1 Lam a U (Ioc (-1 : ℝ) 0))
    (u : ParH1Function U (Ioc (-1 : ℝ) 0))
    (hu : IsParabolicWeakSolution a U (Ioc (-1 : ℝ) 0) u)
    (hpos : ∀ᵐ z ∂(volume.restrict (U ×ˢ Ioc (-1 : ℝ) 0)), 0 ≤ u.toFun z)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hF'' : ∃ C : NNReal, ∀ s, |deriv (deriv F) s| ≤ C)
    {K : ℝ} (hK : 0 ≤ K)
    (hFs : ∀ s, 0 ≤ s → 0 ≤ F s ∧ 0 ≤ deriv (deriv F) s ∧
      deriv F s ^ 2 ≤ K * deriv (deriv F) s * F s)
    (η : Vec d × ℝ → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) {Kx : Set (Vec d)} (hKx : IsCompact Kx)
    (hKxU : Kx ⊆ U) (hηx : ∀ x t, x ∉ Kx → η (x, t) = 0)
    {T tTop δ : ℝ} (hT : -1 < T) (hTt : T < tTop) (htTop : tTop ≤ 0) (hδ : 0 < δ)
    (hηt : ∀ x t, t ≤ T + δ → η (x, t) = 0) :
    (∀ᵐ t ∂(volume.restrict (Ioo T tTop)),
      ∫⁻ x in U, ENNReal.ofReal (η (x, t) ^ 2 * F (u.toFun (x, t))) ≤
        energyBound Lam K F u η T tTop) ∧
    ∫⁻ z in U ×ˢ Ioo T tTop,
        ENNReal.ofReal (η z ^ 2 * deriv (deriv F) (u.toFun z) * vecNormSq (u.grad z)) ≤
      2 * energyBound Lam K F u η T tTop :=
  have H : EnergyHyp U Lam a u F K η Kx T tTop δ :=
    ⟨hU, ha, hu, hpos, hF, hF'', hK, hFs, hη, hKx, hKxU, hηx, hT, hTt, htTop, hδ, hηt⟩
  ⟨energy_time_estimate H, energy_grad_estimate H⟩

end PDE.Parabolic.LocalMax
