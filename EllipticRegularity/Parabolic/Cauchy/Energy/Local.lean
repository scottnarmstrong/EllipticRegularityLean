/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.Cauchy.Energy.Cutoff
public import EllipticRegularity.Parabolic.Energy.Result

/-! # Local energy identity with the Cauchy exhaustion cutoffs -/

@[expose] public section

namespace PDE.Parabolic.Cauchy.Energy

open MeasureTheory Set

theorem cauchy_cutoff_energy_identity {d : ℕ} {lam Lam : ℝ} {a : ParCoeffField d}
    {s T : ℝ} (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsParabolicWeakSolution a univ (Icc s T) u) (R : ℝ) (hR : 0 < R)
    {t : ℝ} (ht : t ∈ Icc s T) (hst : s < t) :
    ((1 / 2 : ℝ) * ∫ x in (univ : Set (Vec d)),
        (cauchyParabolicCutoff s T R hR).toFun (x, t) ^ 2 * u.toFun (x, t) ^ 2) -
      (1 / 2 : ℝ) * ∫ x in (univ : Set (Vec d)),
        (cauchyParabolicCutoff s T R hR).toFun (x, s) ^ 2 * u.toFun (x, s) ^ 2 =
    -∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
      vecDot (matVecMul (a z) (u.grad z))
        ((cauchyParabolicCutoff s T R hR).toFun z ^ 2 • u.grad z +
          (2 * (cauchyParabolicCutoff s T R hR).toFun z * u.toFun z) •
            parSpaceGrad (cauchyParabolicCutoff s T R hR).toFun z) := by
  have hlocal := PDE.Parabolic.energy_identity d lam Lam univ isOpen_univ
    (Icc s T) Set.ordConnected_Icc a ha u hu (cauchyParabolicCutoff s T R hR)
  obtain ⟨_, _, hslab⟩ := hlocal
  obtain ⟨_, _, hidentity⟩ := hslab s t ⟨le_rfl, hsT.le⟩ ht hst
  have hzero : ∀ z : Vec d × ℝ,
      parTimeDeriv (cauchyParabolicCutoff s T R hR).toFun z = 0 := by
    rintro ⟨x, τ⟩
    exact cauchyParabolicCutoff_timeDeriv_eq_zero s T R hR x τ
  have hidentity' := hidentity
  simp only [hzero, mul_zero, integral_zero, zero_sub] at hidentity'
  exact hidentity'

end PDE.Parabolic.Cauchy.Energy
