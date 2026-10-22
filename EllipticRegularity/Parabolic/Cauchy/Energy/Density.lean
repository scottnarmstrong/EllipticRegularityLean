/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.Energy.Result

/-! # Integrability and sign of the whole-space energy density -/

@[expose] public section

namespace PDE.Parabolic.Cauchy.Energy

open MeasureTheory Set

/-- The quadratic energy density in the global Cauchy identity. -/
noncomputable def cauchyEnergyDensity {d : ℕ} {I : Set ℝ} (a : ParCoeffField d)
    (u : ParH1Function (univ : Set (Vec d)) I) (z : Vec d × ℝ) : ℝ :=
  vecDot (u.grad z) (matVecMul (a z) (u.grad z))

theorem cauchyEnergyDensity_integrable {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ}
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T)) :
    IntegrableOn (cauchyEnergyDensity a u) ((univ : Set (Vec d)) ×ˢ Icc s T) := by
  change Integrable (cauchyEnergyDensity a u)
    (volume.restrict ((univ : Set (Vec d)) ×ˢ Icc s T))
  unfold cauchyEnergyDensity vecDot matVecMul
  refine integrable_finsetSum _ fun i _ => ?_
  change Integrable
    ((fun z : Vec d × ℝ => u.grad z i) *
      fun z => ∑ j, a z i j * u.grad z j)
    (volume.restrict ((univ : Set (Vec d)) ×ˢ Icc s T))
  have hflux := PDE.Parabolic.Energy.flux_memLp ha u i
  simpa only [PDE.Parabolic.Energy.flux_apply] using
    (u.gradMemL2 i).integrable_mul hflux

theorem cauchyEnergyDensity_nonneg_ae {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ}
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T)) :
    ∀ᵐ z ∂(volume.restrict ((univ : Set (Vec d)) ×ˢ Icc s T)),
      0 ≤ cauchyEnergyDensity a u z := by
  filter_upwards [ha.elliptic] with z hz
  exact (mul_nonneg hz.lam_pos.le (vecNormSq_nonneg _)).trans (hz.coercive _)

end PDE.Parabolic.Cauchy.Energy
