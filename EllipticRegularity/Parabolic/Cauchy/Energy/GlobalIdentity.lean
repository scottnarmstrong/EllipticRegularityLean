/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.Cauchy.Energy.Global

/-! # The whole-space Cauchy energy identity -/

@[expose] public section

namespace PDE.Parabolic.Cauchy.Energy

open MeasureTheory Set

/-- The whole-space Cauchy energy identity, in the `ENNReal` form used by the statement. -/
theorem cauchyEnergyIdentity (d : ℕ) (lam Lam : ℝ) (a : ParCoeffField d)
    (s T : ℝ) (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (f : Vec d → ℝ)
    (hf : MemLp f 2 volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) (t : ℝ) (ht : t ∈ Icc s T) :
    (∫⁻ x : Vec d, ENNReal.ofReal (u.toFun (x, t) ^ 2)) +
        2 * ∫⁻ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
          ENNReal.ofReal (vecDot (u.grad z) (matVecMul (a z) (u.grad z)))
      = ∫⁻ x : Vec d, ENNReal.ofReal (f x ^ 2) ∧
    (∫⁻ x : Vec d, ENNReal.ofReal (f x ^ 2)) < ⊤ := by
  let Q : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s t
  let q : Vec d × ℝ → ℝ := fun z =>
    vecDot (u.grad z) (matVecMul (a z) (u.grad z))
  have huInt : Integrable (fun x : Vec d => u.toFun (x, t) ^ 2) volume :=
    cauchy_slice_square_integrable hsT ha f hf u hu ht
  have hfInt : Integrable (fun x : Vec d => f x ^ 2) volume := hf.integrable_sq
  have hqInt : IntegrableOn q Q := by
    change IntegrableOn (cauchyEnergyDensity a u) Q
    exact cauchyEnergyDensity_integrable_Ioc ha u ht
  have hQsub : Q ⊆ (univ : Set (Vec d)) ×ˢ Icc s T := by
    intro z hz
    exact ⟨hz.1, ⟨le_of_lt hz.2.1, hz.2.2.trans ht.2⟩⟩
  have hQmeasure : volume.restrict Q ≤
      volume.restrict ((univ : Set (Vec d)) ×ˢ Icc s T) :=
    Measure.restrict_mono hQsub le_rfl
  have hqNonneg : ∀ᵐ z ∂(volume.restrict Q), 0 ≤ q z := by
    change ∀ᵐ z ∂(volume.restrict Q),
      0 ≤ cauchyEnergyDensity a u z
    exact (cauchyEnergyDensity_nonneg_ae ha u).filter_mono
      (ae_mono hQmeasure)
  have huNonneg : ∀ᵐ x : Vec d ∂volume, 0 ≤ u.toFun (x, t) ^ 2 :=
    ae_of_all _ fun x => sq_nonneg _
  have hfNonneg : ∀ᵐ x : Vec d ∂volume, 0 ≤ f x ^ 2 :=
    ae_of_all _ fun x => sq_nonneg _
  have hU : 0 ≤ ∫ x : Vec d, u.toFun (x, t) ^ 2 := integral_nonneg_of_ae huNonneg
  have hF : 0 ≤ ∫ x : Vec d, f x ^ 2 := integral_nonneg_of_ae hfNonneg
  have hQ : 0 ≤ ∫ z in Q, q z := integral_nonneg_of_ae hqNonneg
  have hUconv : ∫⁻ x : Vec d, ENNReal.ofReal (u.toFun (x, t) ^ 2) =
      ENNReal.ofReal (∫ x : Vec d, u.toFun (x, t) ^ 2) :=
    (ofReal_integral_eq_lintegral_ofReal huInt huNonneg).symm
  have hFconv : ∫⁻ x : Vec d, ENNReal.ofReal (f x ^ 2) =
      ENNReal.ofReal (∫ x : Vec d, f x ^ 2) :=
    (ofReal_integral_eq_lintegral_ofReal hfInt hfNonneg).symm
  have hQconv : ∫⁻ z in Q, ENNReal.ofReal (q z) =
      ENNReal.ofReal (∫ z in Q, q z) :=
    (ofReal_integral_eq_lintegral_ofReal hqInt hqNonneg).symm
  have hreal := cauchy_energy_identity_real hsT ha f hf u hu ht
  have hreal' : (∫ x : Vec d, u.toFun (x, t) ^ 2) +
      2 * ∫ z in Q, q z = ∫ x : Vec d, f x ^ 2 := by
    simpa only [Q, q, cauchyEnergyDensity] using hreal
  have hmap := congrArg ENNReal.ofReal hreal'
  rw [ENNReal.ofReal_add hU (mul_nonneg (by norm_num) hQ),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] at hmap
  constructor
  · simpa only [q, Q, hUconv, hQconv, hFconv, ENNReal.ofReal_ofNat] using hmap
  · rw [hFconv]
    exact ENNReal.ofReal_lt_top

end PDE.Parabolic.Cauchy.Energy
