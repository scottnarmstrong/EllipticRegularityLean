/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.Cauchy.Lions.ClosureData
public import EllipticRegularity.Parabolic.Cauchy.Lions.EnergyFields
public import EllipticRegularity.Parabolic.Cauchy.Lions.InitialPairingTransfer

/-! # Transfer of the Lions weak equation to an assembled representative -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace PDE.Parabolic.Lions

/-- The raw Lions weak equation transfers to a `ParH1Function` whose value and gradient fields
agree almost everywhere with the rescaled Lions energy fields. -/
theorem cauchyEnergyFields_transfer_weakSolution
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 (volume : Measure (Vec d)))
    (u : CauchyX d s T)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (W : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hWae : W.toFun =ᵐ[slabMeasure d s T] cauchyEnergyValue u)
    (hGae : ∀ i : Fin d, (fun z => W.grad z i) =ᵐ[slabMeasure d s T]
      (fun z => cauchyEnergyGradient u z i)) :
    IsParabolicWeakSolution a (univ : Set (Vec d)) (Icc s T) W := by
  intro φ
  have hraw := cauchyLions_energyWeakForm hsT ha f hf u hrep φ
  have hGaeAll : ∀ᵐ z ∂(slabMeasure d s T), ∀ i : Fin d,
      W.grad z i = cauchyEnergyGradient u z i := ae_all_iff.2 hGae
  have hFields : (fun z => parWeakIntegrand a W φ.toFun z) =ᵐ[
      slabMeasure d s T] (fun z =>
        -(cauchyEnergyValue u z * parTimeDeriv φ.toFun z) +
          vecDot (matVecMul (a z) (cauchyEnergyGradient u z))
            (parSpaceGrad φ.toFun z)) := by
    filter_upwards [hWae, hGaeAll] with z hval hgrad
    have hgradVec : W.grad z = cauchyEnergyGradient u z := by
      ext i
      exact hgrad i
    simp [parWeakIntegrand, hval, hgradVec]
  have hFields' : (fun z => parWeakIntegrand a W φ.toFun z) =ᵐ[
      (volume : Measure (Vec d × ℝ)).restrict ((univ : Set (Vec d)) ×ˢ Icc s T)]
        (fun z =>
          -(cauchyEnergyValue u z * parTimeDeriv φ.toFun z) +
            vecDot (matVecMul (a z) (cauchyEnergyGradient u z))
              (parSpaceGrad φ.toFun z)) := by
    simpa only [slabMeasure] using hFields
  refine ⟨?_, ?_⟩
  · change Integrable (fun z => parWeakIntegrand a W φ.toFun z)
      (volume.restrict ((univ : Set (Vec d)) ×ˢ Icc s T))
    exact hraw.1.integrable.congr hFields'.symm
  · calc
      ∫ z in (univ : Set (Vec d)) ×ˢ Icc s T, parWeakIntegrand a W φ.toFun z =
          ∫ z in (univ : Set (Vec d)) ×ˢ Icc s T,
            -(cauchyEnergyValue u z * parTimeDeriv φ.toFun z) +
              vecDot (matVecMul (a z) (cauchyEnergyGradient u z))
                (parSpaceGrad φ.toFun z) := integral_congr_ae hFields'
      _ = 0 := hraw.2

/-- A representative of both rescaled Lions energy fields is a Cauchy energy solution. The
substantive existence task is to construct `W` with the displayed almost-everywhere identities. -/
theorem cauchyEnergyRepresentative_isCauchySolution
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 (volume : Measure (Vec d)))
    (u : CauchyX d s T) {u₀ : CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (W : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hWae : W.toFun =ᵐ[slabMeasure d s T] cauchyEnergyValue u)
    (hGae : ∀ i : Fin d, (fun z => W.grad z i) =ᵐ[slabMeasure d s T]
      (fun z => cauchyEnergyGradient u z i)) :
    IsCauchySolution a s T f W := by
  refine ⟨cauchyEnergyFields_transfer_weakSolution hsT ha f hf u hrep W hWae hGae, ?_⟩
  exact cauchyInitial_ae_of_ae_representation hsT ha f hf u hclose hrep W hWae

end PDE.Parabolic.Lions
