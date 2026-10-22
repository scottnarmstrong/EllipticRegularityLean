module

public import EllipticRegularity.Parabolic.Cauchy.Duality.PairDataCutoff
public import EllipticRegularity.Parabolic.Cauchy.Duality.AdjCoeff
public import EllipticRegularity.Parabolic.CauchyDef
public import EllipticRegularity.Ch4.GreenDecay.Algebra

@[expose] public section

namespace PDE.Parabolic.Duality

open MeasureTheory Set
open PDE.Parabolic.Energy

/-- The forward and reflected-transpose fluxes cancel in the bulk of the polarized
product identity. -/
theorem energyData_reverseAdjoint_bulk_cancel {d : ℕ} {s t : ℝ}
    (a : ParCoeffField d)
    (u w : ParH1Function (univ : Set (Vec d)) (Icc s t))
    (D W : Energy.Data d)
    (hDs : D.s = s) (hDt : D.t = t)
    (hWs : W.s = s) (hWt : W.t = t)
    (hD : ∀ᵐ z ∂(volume.restrict (univ ×ˢ Icc s t)),
      D.Du z = u.grad z ∧ D.G z = flux a u z)
    (hW : ∀ᵐ z ∂(volume.restrict (univ ×ˢ Icc s t)),
      W.Du z = w.grad z ∧
        W.G z = flux (parAdjCoeff a (s + t)) w z) :
    ∀ᵐ z ∂(volume.restrict (D.K ×ˢ Ioc D.s D.t)),
      ∑ i : Fin d,
        (D.G z i * (reverseEnergyData W).Du z i +
          (reverseEnergyData W).G z i * D.Du z i) = 0 := by
  let R : Vec d × ℝ → Vec d × ℝ := fun z => (z.1, s + t - z.2)
  have hDΩ : ∀ᵐ z ∂(volume.restrict (D.K ×ˢ Ioc D.s D.t)),
      D.Du z = u.grad z ∧ D.G z = flux a u z := by
    have hsub : D.K ×ˢ Ioc D.s D.t ⊆ (univ : Set (Vec d)) ×ˢ Icc s t := by
      rintro ⟨x, τ⟩ ⟨hx, hτ⟩
      rw [hDs, hDt] at hτ
      exact ⟨trivial, ⟨hτ.1.le, hτ.2⟩⟩
    exact ae_restrict_of_ae_restrict_of_subset hsub hD
  have hWref : ∀ᵐ z ∂(volume.restrict (D.K ×ˢ Ioc D.s D.t)),
      W.Du (R z) = w.grad (R z) ∧
        W.G (R z) = flux (parAdjCoeff a (s + t)) w (R z) := by
    have hR := (time_reflection_quasi_measure_preserving d s t).ae hW
    have hsub : D.K ×ˢ Ioc D.s D.t ⊆ (univ : Set (Vec d)) ×ˢ Icc s t := by
      rintro ⟨x, τ⟩ ⟨hx, hτ⟩
      rw [hDs, hDt] at hτ
      exact ⟨trivial, ⟨hτ.1.le, hτ.2⟩⟩
    exact ae_restrict_of_ae_restrict_of_subset hsub hR
  filter_upwards [hDΩ, hWref] with z hd hw
  have hrev := reverseEnergyData_fields W z
  have hEgradient : (reverseEnergyData W).Du z = w.grad (R z) := by
    rw [hrev.2.1]
    simpa [R, hWs, hWt] using hw.1
  have hEflux : (reverseEnergyData W).G z =
      -flux (parAdjCoeff a (s + t)) w (R z) := by
    rw [hrev.2.2]
    simpa [R, hWs, hWt] using congrArg Neg.neg hw.2
  have hcoeff : parAdjCoeff a (s + t) (R z) = matTranspose (a z) := by
    simp [R, parAdjCoeff, matTranspose]
  have hdot :
      vecDot (matVecMul (a z) (u.grad z)) (w.grad (R z)) =
        vecDot (matVecMul (matTranspose (a z)) (w.grad (R z))) (u.grad z) := by
    calc
      _ = vecDot (u.grad z) (matVecMul (matTranspose (a z)) (w.grad (R z))) :=
        (PDE.Ch4GreenDecay.vecDot_matVecMul_transpose''
          (u.grad z) (w.grad (R z)) (a z)).symm
      _ = _ := vecDot_comm _ _
  calc
    ∑ i : Fin d,
        (D.G z i * (reverseEnergyData W).Du z i +
          (reverseEnergyData W).G z i * D.Du z i) =
      ∑ i : Fin d,
        (flux a u z i * w.grad (R z) i -
          flux (parAdjCoeff a (s + t)) w (R z) i * u.grad z i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hd.2, hd.1, hEgradient, hEflux]
      simp only [Pi.neg_apply]
      ring
    _ = vecDot (matVecMul (a z) (u.grad z)) (w.grad (R z)) -
        vecDot (matVecMul (matTranspose (a z)) (w.grad (R z))) (u.grad z) := by
      simp [vecDot, flux, matVecMul, matTranspose, hcoeff, Finset.sum_sub_distrib]
    _ = 0 := by rw [hdot]; ring

end PDE.Parabolic.Duality
