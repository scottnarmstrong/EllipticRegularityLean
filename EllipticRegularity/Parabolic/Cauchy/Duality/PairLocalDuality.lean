module

public import EllipticRegularity.Parabolic.Cauchy.Duality.PairAdjointBulk

@[expose] public section

namespace PDE.Parabolic.Duality

open MeasureTheory Set
open PDE.Parabolic.Energy

/-- The compactly localized forward/adjoint pairing identity for a time-independent
parabolic cutoff. -/
theorem cauchy_duality_compact_cutoff_identity {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s t : ℝ} (hst : s < t)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s t))
    (f g : Vec d → ℝ) (u w : ParH1Function (univ : Set (Vec d)) (Icc s t))
    (hu : IsCauchySolution a s t f u)
    (hw : IsCauchySolution (parAdjCoeff a (s + t)) s t g w)
    (χ : ParCutoff (univ : Set (Vec d)) (Icc s t))
    (hχt : ∀ z : Vec d × ℝ, parTimeDeriv χ.toFun z = 0) :
    ∃ K : Set (Vec d), ∃ δ0 : ℝ, IsCompact K ∧ 0 < δ0 ∧ δ0 ≤ 1 ∧
      (∀ x τ, τ ∈ Icc s t → x ∉ K → χ.toFun (x, τ) = 0) ∧
      (∫ x in K, χ.toFun (x, t) ^ 2 * u.toFun (x, t) * w.toFun (x, s)) -
          ∫ x in K, χ.toFun (x, s) ^ 2 * u.toFun (x, s) * w.toFun (x, t) =
        -∫ z in K ×ˢ Ioc s t,
          2 * χ.toFun z * ∑ i : Fin d,
            (flux a u z i * w.toFun (z.1, s + t - z.2) -
              flux (parAdjCoeff a (s + t)) w (z.1, s + t - z.2) i *
                u.toFun z) * parSpaceGrad χ.toFun z i := by
  obtain ⟨K, δ0, hKc, hKU, hδ0, hδ1, _, hχzero⟩ :=
    PDE.Parabolic.Energy.exists_collar isOpen_univ χ
  have hχ : ContDiff ℝ 1 χ.toFun := χ.contDiff
  have hχK : ∀ x τ, τ ∈ Icc s t →
      x ∈ Metric.cthickening (2 * δ0) K → x ∉ K → χ.toFun (x, τ) = 0 := by
    intro x τ hτ _ hx
    exact hχzero x (mem_univ x) hx τ hτ
  have haAdj : IsParabolicCoeff lam Lam (parAdjCoeff a (s + t)) univ (Icc s t) :=
    PDE.parAdjCoeff_isParabolicCoeff_core d lam Lam a s t ha
  obtain ⟨D, hDK, hDδ, hDs, hDt, hDuFun, hDφ, hDfields⟩ :=
    cauchy_solution_energy_data_fixed_collar ordConnected_Icc ha u hu.1 hKc
      hδ0 hδ1 (by constructor <;> linarith) (by constructor <;> linarith) hst
      χ.toFun hχ hχK
  obtain ⟨W, hWK, hWδ, hWs, hWt, hWfun, hWφ, hWfields⟩ :=
    cauchy_solution_energy_data_fixed_collar ordConnected_Icc haAdj w hw.1 hKc
      hδ0 hδ1 (by constructor <;> linarith) (by constructor <;> linarith) hst
      χ.toFun hχ hχK
  let E := reverseEnergyData W
  have hKE : D.K = E.K := by simp [E, hDK, hWK, reverseEnergyData]
  have hδE : D.δ0 = E.δ0 := by simp [E, hDδ, hWδ, reverseEnergyData]
  have hsE : D.s = E.s := by simp [E, hDs, hWs, reverseEnergyData]
  have htE : D.t = E.t := by simp [E, hDt, hWt, reverseEnergyData]
  have hbulk := energyData_reverseAdjoint_bulk_cancel a u w D W
    hDs hDt hWs hWt hDfields hWfields
  have hχtD : ∀ z : Vec d × ℝ, parTimeDeriv D.φ z = 0 := by
    simpa only [hDφ] using hχt
  have hcross := energyData_cross_identity_spatial_cutoff D E hKE hδE hsE htE hχtD hbulk
  have hDΩ : ∀ᵐ z ∂(volume.restrict (K ×ˢ Ioc s t)),
      D.Du z = u.grad z ∧ D.G z = flux a u z := by
    have hsub : K ×ˢ Ioc s t ⊆ (univ : Set (Vec d)) ×ˢ Icc s t := by
      rintro ⟨x, τ⟩ ⟨hx, hτ⟩
      exact ⟨mem_univ x, ⟨hτ.1.le, hτ.2⟩⟩
    have h : ∀ᵐ z ∂(volume.restrict (K ×ˢ Ioc s t)),
        D.Du z = u.grad z ∧ D.G z = flux a u z :=
      ae_restrict_of_ae_restrict_of_subset hsub hDfields
    simpa [hDK, hDs, hDt] using h
  let R : Vec d × ℝ → Vec d × ℝ := fun z => (z.1, s + t - z.2)
  have hWref : ∀ᵐ z ∂(volume.restrict (K ×ˢ Ioc s t)),
      W.Du (R z) = w.grad (R z) ∧
        W.G (R z) = flux (parAdjCoeff a (s + t)) w (R z) := by
    have hR := (time_reflection_quasi_measure_preserving d s t).ae hWfields
    have hsub : K ×ˢ Ioc s t ⊆ (univ : Set (Vec d)) ×ˢ Icc s t := by
      rintro ⟨x, τ⟩ ⟨hx, hτ⟩
      exact ⟨mem_univ x, ⟨hτ.1.le, hτ.2⟩⟩
    exact ae_restrict_of_ae_restrict_of_subset hsub hR
  have hEuFun : E.u = fun z => w.toFun (z.1, s + t - z.2) := by
    funext z
    simp [E, reverseEnergyData, hWfun, hWs, hWt]
  have hpoint : ∀ᵐ z ∂(volume.restrict (K ×ˢ Ioc s t)),
      2 * D.φ z * ∑ i : Fin d,
        (D.G z i * E.u z + E.G z i * D.u z) * parSpaceGrad D.φ z i =
      2 * χ.toFun z * ∑ i : Fin d,
        (flux a u z i * w.toFun (R z) -
          flux (parAdjCoeff a (s + t)) w (R z) i * u.toFun z) *
            parSpaceGrad χ.toFun z i := by
    filter_upwards [hDΩ, hWref] with z hd hwz
    have hE := reverseEnergyData_fields W z
    have hEu : E.u z = w.toFun (R z) := by simpa [R] using congrFun hEuFun z
    have hEG : E.G z = -flux (parAdjCoeff a (s + t)) w (R z) := by
      rw [show E.G z = (reverseEnergyData W).G z by rfl, hE.2.2]
      simpa [R, hWs, hWt] using congrArg Neg.neg hwz.2
    have hφD : D.φ = χ.toFun := hDφ
    have hφE : E.φ = χ.toFun := by simp [E, reverseEnergyData, hWφ]
    rw [hDφ, hd.2, hDuFun, hEu, hEG]
    simp only [Pi.neg_apply]
    apply congrArg (fun q : Fin d → ℝ => 2 * χ.toFun z * ∑ i, q i)
    funext i
    ring
  have hcross' :
      (∫ x in K, χ.toFun (x, t) ^ 2 * u.toFun (x, t) * w.toFun (x, s)) -
          ∫ x in K, χ.toFun (x, s) ^ 2 * u.toFun (x, s) * w.toFun (x, t) =
        -∫ z in K ×ˢ Ioc s t,
          2 * χ.toFun z * ∑ i : Fin d,
            (flux a u z i * w.toFun (z.1, s + t - z.2) -
              flux (parAdjCoeff a (s + t)) w (z.1, s + t - z.2) i *
                u.toFun z) * parSpaceGrad χ.toFun z i := by
    have ht0 : s + t - t = s := by ring
    have hs0 : s + t - s = t := by ring
    have hpoint' : ∀ᵐ z ∂(volume.restrict (K ×ˢ Ioc s t)),
        2 * χ.toFun z * ∑ i : Fin d,
          (D.G z i * w.toFun (R z) + E.G z i * u.toFun z) *
            parSpaceGrad χ.toFun z i =
        2 * χ.toFun z * ∑ i : Fin d,
          (flux a u z i * w.toFun (R z) -
            flux (parAdjCoeff a (s + t)) w (R z) i * u.toFun z) *
              parSpaceGrad χ.toFun z i := by
      filter_upwards [hpoint] with z hz
      simpa [hDφ, hEuFun, hDuFun, R] using hz
    rw [hDφ, show D.u = u.toFun by exact hDuFun,
      show E.u = fun z => w.toFun (z.1, s + t - z.2) by
        funext z
        simp [E, reverseEnergyData, hWfun, hWs, hWt]] at hcross
    rw [hDK, hDs, hDt] at hcross
    simp only [ht0, hs0] at hcross
    rw [hcross]
    congr 1
    exact integral_congr_ae hpoint'
  have hχsupport : ∀ x τ, τ ∈ Icc s t → x ∉ K → χ.toFun (x, τ) = 0 := by
    intro x τ hτ hx
    exact hχzero x (mem_univ x) hx τ hτ
  exact ⟨K, δ0, hKc, hδ0, hδ1, hχsupport, hcross'⟩

end PDE.Parabolic.Duality
