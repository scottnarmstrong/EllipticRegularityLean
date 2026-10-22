/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.Chain.ScaleLimit
public import EllipticRegularity.Parabolic.Chain.SmoothSolution
public import EllipticRegularity.Parabolic.Energy.Bridge

/-! # Renormalization for H¹-parabolic weak solutions -/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.Chain

open MeasureTheory Set Filter Topology PDE PDE.Parabolic.Energy

variable {d : ℕ} {lam Lam : ℝ} {U : Set (Vec d)} {I : Set ℝ}
  {a : ParCoeffField d}

/-- The nonlinear renormalization identity for an H¹-parabolic weak solution.
The test has compact support in the interior subslab `(s,t)`, which is the
support condition needed to use the weak equation and eliminate time endpoint
terms. -/
theorem weak_solution_renormalization_H1 (hU : IsOpen U) (hI : I.OrdConnected)
    (ha : IsParabolicCoeff lam Lam a U I) (u : ParH1Function U I)
    (hu : IsParabolicWeakSolution a U I u)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hFLip : ∃ C : NNReal, LipschitzWith C F)
    (hF'bound : ∃ C : NNReal, ∀ s, |deriv F s| ≤ C)
    (hF''bound : ∃ C : NNReal, ∀ s, |deriv (deriv F) s| ≤ C)
    (φ : ParTestFunction U (interior I)) {s t : ℝ}
    (hs : s ∈ I) (ht : t ∈ I) (hst : s < t)
    (hsupp : tsupport φ.toFun ⊆ U ×ˢ Ioo s t) :
    IntegrableOn (renormalizedIntegrand a u F φ.toFun) (U ×ˢ Ioc s t) ∧
      ∫ z in U ×ˢ Ioc s t, renormalizedIntegrand a u F φ.toFun z = 0 := by
  let ψ : ParCutoff U I :=
    { toFun := φ.toFun
      contDiff := φ.contDiff
      compact_support := ⟨tsupport φ.toFun, φ.hasCompactSupport.isCompact,
        (φ.tsupport_subset).trans (prod_mono subset_rfl interior_subset),
        fun z hz hznot => image_eq_zero_of_notMem_tsupport hznot⟩ }
  obtain ⟨D, hDu, hDφ, hDs, hDt, hKU, hDφzero, hae⟩ :=
    PDE.Parabolic.Energy.exists_data hU hI ha u hu ψ hs ht hst
  have hφoutsideD : ∀ x, x ∉ D.K → ∀ τ ∈ Icc D.s D.t, D.φ (x, τ) = 0 := by
    intro x hx τ hτ
    have hτ' : τ ∈ Icc s t := by simpa [hDs, hDt] using hτ
    by_cases hxU : x ∈ U
    · simpa [hDφ, ψ] using hDφzero x hxU hx τ (hI.out hs ht hτ')
    · have hnot : (x, τ) ∉ tsupport φ.toFun := fun hz => hxU (hsupp hz).1
      simpa [hDφ, ψ] using image_eq_zero_of_notMem_tsupport hnot
  have hφsD : ∀ x, D.φ (x, D.s) = 0 := by
    intro x
    have hnot : (x, s) ∉ tsupport φ.toFun := by
      intro hz
      have ht' := (hsupp hz).2
      simp only [mem_Ioo] at ht'
      exact (lt_irrefl s) ht'.1
    simpa [hDφ, hDs, ψ] using image_eq_zero_of_notMem_tsupport hnot
  have hφtD : ∀ x, D.φ (x, D.t) = 0 := by
    intro x
    have hnot : (x, t) ∉ tsupport φ.toFun := by
      intro hz
      have ht' := (hsupp hz).2
      simp only [mem_Ioo] at ht'
      exact (lt_irrefl t) ht'.2
    simpa [hDφ, hDt, ψ] using image_eq_zero_of_notMem_tsupport hnot
  obtain ⟨hDataInt, hDataZero⟩ :=
    Energy.Data.renormalization_identity D F hF hFLip
    hF'bound hF''bound hφoutsideD hφsD hφtD
  have hslab : D.K ×ˢ Ioc s t ⊆ U ×ˢ I :=
    prod_mono hKU ((Ioc_subset_Icc_self).trans (hI.out hs ht))
  have haeK : ∀ᵐ z ∂(volume.restrict (D.K ×ˢ Ioc s t)),
      (∀ i, D.G z i = PDE.Parabolic.Energy.flux a u z i) ∧
        ∀ i, D.Du z i = u.grad z i :=
    ae_restrict_of_ae_restrict_of_subset hslab hae
  have hrenAE : dataRenormalizedIntegrand D F =ᵐ[volume.restrict (D.K ×ˢ Ioc s t)]
      renormalizedIntegrand a u F φ.toFun := by
    filter_upwards [haeK] with z hz
    have hG (i : Fin d) : D.G z i = ∑ j, a z i j * u.grad z j := by
      simpa [PDE.Parabolic.Energy.flux, matVecMul] using hz.1 i
    have hDu' (i : Fin d) : D.Du z i = u.grad z i := hz.2 i
    have hlin : ∑ i, deriv F (u.toFun z) * parSpaceGrad φ.toFun z i * D.G z i =
        deriv F (u.toFun z) * vecDot (matVecMul (a z) (u.grad z))
          (parSpaceGrad φ.toFun z) := by
      calc
        _ = ∑ i, deriv F (u.toFun z) *
            (matVecMul (a z) (u.grad z) i * parSpaceGrad φ.toFun z i) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [hG i, matVecMul_apply]
              ring
        _ = deriv F (u.toFun z) *
            ∑ i, matVecMul (a z) (u.grad z) i * parSpaceGrad φ.toFun z i := by
              rw [← Finset.mul_sum]
        _ = deriv F (u.toFun z) * vecDot (matVecMul (a z) (u.grad z))
            (parSpaceGrad φ.toFun z) := by simp [vecDot]
    have hquad : ∑ i, deriv (deriv F) (u.toFun z) * φ.toFun z *
        D.G z i * D.Du z i = deriv (deriv F) (u.toFun z) *
          vecDot (matVecMul (a z) (u.grad z)) (u.grad z) * φ.toFun z := by
      calc
        _ = ∑ i, (deriv (deriv F) (u.toFun z) * φ.toFun z) *
            (matVecMul (a z) (u.grad z) i * u.grad z i) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [hG i, hDu' i, matVecMul_apply]
              ring
        _ = (deriv (deriv F) (u.toFun z) * φ.toFun z) *
            ∑ i, matVecMul (a z) (u.grad z) i * u.grad z i := by
              rw [← Finset.mul_sum]
        _ = (deriv (deriv F) (u.toFun z) * φ.toFun z) *
            vecDot (matVecMul (a z) (u.grad z)) (u.grad z) := by simp [vecDot]
        _ = _ := by ring
    simp only [dataRenormalizedIntegrand, renormalizedIntegrand, hDu, hDφ, ψ]
    rw [Finset.sum_add_distrib, hquad, hlin]
    ring
  have hrenK : IntegrableOn (renormalizedIntegrand a u F φ.toFun)
      (D.K ×ˢ Ioc s t) := by
    have hDataInt' : Integrable (dataRenormalizedIntegrand D F)
        (volume.restrict (D.K ×ˢ Ioc s t)) := by
      simpa [Data.μP, hDs, hDt] using hDataInt
    change Integrable (renormalizedIntegrand a u F φ.toFun)
      (volume.restrict (D.K ×ˢ Ioc s t))
    exact hDataInt'.congr hrenAE
  have hIoo : Ioo s t ⊆ interior I :=
    interior_maximal ((Ioo_subset_Icc_self).trans (hI.out hs ht)) isOpen_Ioo
  have hφzeroOutside : ∀ x, x ∉ D.K → ∀ τ ∈ I, φ.toFun (x, τ) = 0 := by
    intro x hx τ hτ
    by_cases hxU : x ∈ U
    · have h := hDφzero x hxU hx τ hτ
      simpa [hDφ] using h
    · apply image_eq_zero_of_notMem_tsupport
      intro hz
      exact hxU (hsupp hz).1
  have hrenzeroOutside : ∀ z ∈ (U ×ˢ Ioc s t) \ (D.K ×ˢ Ioc s t),
      renormalizedIntegrand a u F φ.toFun z = 0 := by
    rintro ⟨x, τ⟩ ⟨⟨hxU, hτ⟩, hnot⟩
    have hxK : x ∉ D.K := by
      intro hxK
      exact hnot ⟨hxK, hτ⟩
    have hτI : τ ∈ I := (hI.out hs ht) ⟨hτ.1.le, hτ.2⟩
    have hφvalue : φ.toFun (x, τ) = 0 := hφzeroOutside x hxK τ hτI
    have hfd : fderiv ℝ φ.toFun (x, τ) = 0 := by
      rcases lt_or_eq_of_le hτ.2 with hτt | hτeq
      · have hopen : IsOpen (D.Kᶜ ×ˢ interior I) :=
          D.hK.isClosed.isOpen_compl.prod isOpen_interior
        have hlocal : φ.toFun =ᶠ[nhds (x, τ)] fun _ => (0 : ℝ) :=
          Filter.eventually_of_mem (hopen.mem_nhds ⟨hxK, hIoo ⟨hτ.1, hτt⟩⟩)
            (fun z hz => hφzeroOutside z.1 hz.1 z.2 (interior_subset hz.2))
        rw [hlocal.fderiv_eq]
        simp
      · have hnotSupport : (x, τ) ∉ tsupport φ.toFun := by
          intro hz
          have hτmem : τ ∈ Ioo s t := (hsupp hz).2
          have hτlt : τ < t := hτmem.2
          have hτeq' : τ = t := by simpa using hτeq
          rw [hτeq'] at hτlt
          exact (lt_irrefl t) hτlt
        exact fderiv_of_notMem_tsupport ℝ hnotSupport
    have htimezero : parTimeDeriv φ.toFun (x, τ) = 0 := by
      simp [parTimeDeriv, hfd]
    have hgradzero : parSpaceGrad φ.toFun (x, τ) = 0 := by
      ext i
      simp [parSpaceGrad, hfd]
    unfold renormalizedIntegrand
    rw [htimezero, hgradzero, hφvalue]
    simp [vecDot]
  have hrenU : IntegrableOn (renormalizedIntegrand a u F φ.toFun)
      (U ×ˢ Ioc s t) :=
    hrenK.of_forall_sdiff_eq_zero (hU.measurableSet.prod measurableSet_Ioc) hrenzeroOutside
  have hIntegralU : ∫ z in U ×ˢ Ioc s t, renormalizedIntegrand a u F φ.toFun z =
      ∫ z in D.K ×ˢ Ioc s t, renormalizedIntegrand a u F φ.toFun z := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (hU.measurableSet.prod measurableSet_Ioc) (prod_mono hKU subset_rfl)]
    exact hrenzeroOutside
  have hIntegralK : ∫ z in D.K ×ˢ Ioc s t, renormalizedIntegrand a u F φ.toFun z = 0 := by
    have hEq : ∫ z in D.K ×ˢ Ioc s t, dataRenormalizedIntegrand D F z =
        ∫ z in D.K ×ˢ Ioc s t, renormalizedIntegrand a u F φ.toFun z := by
      exact integral_congr_ae hrenAE
    calc
      _ = ∫ z in D.K ×ˢ Ioc s t, dataRenormalizedIntegrand D F z := hEq.symm
      _ = 0 := by simpa [Data.μP, hDs, hDt] using hDataZero
  exact ⟨hrenU, hIntegralU.trans hIntegralK⟩

end PDE.Parabolic.Chain
