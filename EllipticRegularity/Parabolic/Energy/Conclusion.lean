module

public import EllipticRegularity.Parabolic.Energy.Bridge
public import EllipticRegularity.Parabolic.Energy.Integrable
public import EllipticRegularity.Parabolic.Energy.Primitive

/-!
# The energy identity for `H¹_par` weak solutions (assembly)
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.Energy

open MeasureTheory Set Filter Topology Metric PDE PDE.Parabolic.WeakSlice

section Conclusion

variable {d : ℕ} {lam Lam : ℝ} {U : Set (Vec d)} {I : Set ℝ} {a : ParCoeffField d}

/-- The integrand `∇u · ∇(φ² u)`-type term of the energy identity (Lemma 5.6). -/
theorem vecDot_eq_sum (a : ParCoeffField d) (u : ParH1Function U I) (φ : Vec d × ℝ → ℝ)
    (z : Vec d × ℝ) :
    vecDot (matVecMul (a z) (u.grad z))
        (φ z ^ 2 • u.grad z + (2 * φ z * u.toFun z) • parSpaceGrad φ z) =
      ∑ i, flux a u z i * (φ z ^ 2 * u.grad z i + 2 * φ z * u.toFun z * parSpaceGrad φ z i) := by
  simp [vecDot, flux]

/-- Part (3) of the energy identity, for one `s < t`. -/
theorem slab_conclusion (hU : IsOpen U) (hI : I.OrdConnected)
    (ha : IsParabolicCoeff lam Lam a U I) (u : ParH1Function U I)
    (hu : IsParabolicWeakSolution a U I u) (φ : ParCutoff U I) {s t : ℝ} (hs : s ∈ I)
    (ht : t ∈ I) (hst : s < t) :
    IntegrableOn (fun z => u.toFun z ^ 2 * φ.toFun z * parTimeDeriv φ.toFun z)
        (U ×ˢ Ioc s t) ∧
      IntegrableOn (fun z => vecDot (matVecMul (a z) (u.grad z))
          (φ.toFun z ^ 2 • u.grad z + (2 * φ.toFun z * u.toFun z) • parSpaceGrad φ.toFun z))
          (U ×ˢ Ioc s t) ∧
      ((1 / 2 : ℝ) * ∫ x in U, φ.toFun (x, t) ^ 2 * u.toFun (x, t) ^ 2) -
          (1 / 2 : ℝ) * ∫ x in U, φ.toFun (x, s) ^ 2 * u.toFun (x, s) ^ 2 =
        (∫ z in U ×ˢ Ioc s t, u.toFun z ^ 2 * φ.toFun z * parTimeDeriv φ.toFun z) -
          ∫ z in U ×ˢ Ioc s t, vecDot (matVecMul (a z) (u.grad z))
            (φ.toFun z ^ 2 • u.grad z + (2 * φ.toFun z * u.toFun z) • parSpaceGrad φ.toFun z) := by
  obtain ⟨D, hDu, hDφ, hDs, hDt, hKU, hφ0, hae⟩ := exists_data hU hI ha u hu φ hs ht hst
  have hIcc : Icc s t ⊆ I := hI.out hs ht
  have hIoc : Ioc s t ⊆ I := Ioc_subset_Icc_self.trans hIcc
  have key := D.energy_identity
  have hA := D.integrable_A
  have hB := D.integrable_B
  unfold Data.μP at key hA hB
  rw [hDu, hDφ, hDs, hDt] at key hA hB
  have hmeas : MeasurableSet (U ×ˢ Ioc s t) := hU.measurableSet.prod measurableSet_Ioc
  have hsub : D.K ×ˢ Ioc s t ⊆ U ×ˢ Ioc s t := prod_mono hKU subset_rfl
  have hvan : ∀ z ∈ U ×ˢ Ioc s t \ D.K ×ˢ Ioc s t, φ.toFun z = 0 := by
    rintro ⟨x, τ⟩ ⟨⟨hx, hτ⟩, hn⟩
    exact hφ0 x hx (fun h => hn ⟨h, hτ⟩) τ (hIoc hτ)
  have haeS : ∀ᵐ z ∂(volume.restrict (D.K ×ˢ Ioc s t)),
      ∑ i, D.G z i * (φ.toFun z ^ 2 * D.Du z i + 2 * φ.toFun z * u.toFun z *
        parSpaceGrad φ.toFun z i) =
      vecDot (matVecMul (a z) (u.grad z))
        (φ.toFun z ^ 2 • u.grad z + (2 * φ.toFun z * u.toFun z) • parSpaceGrad φ.toFun z) := by
    have hsl : D.K ×ˢ Ioc s t ⊆ U ×ˢ I := prod_mono hKU hIoc
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsl hae] with z hz
    rw [vecDot_eq_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hz.1 i, hz.2 i]
  have hA1 : IntegrableOn (fun z => u.toFun z ^ 2 * φ.toFun z * parTimeDeriv φ.toFun z)
      (D.K ×ˢ Ioc s t) := hA
  have hA' : IntegrableOn (fun z => u.toFun z ^ 2 * φ.toFun z * parTimeDeriv φ.toFun z)
      (U ×ˢ Ioc s t) :=
    hA1.of_forall_sdiff_eq_zero hmeas fun z hz => by rw [hvan z hz]; ring
  have hB1 : IntegrableOn (fun z => vecDot (matVecMul (a z) (u.grad z))
      (φ.toFun z ^ 2 • u.grad z + (2 * φ.toFun z * u.toFun z) • parSpaceGrad φ.toFun z))
      (D.K ×ˢ Ioc s t) := hB.congr haeS
  have hB' : IntegrableOn (fun z => vecDot (matVecMul (a z) (u.grad z))
      (φ.toFun z ^ 2 • u.grad z + (2 * φ.toFun z * u.toFun z) • parSpaceGrad φ.toFun z))
      (U ×ˢ Ioc s t) :=
    hB1.of_forall_sdiff_eq_zero hmeas fun z hz => by simp [vecDot, hvan z hz]
  refine ⟨hA', hB', ?_⟩
  have e1 : ∀ τ ∈ I, ∫ x in U, φ.toFun (x, τ) ^ 2 * u.toFun (x, τ) ^ 2 =
      ∫ x in D.K, φ.toFun (x, τ) ^ 2 * u.toFun (x, τ) ^ 2 := by
    intro τ hτ
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hKU fun x hx => ?_
    rw [hφ0 x hx.1 hx.2 τ hτ]; ring
  have e2 : ∫ z in U ×ˢ Ioc s t, u.toFun z ^ 2 * φ.toFun z * parTimeDeriv φ.toFun z =
      ∫ z in D.K ×ˢ Ioc s t, u.toFun z ^ 2 * φ.toFun z * parTimeDeriv φ.toFun z := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeas hsub fun z hz => ?_
    rw [hvan z hz]; ring
  have e3 : ∫ z in U ×ˢ Ioc s t, vecDot (matVecMul (a z) (u.grad z))
        (φ.toFun z ^ 2 • u.grad z + (2 * φ.toFun z * u.toFun z) • parSpaceGrad φ.toFun z) =
      ∫ z in D.K ×ˢ Ioc s t, ∑ i, D.G z i * (φ.toFun z ^ 2 * D.Du z i + 2 * φ.toFun z *
        u.toFun z * parSpaceGrad φ.toFun z i) := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeas hsub]
    · exact (integral_congr_ae haeS).symm
    · intro z hz
      simp [vecDot, hvan z hz]
  rw [e1 t ht, e1 s hs, e2, e3]
  exact key

/-- Part (1) of the energy identity. -/
theorem slice_integrable (hU : IsOpen U) (u : ParH1Function U I) (φ : ParCutoff U I) {t : ℝ}
    (ht : t ∈ I) :
    Integrable (fun x => φ.toFun (x, t) ^ 2 * u.toFun (x, t) ^ 2) (volume.restrict U) := by
  obtain ⟨K, δ0, hKc, hKU, -, -, -, hφ0⟩ := exists_collar hU φ
  have hφc : Continuous fun x => φ.toFun (x, t) ^ 2 :=
    (φ.contDiff.continuous.comp (continuous_id.prodMk continuous_const)).pow 2
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hφc.continuousOn
  have hu2 : MemLp (fun x => u.toFun (x, t)) 2 (volume.restrict K) := u.sliceL2loc t ht K hKc hKU
  have hK : IntegrableOn (fun x => φ.toFun (x, t) ^ 2 * u.toFun (x, t) ^ 2) K := by
    refine (hu2.integrable_sq).bdd_mul hφc.aestronglyMeasurable (c := M) ?_
    exact (ae_restrict_iff' hKc.measurableSet).2 (Filter.Eventually.of_forall fun x hx => by
      simpa using hM x hx)
  refine hK.of_forall_sdiff_eq_zero hU.measurableSet fun x hx => ?_
  rw [hφ0 x hx.1 hx.2 t ht]; ring

/-- Part (2) of the energy identity: continuity of the energy. -/
theorem energy_continuousOn (hU : IsOpen U) (hI : I.OrdConnected)
    (ha : IsParabolicCoeff lam Lam a U I) (u : ParH1Function U I)
    (hu : IsParabolicWeakSolution a U I u) (φ : ParCutoff U I) :
    ContinuousOn (fun t => (1 / 2 : ℝ) * ∫ x in U, φ.toFun (x, t) ^ 2 * u.toFun (x, t) ^ 2) I := by
  set A : Vec d × ℝ → ℝ := fun z => u.toFun z ^ 2 * φ.toFun z * parTimeDeriv φ.toFun z with hA
  set B : Vec d × ℝ → ℝ := fun z => vecDot (matVecMul (a z) (u.grad z))
    (φ.toFun z ^ 2 • u.grad z + (2 * φ.toFun z * u.toFun z) • parSpaceGrad φ.toFun z) with hB
  refine continuousOn_of_primitive hI (g := fun σ => ∫ x in U, (A - B) (x, σ)) ?_
  intro s t hs ht hst
  obtain ⟨hAi, hBi, hid⟩ := slab_conclusion hU hI ha u hu φ hs ht hst
  have hΨ : Integrable (A - B) (volume.restrict (U ×ˢ Ioc s t)) := hAi.sub hBi
  have hΨ' : Integrable (A - B) ((volume.restrict U).prod (volume.restrict (Ioc s t))) := by
    rw [← volume_restrict_prod]; exact hΨ
  refine ⟨hΨ'.integral_prod_right, ?_⟩
  rw [hid, ← integral_sub hAi hBi]
  have := integral_prod_symm (A - B) hΨ'
  rw [← volume_restrict_prod] at this
  exact this

end Conclusion

end PDE.Parabolic.Energy
