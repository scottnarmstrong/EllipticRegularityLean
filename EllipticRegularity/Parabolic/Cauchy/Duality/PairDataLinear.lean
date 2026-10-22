module

public import EllipticRegularity.Parabolic.Cauchy.Duality.PairReverseData

@[expose] public section

namespace PDE.Parabolic.Duality

open MeasureTheory Set
open PDE.Parabolic.Energy

private theorem energyData_kern_mul_u_integrable {d : ℕ} (D : Energy.Data d)
    (a : ℝ) (x : Vec d) {τ : ℝ} (hτ : τ ∈ Icc D.s D.t) :
    IntegrableOn (fun y => kern a (x - y) * D.u (y, τ)) D.K1 := by
  have hu : Integrable (fun y => D.u (y, τ)) (volume.restrict D.K1) :=
    (D.hus τ hτ).integrable (by norm_num)
  have hk : Continuous fun y : Vec d => kern a (x - y) := by
    exact (kern_continuous a).comp (continuous_const.sub continuous_id)
  obtain ⟨M, hM⟩ := D.K1_compact.exists_bound_of_continuousOn hk.continuousOn
  have hbound : ∀ᵐ y ∂(volume.restrict D.K1), |kern a (x - y)| ≤ M := by
    exact (ae_restrict_iff' D.K1_measurable).2
      (Filter.Eventually.of_forall fun y hy => hM y hy)
  have hm := hu.bdd_mul hk.aestronglyMeasurable (c := M) hbound
  exact hm.congr (Filter.Eventually.of_forall fun y => by ring)

private theorem energyData_ae_integrable_Du_slice {d : ℕ} (D : Energy.Data d)
    (i : Fin d) :
    ∀ᵐ τ ∂(volume.restrict (Ioc D.s D.t)),
      IntegrableOn (fun y => D.Du (y, τ) i) D.K1 := by
  have hslice := Energy.ae_slice_memLp D.K1_measurable (D.hDu2 i)
  filter_upwards [hslice] with τ hτ
  have hmem : MemLp (fun y => D.Du (y, τ) i) 2 (volume.restrict D.K1) :=
    (memLp_indicator_iff_restrict D.K1_measurable).1 hτ
  exact hmem.integrable (by norm_num)

/-- Add two abstract energy data sets on the same collar, interval, and cutoff. -/
noncomputable def energyDataAdd {d : ℕ} (D E : Energy.Data d)
    (hK : D.K = E.K) (hδ : D.δ0 = E.δ0) (hs : D.s = E.s) (ht : D.t = E.t) :
    Energy.Data d := by
  have hK1 : D.K1 = E.K1 := by simp [Energy.Data.K1, hK, hδ]
  have hQ : D.K1 ×ˢ Ioc D.s D.t = E.K1 ×ˢ Ioc E.s E.t := by
    simp [hK1, hs, ht]
  have hμ : volume.restrict (D.K1 ×ˢ Ioc D.s D.t) =
      volume.restrict (E.K1 ×ˢ Ioc E.s E.t) := congrArg (fun S => volume.restrict S) hQ
  have hEhu2 : MemLp E.u 2 (volume.restrict (D.K1 ×ˢ Ioc D.s D.t)) := by
    rw [hμ]
    exact E.hu2
  have hEDu2 : ∀ i, MemLp (fun z => E.Du z i) 2
      (volume.restrict (D.K1 ×ˢ Ioc D.s D.t)) := by
    intro i
    rw [hμ]
    exact E.hDu2 i
  have hEG2 : ∀ i, MemLp (fun z => E.G z i) 2
      (volume.restrict (D.K1 ×ˢ Ioc D.s D.t)) := by
    intro i
    rw [hμ]
    exact E.hG2 i
  refine {
    K := D.K
    hK := D.hK
    δ0 := D.δ0
    hδ0 := D.hδ0
    hδ1 := D.hδ1
    s := D.s
    t := D.t
    hst := D.hst
    u := fun z => D.u z + E.u z
    Du := fun z => D.Du z + E.Du z
    G := fun z => D.G z + E.G z
    φ := D.φ
    hφ := D.hφ
    hφK := D.hφK
    hDum := fun i => (D.hDum i).add (E.hDum i)
    hGm := fun i => (D.hGm i).add (E.hGm i)
    hu2 := D.hu2.add hEhu2
    hDu2 := fun i => (D.hDu2 i).add (hEDu2 i)
    hG2 := fun i => (D.hG2 i).add (hEG2 i)
    hus := by
      intro τ hτ
      have hEτ : τ ∈ Icc E.s E.t := by simpa [hs, ht] using hτ
      have hEhus := E.hus τ hEτ
      have hEhus' : MemLp (fun y => E.u (y, τ)) 2 (volume.restrict D.K1) := by
        rw [show volume.restrict D.K1 = volume.restrict E.K1 by rw [hK1]]
        exact hEhus
      exact (D.hus τ hτ).add hEhus'
    hwg := by
      have hDuD := energyData_ae_integrable_Du_slice D
      have hDuE := energyData_ae_integrable_Du_slice E
      have hDuE' : ∀ i, ∀ᵐ τ ∂(volume.restrict (Ioc D.s D.t)),
          IntegrableOn (fun y => E.Du (y, τ) i) D.K1 := by
        intro i
        have h := hDuE i
        have hIoc : volume.restrict (Ioc D.s D.t) = volume.restrict (Ioc E.s E.t) := by
          rw [hs, ht]
        rw [← hIoc] at h
        filter_upwards [h] with τ hτ
        simpa [← hK1] using hτ
      have hDuDall : ∀ᵐ τ ∂(volume.restrict (Ioc D.s D.t)), ∀ i,
          IntegrableOn (fun y => D.Du (y, τ) i) D.K1 := by
        rw [ae_all_iff]
        exact hDuD
      have hDuEall : ∀ᵐ τ ∂(volume.restrict (Ioc D.s D.t)), ∀ i,
          IntegrableOn (fun y => E.Du (y, τ) i) D.K1 := by
        rw [ae_all_iff]
        exact hDuE'
      have hDweak := D.hwg
      have hEweak : ∀ᵐ τ ∂(volume.restrict (Ioc D.s D.t)), ∀ a : ℝ, 0 < a → a ≤ D.δ0 →
          ∀ x ∈ D.K, ∀ i,
            ∫ y in D.K1, fderiv ℝ (kern a) (x - y) (basisVec i) * E.u (y, τ) =
              ∫ y in D.K1, kern a (x - y) * E.Du (y, τ) i := by
        have h := E.hwg
        have hIoc : volume.restrict (Ioc D.s D.t) = volume.restrict (Ioc E.s E.t) := by
          rw [hs, ht]
        rw [← hIoc] at h
        filter_upwards [h] with τ hτ
        simpa [← hK1, ← hδ, ← hK] using hτ
      have hτmem : ∀ᵐ τ ∂(volume.restrict (Ioc D.s D.t)), τ ∈ Ioc D.s D.t :=
        ae_restrict_mem measurableSet_Ioc
      filter_upwards [hDweak, hEweak, hDuDall, hDuEall, hτmem]
        with τ hD hE hDuDτ hDuEτ hτmem
      intro a ha haδ x hx i
      have hτcc : τ ∈ Icc D.s D.t := ⟨hτmem.1.le, hτmem.2⟩
      have hEτcc : τ ∈ Icc E.s E.t := by simpa [hs, ht] using hτcc
      have hleftD : IntegrableOn
          (fun y => fderiv ℝ (kern a) (x - y) (basisVec i) * D.u (y, τ)) D.K1 := by
        have hu := (D.hus τ hτcc).integrable (by norm_num)
        have hw : Continuous fun y : Vec d =>
            fderiv ℝ (kern a) (x - y) (basisVec i) :=
          (kern_fderiv_continuous a (basisVec i)).comp
            (continuous_const.sub continuous_id)
        obtain ⟨M, hM⟩ := D.K1_compact.exists_bound_of_continuousOn hw.continuousOn
        have hbound : ∀ᵐ y ∂(volume.restrict D.K1),
            |fderiv ℝ (kern a) (x - y) (basisVec i)| ≤ M :=
          (ae_restrict_iff' D.K1_measurable).2
            (Filter.Eventually.of_forall fun y hy => by simpa using hM y hy)
        have hm := hu.bdd_mul hw.aestronglyMeasurable (c := M) hbound
        change Integrable (fun y => fderiv ℝ (kern a) (x - y) (basisVec i) *
          D.u (y, τ)) (volume.restrict D.K1)
        exact hm.congr (Filter.Eventually.of_forall fun y => by ring)
      have hleftE : IntegrableOn
          (fun y => fderiv ℝ (kern a) (x - y) (basisVec i) * E.u (y, τ)) D.K1 := by
        have hu := (E.hus τ hEτcc).integrable (by norm_num)
        have hw : Continuous fun y : Vec d =>
            fderiv ℝ (kern a) (x - y) (basisVec i) :=
          (kern_fderiv_continuous a (basisVec i)).comp
            (continuous_const.sub continuous_id)
        obtain ⟨M, hM⟩ := E.K1_compact.exists_bound_of_continuousOn hw.continuousOn
        have hbound : ∀ᵐ y ∂(volume.restrict E.K1),
            ‖fderiv ℝ (kern a) (x - y) (basisVec i)‖ ≤ M := by
          exact (ae_restrict_iff' E.K1_measurable).2
            (Filter.Eventually.of_forall fun y hy => hM y hy)
        have hm := hu.bdd_mul hw.aestronglyMeasurable (c := M) hbound
        have hmE : Integrable (fun y => E.u (y, τ) *
            fderiv ℝ (kern a) (x - y) (basisVec i)) (volume.restrict D.K1) := by
          rw [show volume.restrict D.K1 = volume.restrict E.K1 by rw [hK1]]
          exact hm.congr (Filter.Eventually.of_forall fun y => by ring)
        change Integrable (fun y => fderiv ℝ (kern a) (x - y) (basisVec i) *
          E.u (y, τ)) (volume.restrict D.K1)
        exact hmE.congr (Filter.Eventually.of_forall fun y => by ring)
      have hrightD : IntegrableOn
          (fun y => kern a (x - y) * D.Du (y, τ) i) D.K1 := by
        have hdu := hDuDτ i
        obtain ⟨C, hC⟩ := kern_bound (d := d) ha
        have hk : AEStronglyMeasurable (fun y : Vec d => kern a (x - y))
            (volume.restrict D.K1) :=
          (kern_continuous a).comp (continuous_const.sub continuous_id) |>.aestronglyMeasurable
        have hbound : ∀ᵐ y ∂(volume.restrict D.K1), |kern a (x - y)| ≤ C := by
          exact (ae_restrict_iff' D.K1_measurable).2
            (Filter.Eventually.of_forall fun y _ => hC (x - y))
        exact (hdu.bdd_mul hk (c := C) hbound).congr
          (Filter.Eventually.of_forall fun y => by ring)
      have hrightE : IntegrableOn
          (fun y => kern a (x - y) * E.Du (y, τ) i) D.K1 := by
        have hdu := hDuEτ i
        obtain ⟨C, hC⟩ := kern_bound (d := d) ha
        have hk : AEStronglyMeasurable (fun y : Vec d => kern a (x - y))
            (volume.restrict D.K1) :=
          (kern_continuous a).comp (continuous_const.sub continuous_id) |>.aestronglyMeasurable
        have hbound : ∀ᵐ y ∂(volume.restrict D.K1), |kern a (x - y)| ≤ C := by
          exact (ae_restrict_iff' D.K1_measurable).2
            (Filter.Eventually.of_forall fun y _ => hC (x - y))
        exact (hdu.bdd_mul hk (c := C) hbound).congr
          (Filter.Eventually.of_forall fun y => by ring)
      calc
        ∫ y in D.K1, fderiv ℝ (kern a) (x - y) (basisVec i) *
            (D.u (y, τ) + E.u (y, τ)) =
          (∫ y in D.K1, fderiv ℝ (kern a) (x - y) (basisVec i) * D.u (y, τ)) +
            ∫ y in D.K1, fderiv ℝ (kern a) (x - y) (basisVec i) * E.u (y, τ) := by
          rw [show (fun y => fderiv ℝ (kern a) (x - y) (basisVec i) *
              (D.u (y, τ) + E.u (y, τ))) =
              fun y => fderiv ℝ (kern a) (x - y) (basisVec i) * D.u (y, τ) +
                fderiv ℝ (kern a) (x - y) (basisVec i) * E.u (y, τ) by
            funext y
            ring, integral_add hleftD hleftE]
        _ = (∫ y in D.K1, kern a (x - y) * D.Du (y, τ) i) +
            ∫ y in D.K1, kern a (x - y) * E.Du (y, τ) i := by rw [hD a ha haδ x hx i, hE a ha haδ x hx i]
        _ = ∫ y in D.K1, kern a (x - y) * (D.Du (y, τ) + E.Du (y, τ)) i := by
          rw [show (fun y => kern a (x - y) * (D.Du (y, τ) + E.Du (y, τ)) i) =
            fun y => kern a (x - y) * D.Du (y, τ) i + kern a (x - y) * E.Du (y, τ) i by
              funext y
              simp only [Pi.add_apply]
              ring, integral_add hrightD hrightE]
    hslice := by
      intro a ha haδ x hx τ1 τ2 h1 h12 h2
      change
        (∫ y in D.K1, kern a (x - y) * (D.u (y, τ2) + E.u (y, τ2))) -
          ∫ y in D.K1, kern a (x - y) * (D.u (y, τ1) + E.u (y, τ1)) =
        ∫ z in D.K1 ×ˢ Ioc τ1 τ2,
          ∑ i, (D.G z + E.G z) i * fderiv ℝ (kern a) (x - z.1) (basisVec i)
      have hEsl : ∀ a' : ℝ, 0 < a' → a' ≤ D.δ0 → ∀ x ∈ D.K,
          ∀ τ1 τ2 : ℝ, D.s ≤ τ1 → τ1 ≤ τ2 → τ2 ≤ D.t →
          (∫ y in D.K1, kern a' (x - y) * E.u (y, τ2)) -
            ∫ y in D.K1, kern a' (x - y) * E.u (y, τ1) =
          ∫ z in D.K1 ×ˢ Ioc τ1 τ2,
            ∑ i, E.G z i * fderiv ℝ (kern a') (x - z.1) (basisVec i) := by
        intro a' ha' haδ' x hx τ1 τ2 h1 h12 h2
        have haδE : a' ≤ E.δ0 := by simpa [hδ] using haδ'
        have hxE : x ∈ E.K := by simpa [hK] using hx
        have h1E : E.s ≤ τ1 := by rw [← hs]; exact h1
        have h2E : τ2 ≤ E.t := by rw [← ht]; exact h2
        have h := E.hslice a' ha' haδE x hxE τ1 τ2 h1E h12 h2E
        simpa [← hK1] using h
      have hL2 : IntegrableOn (fun y => kern a (x - y) * D.u (y, τ1)) D.K1 :=
        energyData_kern_mul_u_integrable D a x ⟨h1, h12.trans h2⟩
      have hL3 : IntegrableOn (fun y => kern a (x - y) * D.u (y, τ2)) D.K1 :=
        energyData_kern_mul_u_integrable D a x ⟨h1.trans h12, h2⟩
      have hE1 : IntegrableOn (fun y => kern a (x - y) * E.u (y, τ1)) D.K1 := by
        have h1E : E.s ≤ τ1 := by rw [← hs]; exact h1
        have h2E : τ1 ≤ E.t := by rw [← ht]; exact (h12.trans h2)
        have hτ : τ1 ∈ Icc E.s E.t := ⟨h1E, h2E⟩
        have h := energyData_kern_mul_u_integrable E a x hτ
        simpa [← hK1] using h
      have hE2 : IntegrableOn (fun y => kern a (x - y) * E.u (y, τ2)) D.K1 := by
        have h1E : E.s ≤ τ2 := by rw [← hs]; exact (h1.trans h12)
        have h2E : τ2 ≤ E.t := by rw [← ht]; exact h2
        have hτ : τ2 ∈ Icc E.s E.t := ⟨h1E, h2E⟩
        have h := energyData_kern_mul_u_integrable E a x hτ
        simpa [← hK1] using h
      have hPhiD := Energy.Data.Phi_integrableOn D ha x h1 h2
      have hPhiE : IntegrableOn (fun z =>
          ∑ i, E.G z i * fderiv ℝ (kern a) (x - z.1) (basisVec i))
          (D.K1 ×ˢ Ioc τ1 τ2) := by
        have h1E : E.s ≤ τ1 := by rw [← hs]; exact h1
        have h2E : τ2 ≤ E.t := by rw [← ht]; exact h2
        have h := Energy.Data.Phi_integrableOn E ha x h1E h2E
        have hset : D.K1 ×ˢ Ioc τ1 τ2 = E.K1 ×ˢ Ioc τ1 τ2 := by rw [hK1]
        rw [hset]
        change IntegrableOn (E.Phi a x) (E.K1 ×ˢ Ioc τ1 τ2)
        exact h
      have hval2 : ∫ y in D.K1, kern a (x - y) *
          (D.u (y, τ2) + E.u (y, τ2)) =
          (∫ y in D.K1, kern a (x - y) * D.u (y, τ2)) +
            ∫ y in D.K1, kern a (x - y) * E.u (y, τ2) := by
        rw [show (fun y => kern a (x - y) * (D.u (y, τ2) + E.u (y, τ2))) =
            fun y => kern a (x - y) * D.u (y, τ2) + kern a (x - y) * E.u (y, τ2) by
              funext y
              ring, integral_add hL3 hE2]
      have hval1 : ∫ y in D.K1, kern a (x - y) *
          (D.u (y, τ1) + E.u (y, τ1)) =
          (∫ y in D.K1, kern a (x - y) * D.u (y, τ1)) +
            ∫ y in D.K1, kern a (x - y) * E.u (y, τ1) := by
        rw [show (fun y => kern a (x - y) * (D.u (y, τ1) + E.u (y, τ1))) =
            fun y => kern a (x - y) * D.u (y, τ1) + kern a (x - y) * E.u (y, τ1) by
              funext y
              ring, integral_add hL2 hE1]
      have hDsl : (∫ y in D.K1, kern a (x - y) * D.u (y, τ2)) -
          ∫ y in D.K1, kern a (x - y) * D.u (y, τ1) =
          ∫ z in D.K1 ×ˢ Ioc τ1 τ2,
            ∑ i, D.G z i * fderiv ℝ (kern a) (x - z.1) (basisVec i) := by
        simpa [Energy.Data.K1] using D.hslice a ha haδ x hx τ1 τ2 h1 h12 h2
      have hsum : (fun z =>
          (∑ i, D.G z i * fderiv ℝ (kern a) (x - z.1) (basisVec i)) +
          ∑ i, E.G z i * fderiv ℝ (kern a) (x - z.1) (basisVec i)) =
          fun z => ∑ i, (D.G z i + E.G z i) *
            fderiv ℝ (kern a) (x - z.1) (basisVec i) := by
        funext z
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      have hPhiD' : IntegrableOn (fun z =>
          ∑ i, D.G z i * fderiv ℝ (kern a) (x - z.1) (basisVec i))
          (D.K1 ×ˢ Ioc τ1 τ2) := by
        change IntegrableOn (D.Phi a x) (D.K1 ×ˢ Ioc τ1 τ2)
        exact hPhiD
      rw [hval2, hval1]
      calc
        _ = ((∫ z in D.K1 ×ˢ Ioc τ1 τ2,
              ∑ i, D.G z i * fderiv ℝ (kern a) (x - z.1) (basisVec i)) +
            ∫ z in D.K1 ×ˢ Ioc τ1 τ2,
              ∑ i, E.G z i * fderiv ℝ (kern a) (x - z.1) (basisVec i)) := by
          rw [show
            ((∫ y in D.K1, kern a (x - y) * D.u (y, τ2)) +
                ∫ y in D.K1, kern a (x - y) * E.u (y, τ2)) -
              ((∫ y in D.K1, kern a (x - y) * D.u (y, τ1)) +
                ∫ y in D.K1, kern a (x - y) * E.u (y, τ1)) =
            ((∫ y in D.K1, kern a (x - y) * D.u (y, τ2)) -
                ∫ y in D.K1, kern a (x - y) * D.u (y, τ1)) +
              ((∫ y in D.K1, kern a (x - y) * E.u (y, τ2)) -
                ∫ y in D.K1, kern a (x - y) * E.u (y, τ1)) by ring]
          rw [hDsl, hEsl a ha haδ x hx τ1 τ2 h1 h12 h2]
        _ = ∫ z in D.K1 ×ˢ Ioc τ1 τ2,
              ∑ i, (D.G z + E.G z) i *
                fderiv ℝ (kern a) (x - z.1) (basisVec i) := by
          rw [← integral_add hPhiD' hPhiE, hsum]
          simp only [Pi.add_apply]
  }

end PDE.Parabolic.Duality
