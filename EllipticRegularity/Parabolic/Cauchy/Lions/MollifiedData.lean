module

public import EllipticRegularity.Parabolic.Cauchy.Lions.ClosureData
public import EllipticRegularity.Parabolic.Cauchy.Lions.MollifiedSliceIdentity
public import EllipticRegularity.Parabolic.Energy.Fubini

/-! # Mollified Lions representatives in the energy-data format -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set Metric intervalIntegral

namespace PDE.Parabolic.Lions

private theorem mollifiedKernelIntegral_eq_collar {d : ℕ} {δ : ℝ}
    (hδ : 0 < δ) {K1 : Set (Vec d)} (_hK1m : MeasurableSet K1) {x : Vec d}
    (hball : closedBall x δ ⊆ K1) (t : ℝ) (w : Vec d × ℝ → ℝ) :
    (∫ y, PDE.Parabolic.Energy.kern δ (x - y) * w (y, t)) =
      ∫ y in K1, PDE.Parabolic.Energy.kern δ (x - y) * w (y, t) := by
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := K1) (f := fun y : Vec d =>
      PDE.Parabolic.Energy.kern δ (x - y) * w (y, t))
    (fun y hy => by
      have hyball : y ∉ closedBall x δ := fun h => hy (hball h)
      have hnorm := PDE.Parabolic.Energy.lt_norm_of_notMem_closedBall hyball
      simp [PDE.Parabolic.Energy.kern_eq_zero_of_lt_norm hδ hnorm])).symm

private theorem mollifiedKernelDerivativeIntegral_eq_collar {d : ℕ} {δ : ℝ}
    (hδ : 0 < δ) {K1 : Set (Vec d)} (_hK1m : MeasurableSet K1)
    {x : Vec d} {i : Fin d}
    (hball : closedBall x δ ⊆ K1) :
    ∀ t (F : Vec d × ℝ → ℝ),
      (∫ y, F (y, t) *
          fderiv ℝ (PDE.Parabolic.Energy.kern δ) (x - y) (basisVec i)) =
        ∫ y in K1, F (y, t) *
          fderiv ℝ (PDE.Parabolic.Energy.kern δ) (x - y) (basisVec i) := by
  intro t F
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := K1) (f := fun y : Vec d => F (y, t) *
      fderiv ℝ (PDE.Parabolic.Energy.kern δ) (x - y) (basisVec i))
    (fun y hy => by
      have hyball : y ∉ closedBall x δ := fun h => hy (hball h)
      have hnorm := PDE.Parabolic.Energy.lt_norm_of_notMem_closedBall hyball
      have hk := PDE.Parabolic.Energy.fderiv_kern_eq_zero_of_lt_norm hδ hnorm
      have hki := congrArg (fun L : Vec d →L[ℝ] ℝ => L (basisVec i)) hk
      simp [hki])).symm

/-- The mollified scalar representative increment, rewritten in the collar integral format used
by the cutoff energy identity. -/
theorem cauchyMollifiedRepresentative_hslice
    {d : ℕ} {lam Lam s T δ ε : ℝ} {A : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam A univ (Icc s T))
    (hδ : 0 < δ) (hε : 0 < ε) (f : Vec d → ℝ)
    (hf : MemLp f 2 (volume : Measure (Vec d)))
    (u : CauchyX d s T)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    {K : Set (Vec d)} (hK : IsCompact K) {δ0 : ℝ} (_hδ0 : 0 < δ0)
    (w : Vec d × ℝ → ℝ) (G : Vec d × ℝ → Vec d)
    (hwm : Measurable w)
    (hwcont : ∀ x, ContinuousOn (fun t => w (x, t)) (Icc s T))
    (hwae : w =ᵐ[slabMeasure d s T]
      PDE.Parabolic.Energy.mollT ε univ (cauchyEnergyValue u))
    (B : ℝ) (hB : 0 ≤ B)
    (hwB : ∀ x t, t ∈ Icc s T → |w (x, t)| ≤ B)
    (hGmem : ∀ i, MemLp (fun z => G z i) 2 (slabMeasure d s T))
    (hGae : ∀ i, ∀ᵐ z ∂(slabMeasure d s T),
      G z i = PDE.Parabolic.Energy.mollT ε univ
        (fun z => matVecMul (A z) (cauchyEnergyGradient u z) i) z)
    {p q : ℝ} (hp : s ≤ p) (hpq : p ≤ q) (hq : q ≤ T)
    (hδδ : δ ≤ δ0) :
    ∀ x ∈ K,
      (∫ y in cthickening δ0 K,
          PDE.Parabolic.Energy.kern δ (x - y) * w (y, q)) -
        ∫ y in cthickening δ0 K,
          PDE.Parabolic.Energy.kern δ (x - y) * w (y, p) =
      ∫ z in cthickening δ0 K ×ˢ Ioc p q,
        ∑ i, G z i * fderiv ℝ (PDE.Parabolic.Energy.kern δ)
          (x - z.1) (basisVec i) := by
  intro x hx
  let K1 : Set (Vec d) := cthickening δ0 K
  have hK1 : IsCompact K1 := hK.cthickening
  have hK1m : MeasurableSet K1 := hK1.measurableSet
  have hcollar : ∀ x ∈ K, closedBall x δ ⊆ K1 := by
    intro y hy
    exact (closedBall_subset_cthickening hy δ).trans
      (cthickening_mono hδδ K)
  have hxball := hcollar x hx
  obtain ⟨v, hvcont, hvpair, hvinit, hvinc⟩ :=
    exists_cauchy_mollified_kernel_time_representative hsT ha hδ hε f hf u hrep
      w hwm hwcont hwae B hB hwB x
  have hleftq := mollifiedKernelIntegral_eq_collar hδ hK1m hxball q w
  have hleftp := mollifiedKernelIntegral_eq_collar hδ hK1m hxball p w
  -- The spacetime a.e. representative identity identifies the time-slice flux pairings.
  have hmeasure : (volume : Measure (Vec d)).prod
      (volume.restrict (Icc s T)) = slabMeasure d s T := by
    change (volume : Measure (Vec d)).prod (volume.restrict (Icc s T)) =
      (volume : Measure (Vec d × ℝ)).restrict (univ ×ˢ Icc s T)
    calc
      _ = (volume.restrict (univ : Set (Vec d))).prod
          (volume.restrict (Icc s T)) := by simp
      _ = (volume : Measure (Vec d × ℝ)).restrict (univ ×ˢ Icc s T) :=
        (PDE.Parabolic.Energy.volume_restrict_prod univ (Icc s T)).symm
  have hGprod (i : Fin d) : ∀ᵐ z ∂((volume : Measure (Vec d)).prod
      (volume.restrict (Icc s T))),
      G z i = PDE.Parabolic.Energy.mollT ε univ
        (fun z => matVecMul (A z) (cauchyEnergyGradient u z) i) z := by
    have h := hGae i
    rw [← hmeasure] at h
    exact h
  have hGtime (i : Fin d) : ∀ᵐ t ∂(volume.restrict (Icc s T)),
      ∀ᵐ (y : Vec d) ∂(volume : Measure (Vec d)),
        G (y, t) i = PDE.Parabolic.Energy.mollT ε univ
          (fun z => matVecMul (A z) (cauchyEnergyGradient u z) i) (y, t) :=
    PDE.Parabolic.Energy.ae_ae_swap (hGprod i)
  have hkernelSupport (i : Fin d) (y : Vec d) (hy : y ∉ K1) :
      fderiv ℝ (PDE.Parabolic.Energy.kern δ) (x - y) (basisVec i) = 0 := by
    have hyball : y ∉ closedBall x δ := fun hy' => hy (hxball hy')
    exact congrArg (fun L : Vec d →L[ℝ] ℝ => L (basisVec i))
      (PDE.Parabolic.Energy.fderiv_kern_eq_zero_of_lt_norm hδ
        (PDE.Parabolic.Energy.lt_norm_of_notMem_closedBall hyball))
  have htimePair (i : Fin d) : ∀ᵐ t ∂(volume.restrict (Icc s T)),
      (∫ y, PDE.wholeSpaceMollify ε
          (fun z : Vec d => matVecMul (A (z, t))
            (cauchyEnergyGradient u (z, t)) i) y *
            fderiv ℝ (PDE.Parabolic.Energy.kern δ) (x - y) (basisVec i)) =
        ∫ y in K1, G (y, t) i *
          fderiv ℝ (PDE.Parabolic.Energy.kern δ) (x - y) (basisVec i) := by
    filter_upwards [hGtime i] with t ht
    have hset : (∫ y, PDE.wholeSpaceMollify ε
        (fun z : Vec d => matVecMul (A (z, t))
          (cauchyEnergyGradient u (z, t)) i) y *
          fderiv ℝ (PDE.Parabolic.Energy.kern δ) (x - y) (basisVec i)) =
        ∫ y in K1, PDE.wholeSpaceMollify ε
          (fun z : Vec d => matVecMul (A (z, t))
            (cauchyEnergyGradient u (z, t)) i) y *
          fderiv ℝ (PDE.Parabolic.Energy.kern δ) (x - y) (basisVec i) := by
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := K1) (f := fun y : Vec d => PDE.wholeSpaceMollify ε
          (fun z : Vec d => matVecMul (A (z, t))
            (cauchyEnergyGradient u (z, t)) i) y *
          fderiv ℝ (PDE.Parabolic.Energy.kern δ) (x - y) (basisVec i))
        (fun y hy => by simp [hkernelSupport i y hy])).symm
    rw [hset]
    have htK : ∀ᵐ y ∂(volume.restrict K1),
        G (y, t) i = PDE.Parabolic.Energy.mollT ε univ
          (fun z => matVecMul (A z) (cauchyEnergyGradient u z) i) (y, t) :=
      (ae_restrict_iff' hK1m).2 (ht.mono fun y hy => fun _ => hy)
    apply MeasureTheory.integral_congr_ae
    filter_upwards [htK] with y hy
    rw [hy]
    simp [PDE.Parabolic.Energy.mollT]
  have htimePairAll : ∀ᵐ t ∂(volume.restrict (Icc s T)), ∀ i : Fin d,
      (∫ y, PDE.wholeSpaceMollify ε
          (fun z : Vec d => matVecMul (A (z, t))
            (cauchyEnergyGradient u (z, t)) i) y *
            fderiv ℝ (PDE.Parabolic.Energy.kern δ) (x - y) (basisVec i)) =
        ∫ y in K1, G (y, t) i *
          fderiv ℝ (PDE.Parabolic.Energy.kern δ) (x - y) (basisVec i) := by
    rw [ae_all_iff]
    intro i
    exact htimePair i
  have hIoc : Ioc p q ⊆ Icc s T := by
    intro t ht
    exact ⟨hp.trans ht.1.le, ht.2.trans hq⟩
  have htimePairIoc := ae_restrict_of_ae_restrict_of_subset hIoc htimePairAll
  have hslab : K1 ×ˢ Ioc p q ⊆ (univ : Set (Vec d)) ×ˢ Icc s T :=
    prod_mono (subset_univ _) hIoc
  have hrestrict : volume.restrict (K1 ×ˢ Ioc p q) ≤ slabMeasure d s T :=
    Measure.restrict_mono hslab le_rfl
  let : IsFiniteMeasure (volume.restrict (K1 ×ˢ Ioc p q)) := ⟨by
    rw [Measure.restrict_apply_univ, Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_lt_top hK1.measure_lt_top (by simp)⟩
  let H : Vec d × ℝ → ℝ := fun z => ∑ i : Fin d,
    G z i * fderiv ℝ (PDE.Parabolic.Energy.kern δ) (x - z.1) (basisVec i)
  have hHi : ∀ i : Fin d, Integrable (fun z : Vec d × ℝ =>
      G z i * fderiv ℝ (PDE.Parabolic.Energy.kern δ)
        (x - z.1) (basisVec i)) (volume.restrict (K1 ×ˢ Ioc p q)) := by
    intro i
    have hGi : MemLp (fun z : Vec d × ℝ => G z i) 2
        (volume.restrict (K1 ×ˢ Ioc p q)) := (hGmem i).mono_measure hrestrict
    have hGint := hGi.integrable (by norm_num)
    have hkcont : Continuous (fun z : Vec d × ℝ =>
        fderiv ℝ (PDE.Parabolic.Energy.kern δ) (x - z.1) (basisVec i)) :=
      (PDE.Parabolic.Energy.kern_fderiv_continuous δ (basisVec i)).comp
        (continuous_const.sub continuous_fst)
    obtain ⟨C, hC⟩ := PDE.Parabolic.Energy.kern_fderiv_bound hδ (basisVec i)
    let C' := max C 0
    have hbound : ∀ᵐ z ∂(volume.restrict (K1 ×ˢ Ioc p q)),
        ‖fderiv ℝ (PDE.Parabolic.Energy.kern δ) (x - z.1) (basisVec i)‖ ≤ C' := by
      filter_upwards [] with z
      rw [Real.norm_eq_abs]
      exact (hC (x - z.1)).trans (le_max_left _ _)
    have hmul := hGint.mul_bdd hkcont.aestronglyMeasurable
        (c := C') hbound
    exact hmul.congr (Filter.Eventually.of_forall fun z => by ring)
  have hHint : Integrable H (volume.restrict (K1 ×ˢ Ioc p q)) := by
    unfold H
    exact integrable_finsetSum _ fun i hi => hHi i
  have hHintOn : IntegrableOn H (K1 ×ˢ Ioc p q) volume := hHint
  have hFub := PDE.Parabolic.WeakSlice.integral_prod_slices hHintOn
  have hsliceInt (i : Fin d) : ∀ᵐ t ∂(volume.restrict (Ioc p q)),
      Integrable (fun y : Vec d => G (y, t) i *
        fderiv ℝ (PDE.Parabolic.Energy.kern δ) (x - y) (basisVec i))
          (volume.restrict K1) := by
    have hprod : Integrable
        (fun z : Vec d × ℝ => G z i *
          fderiv ℝ (PDE.Parabolic.Energy.kern δ) (x - z.1) (basisVec i))
        ((volume.restrict K1).prod (volume.restrict (Ioc p q))) := by
      rw [← PDE.Parabolic.Energy.volume_restrict_prod]
      exact hHi i
    exact hprod.prod_left_ae
  have hsumSlices : ∀ᵐ t ∂(volume.restrict (Ioc p q)),
      (∫ y in K1, ∑ i : Fin d, G (y, t) i *
        fderiv ℝ (PDE.Parabolic.Energy.kern δ) (x - y) (basisVec i)) =
      ∑ i : Fin d, ∫ y in K1, G (y, t) i *
        fderiv ℝ (PDE.Parabolic.Energy.kern δ) (x - y) (basisVec i) := by
    have hsi : ∀ᵐ t ∂(volume.restrict (Ioc p q)), ∀ i : Fin d,
        Integrable (fun y : Vec d => G (y, t) i *
          fderiv ℝ (PDE.Parabolic.Energy.kern δ) (x - y) (basisVec i))
            (volume.restrict K1) := by
      rw [ae_all_iff]
      intro i
      exact hsliceInt i
    filter_upwards [hsi] with t ht
    exact integral_finsetSum Finset.univ fun i hi => ht i
  have htimePairSummed : ∀ᵐ t ∂(volume.restrict (Ioc p q)),
      (∑ i : Fin d, ∫ y,
          PDE.wholeSpaceMollify ε
          (fun z : Vec d => matVecMul (A (z, t))
              (cauchyEnergyGradient u (z, t)) i) y *
            fderiv ℝ (PDE.Parabolic.Energy.kern δ) (x - y) (basisVec i)) =
        ∫ y in K1, ∑ i : Fin d, G (y, t) i *
          fderiv ℝ (PDE.Parabolic.Energy.kern δ) (x - y) (basisVec i) := by
    have htime := ae_restrict_of_ae_restrict_of_subset hIoc htimePairAll
    filter_upwards [htime, hsumSlices] with t ht hs
    calc
      (∑ i : Fin d, ∫ y,
          PDE.wholeSpaceMollify ε
            (fun z : Vec d => matVecMul (A (z, t))
              (cauchyEnergyGradient u (z, t)) i) y *
            fderiv ℝ (PDE.Parabolic.Energy.kern δ) (x - y) (basisVec i)) =
        ∑ i : Fin d, ∫ y in K1, G (y, t) i *
          fderiv ℝ (PDE.Parabolic.Energy.kern δ) (x - y) (basisVec i) :=
            Finset.sum_congr rfl fun i hi => ht i
      _ = ∫ y in K1, ∑ i : Fin d, G (y, t) i *
          fderiv ℝ (PDE.Parabolic.Energy.kern δ) (x - y) (basisVec i) := hs.symm
  have htimePairVolume : ∀ᵐ t ∂volume, t ∈ Ioc p q →
      (∑ i : Fin d, ∫ y,
          PDE.wholeSpaceMollify ε
            (fun z : Vec d => matVecMul (A (z, t))
              (cauchyEnergyGradient u (z, t)) i) y *
            fderiv ℝ (PDE.Parabolic.Energy.kern δ) (x - y) (basisVec i)) =
        ∫ y in K1, ∑ i : Fin d, G (y, t) i *
          fderiv ℝ (PDE.Parabolic.Energy.kern δ) (x - y) (basisVec i) :=
    (ae_restrict_iff' measurableSet_Ioc).1 htimePairSummed
  have htimeEq :
      (∫ t in p..q, ∑ i : Fin d, ∫ y,
          PDE.wholeSpaceMollify ε
            (fun z : Vec d => matVecMul (A (z, t))
              (cauchyEnergyGradient u (z, t)) i) y *
            fderiv ℝ (PDE.Parabolic.Energy.kern δ) (x - y) (basisVec i)) =
        ∫ z in K1 ×ˢ Ioc p q, H z := by
    rw [intervalIntegral.integral_of_le hpq]
    calc
      (∫ t in Ioc p q, ∑ i : Fin d, ∫ y,
          PDE.wholeSpaceMollify ε
            (fun z : Vec d => matVecMul (A (z, t))
              (cauchyEnergyGradient u (z, t)) i) y *
            fderiv ℝ (PDE.Parabolic.Energy.kern δ) (x - y) (basisVec i)) =
        ∫ t in Ioc p q, ∫ y in K1, H (y, t) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [htimePairSummed] with t ht
          simpa [H] using ht
      _ = ∫ z in K1 ×ˢ Ioc p q, H z := hFub.2.symm
  have hfinal := hvinc p ⟨hp, hpq.trans hq⟩ q ⟨hp.trans hpq, hq⟩
  calc
    (∫ y in K1, PDE.Parabolic.Energy.kern δ (x - y) * w (y, q)) -
        ∫ y in K1, PDE.Parabolic.Energy.kern δ (x - y) * w (y, p) = v q - v p := by
      rw [← hleftq, ← hleftp, hvpair q ⟨hp.trans hpq, hq⟩,
        hvpair p ⟨hp, hpq.trans hq⟩]
    _ = ∫ t in p..q, ∑ i : Fin d, ∫ y,
          PDE.wholeSpaceMollify ε
            (fun z : Vec d => matVecMul (A (z, t))
              (cauchyEnergyGradient u (z, t)) i) y *
            fderiv ℝ (PDE.Parabolic.Energy.kern δ) (x - y) (basisVec i) := hfinal
    _ = ∫ z in K1 ×ˢ Ioc p q, H z := htimeEq
    _ = ∫ z in K1 ×ˢ Ioc p q, ∑ i, G z i *
          fderiv ℝ (PDE.Parabolic.Energy.kern δ) (x - z.1) (basisVec i) := by
        rfl

end PDE.Parabolic.Lions
