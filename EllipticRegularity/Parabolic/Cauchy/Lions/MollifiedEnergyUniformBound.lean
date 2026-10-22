module

public import EllipticRegularity.Parabolic.Cauchy.Lions.MollifiedEnergyEstimate

/-! # Uniform energy bounds for fixed-scale mollifications -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace PDE.Parabolic.Lions

theorem cauchyEnergyData_initial_cutoff_le
    {d : ℕ} (D : PDE.Parabolic.Energy.Data d) {ε : ℝ}
    (hε : 0 < ε) {f : Vec d → ℝ} (hf : MemLp f 2 volume)
    (hphi : ∀ z, |D.φ z| ≤ 1)
    (hinit : ∀ x, D.u (x, D.s) = PDE.wholeSpaceMollify ε f x) :
    (∫ x in D.K, D.φ (x, D.s) ^ 2 * D.u (x, D.s) ^ 2) ≤
      (eLpNorm f 2 volume).toReal ^ 2 := by
  have hMoll := PDE.Parabolic.Energy.eLpNorm_moll_le hε hf
  have hMollSq := hMoll.1.integrable_sq
  let q : Vec d → ℝ := fun x => D.φ (x, D.s) ^ 2
  have hqcont : Continuous q := by
    dsimp [q]
    exact (D.hφ.continuous.comp (continuous_id.prodMk continuous_const)).pow 2
  have hqmeas : AEStronglyMeasurable q (volume.restrict D.K) :=
    hqcont.aestronglyMeasurable
  have hqbound : ∀ᵐ x ∂(volume.restrict D.K), ‖q x‖ ≤ 1 := by
    filter_upwards [] with x
    rw [Real.norm_eq_abs]
    dsimp [q]
    rw [abs_pow]
    have hφ : |D.φ (x, D.s)| ≤ 1 := hphi (x, D.s)
    have hφ0 : 0 ≤ |D.φ (x, D.s)| := abs_nonneg _
    have hsquare := mul_self_le_mul_self hφ0 hφ
    nlinarith
  have hlocal : Integrable (fun x => q x * (PDE.wholeSpaceMollify ε f x) ^ 2)
      (volume.restrict D.K) := by
    have hrestrict : volume.restrict D.K ≤ volume := Measure.restrict_le_self
    have hsq : Integrable (fun x => (PDE.wholeSpaceMollify ε f x) ^ 2)
        (volume.restrict D.K) := hMollSq.mono_measure hrestrict
    exact hsq.bdd_mul hqmeas (c := 1) hqbound
  have hlocalSq : Integrable (fun x => (PDE.wholeSpaceMollify ε f x) ^ 2)
      (volume.restrict D.K) := by
    exact hMollSq.mono_measure (show volume.restrict D.K ≤ volume from
      Measure.restrict_le_self)
  have hcongr : (∫ x in D.K, D.φ (x, D.s) ^ 2 * D.u (x, D.s) ^ 2) =
      ∫ x in D.K, q x * (PDE.wholeSpaceMollify ε f x) ^ 2 := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [hinit x]
  rw [hcongr]
  have hpoint : ∀ᵐ x ∂(volume.restrict D.K),
      q x * (PDE.wholeSpaceMollify ε f x) ^ 2 ≤
        (PDE.wholeSpaceMollify ε f x) ^ 2 := by
    filter_upwards [hqbound] with x hx
    have hq0 : 0 ≤ q x := sq_nonneg _
    have hq1 : q x ≤ 1 := by
      simpa [q, abs_of_nonneg (sq_nonneg (D.φ (x, D.s)))] using hx
    exact mul_le_of_le_one_left (sq_nonneg _) hq1
  have hlocalLe := integral_mono_ae hlocal hlocalSq hpoint
  have hglobalLe := integral_mono_measure
    (show volume.restrict D.K ≤ volume from Measure.restrict_le_self)
    (ae_of_all _ fun x => sq_nonneg (PDE.wholeSpaceMollify ε f x)) hMollSq
  have hnormMoll : (eLpNorm (PDE.wholeSpaceMollify ε f) 2 volume).toReal ≤
      (eLpNorm f 2 volume).toReal :=
    ENNReal.toReal_mono hf.eLpNorm_ne_top hMoll.2
  have hsqMoll : (eLpNorm (PDE.wholeSpaceMollify ε f) 2 volume).toReal ^ 2 =
      ∫ x, (PDE.wholeSpaceMollify ε f x) ^ 2 :=
    PDE.toReal_eLpNorm_two_sq_eq_integral_sq hMoll.1
  calc
    (∫ x in D.K, q x * (PDE.wholeSpaceMollify ε f x) ^ 2) ≤
        ∫ x in D.K, (PDE.wholeSpaceMollify ε f x) ^ 2 := hlocalLe
    _ ≤ ∫ x, (PDE.wholeSpaceMollify ε f x) ^ 2 := hglobalLe
    _ = (eLpNorm (PDE.wholeSpaceMollify ε f) 2 volume).toReal ^ 2 := hsqMoll.symm
    _ ≤ (eLpNorm f 2 volume).toReal ^ 2 := by
      have hsquare := mul_self_le_mul_self ENNReal.toReal_nonneg hnormMoll
      simpa only [pow_two] using hsquare

theorem eLpNorm_local_ae_le_global
    {d : ℕ} {s T : ℝ} (D : PDE.Parabolic.Energy.Data d)
    {F F₀ : Vec d × ℝ → ℝ} (hμ : D.μP ≤ slabMeasure d s T)
    (hF : F =ᵐ[slabMeasure d s T] F₀) :
    eLpNorm F 2 D.μP ≤ eLpNorm F₀ 2 (slabMeasure d s T) := by
  calc
    eLpNorm F 2 D.μP = eLpNorm F₀ 2 D.μP := by
      apply eLpNorm_congr_ae
      exact hF.filter_mono (ae_mono hμ)
    _ ≤ eLpNorm F₀ 2 (slabMeasure d s T) := eLpNorm_mono_measure F₀ hμ

theorem cauchyEnergyData_cutoff_slice_bound_of_norms
    {d : ℕ} (D : PDE.Parabolic.Energy.Data d) {R : ℝ} (hR : 0 < R)
    (hRone : 1 ≤ R)
    (htime : ∀ z, PDE.parTimeDeriv D.φ z = 0)
    (hphi : ∀ z, |D.φ z| ≤ 1)
    (hcross : ∀ z i, |2 * D.φ z * PDE.parSpaceGrad D.φ z i| ≤ 64 / R)
    {F V : ℝ} {G H : Fin d → ℝ}
    (hinit : (∫ x in D.K, D.φ (x, D.s) ^ 2 * D.u (x, D.s) ^ 2) ≤ F)
    (hV : (eLpNorm D.u 2 D.μP).toReal ≤ V)
    (hH : ∀ i, (eLpNorm (fun z => D.Du z i) 2 D.μP).toReal ≤ H i)
    (hG : ∀ i, (eLpNorm (fun z => D.G z i) 2 D.μP).toReal ≤ G i)
    (hGnonneg : ∀ i, 0 ≤ G i) :
    (∫ x in D.K, D.φ (x, D.t) ^ 2 * D.u (x, D.t) ^ 2) ≤
      F + 2 * ∑ i : Fin d, (G i * H i + 64 * G i * V) := by
  have hcut := cauchyEnergyData_cutoff_slice_bound D hR htime hphi hcross
  have hcoef : 64 / R ≤ 64 := by
    rw [div_le_iff₀ hR]
    nlinarith
  have hsum :
      (∑ i : Fin d,
        ((eLpNorm (fun z => D.G z i) 2 D.μP).toReal *
            (eLpNorm (fun z => D.Du z i) 2 D.μP).toReal +
          (64 / R) * (eLpNorm (fun z => D.G z i) 2 D.μP).toReal *
            (eLpNorm D.u 2 D.μP).toReal)) ≤
        ∑ i : Fin d, (G i * H i + 64 * G i * V) := by
    apply Finset.sum_le_sum
    intro i hi
    have hg0 : 0 ≤ (eLpNorm (fun z => D.G z i) 2 D.μP).toReal := ENNReal.toReal_nonneg
    have hh0 : 0 ≤ (eLpNorm (fun z => D.Du z i) 2 D.μP).toReal := ENNReal.toReal_nonneg
    have hv0 : 0 ≤ (eLpNorm D.u 2 D.μP).toReal := ENNReal.toReal_nonneg
    have hfirst := mul_le_mul (hG i) (hH i) hh0 (hGnonneg i)
    have hcross₁ := mul_le_mul hcoef (hG i) hg0 (by norm_num)
    have hcross₂ := mul_le_mul hcross₁ hV hv0
      (mul_nonneg (by norm_num) (hGnonneg i))
    exact add_le_add hfirst (by simpa [mul_assoc] using hcross₂)
  calc
    (∫ x in D.K, D.φ (x, D.t) ^ 2 * D.u (x, D.t) ^ 2) ≤
        (∫ x in D.K, D.φ (x, D.s) ^ 2 * D.u (x, D.s) ^ 2) +
          2 * ∑ i : Fin d,
            ((eLpNorm (fun z => D.G z i) 2 D.μP).toReal *
                (eLpNorm (fun z => D.Du z i) 2 D.μP).toReal +
              (64 / R) * (eLpNorm (fun z => D.G z i) 2 D.μP).toReal *
                (eLpNorm D.u 2 D.μP).toReal) := hcut
    _ ≤ F + 2 * ∑ i : Fin d, (G i * H i + 64 * G i * V) := by
      exact add_le_add hinit (mul_le_mul_of_nonneg_left hsum (by norm_num))

end PDE.Parabolic.Lions
