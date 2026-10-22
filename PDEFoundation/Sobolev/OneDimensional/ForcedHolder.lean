module

public import PDEFoundation.Sobolev.OneDimensional.WeakPrimitiveRepresentation
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! # Exact forced Hölder increments on scalar intervals -/

@[expose] public section

namespace PDE

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The exact `L¹` to `Lᵖ` comparison on finite measure, written with the
real-valued norm. Its measure exponent is `1 - 1 / p`. -/
theorem integral_abs_le_eLpNorm_mul_measure_rpow
    {μ : Measure ℝ} [IsFiniteMeasure μ] {F : ℝ → ℝ} {p : ℝ}
    (hp : 1 < p) (hF : MemLp F (ENNReal.ofReal p) μ) :
    (∫ t, |F t| ∂μ) ≤ (eLpNorm F (ENNReal.ofReal p) μ).toReal *
      (μ Set.univ).toReal ^ (1 - 1 / p) := by
  have hpENN : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp.le
  have he : 0 ≤ 1 - 1 / p := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp.le
    norm_num at h
    simpa only [one_div] using sub_nonneg.mpr h
  have h1 : MemLp F 1 μ := hF.mono_exponent hpENN
  have hnorm : (eLpNorm F 1 μ).toReal = ∫ t, |F t| ∂μ := by
    rw [h1.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_one, inv_one, Real.rpow_one, Real.norm_eq_abs]
    exact ENNReal.toReal_ofReal (integral_nonneg fun t => abs_nonneg (F t))
  have hcomp := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpENN hF.aestronglyMeasurable
  simp only [ENNReal.toReal_one, div_one, ENNReal.toReal_ofReal (zero_lt_one.trans hp).le] at hcomp
  have htop : eLpNorm F (ENNReal.ofReal p) μ * μ Set.univ ^ (1 - 1 / p) ≠ ∞ :=
    ENNReal.mul_ne_top hF.eLpNorm_ne_top
      (ENNReal.rpow_ne_top_of_nonneg he (measure_ne_top μ Set.univ))
  have hreal := ENNReal.toReal_mono htop hcomp
  rw [hnorm, ENNReal.toReal_mul, ← ENNReal.toReal_rpow] at hreal
  exact hreal

/-- A subinterval carries at most its exact length power times the original
interval `Lᵖ` norm of the forcing. -/
theorem setIntegral_abs_le_eLpNorm_mul_sub_rpow
    {a b s t p : ℝ} {F : ℝ → ℝ} (hp : 1 < p)
    (hF : MemLp F (ENNReal.ofReal p) (volume.restrict (Ioo a b)))
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    (∫ x in Icc s t, |F x|) ≤
      (eLpNorm F (ENNReal.ofReal p) (volume.restrict (Ioo a b))).toReal *
        (t - s) ^ (1 - 1 / p) := by
  have hFclosed : MemLp F (ENNReal.ofReal p) (volume.restrict (Icc a b)) := by
    simpa only [restrict_Ioo_eq_restrict_Icc] using hF
  have hsubset := Icc_subset_Icc hs.1 ht.2
  have hFlocal := hFclosed.mono_measure (Measure.restrict_mono hsubset le_rfl)
  have hlocal := integral_abs_le_eLpNorm_mul_measure_rpow hp hFlocal
  have hnorm :
      (eLpNorm F (ENNReal.ofReal p) (volume.restrict (Icc s t))).toReal ≤
        (eLpNorm F (ENNReal.ofReal p) (volume.restrict (Ioo a b))).toReal := by
    apply ENNReal.toReal_mono hF.eLpNorm_ne_top
    rw [restrict_Ioo_eq_restrict_Icc]
    exact eLpNorm_mono_measure F (Measure.restrict_mono hsubset le_rfl)
  have hvolume : (volume.restrict (Icc s t) Set.univ).toReal = t - s := by
    rw [Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hst)]
  rw [hvolume] at hlocal
  exact hlocal.trans (mul_le_mul_of_nonneg_right hnorm
    (Real.rpow_nonneg (sub_nonneg.mpr hst) _))

/-- An actual almost everywhere derivative bound gives the exact forced
increment estimate on an ordered subinterval. -/
theorem abs_intervalIntegral_le_forced_bound
    {a b s t p A B : ℝ} {g F : ℝ → ℝ} (hp : 1 < p)
    (hg : MemLp g 2 (volume.restrict (Ioo a b)))
    (hF : MemLp F (ENNReal.ofReal p) (volume.restrict (Ioo a b)))
    (hB : 0 ≤ B)
    (hbound : ∀ᵐ x ∂volume.restrict (Ioo a b), |g x| ≤ A + B * |F x|)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    |∫ x in s..t, g x| ≤ A * (t - s) +
      B * (eLpNorm F (ENNReal.ofReal p) (volume.restrict (Ioo a b))).toReal *
        (t - s) ^ (1 - 1 / p) := by
  have hsubset := Icc_subset_Icc hs.1 ht.2
  have hgclosed : MemLp g 2 (volume.restrict (Icc a b)) := by
    simpa only [restrict_Ioo_eq_restrict_Icc] using hg
  have hFclosed : MemLp F (ENNReal.ofReal p) (volume.restrict (Icc a b)) := by
    simpa only [restrict_Ioo_eq_restrict_Icc] using hF
  have hglocal := hgclosed.mono_measure (Measure.restrict_mono hsubset le_rfl)
  have hFlocal := hFclosed.mono_measure (Measure.restrict_mono hsubset le_rfl)
  have hgabs : Integrable (fun x => |g x|) (volume.restrict (Icc s t)) := by
    simpa only [Real.norm_eq_abs] using (hglocal.integrable (by norm_num)).norm
  have hFabs : Integrable (fun x => |F x|) (volume.restrict (Icc s t)) := by
    simpa only [Real.norm_eq_abs] using
      (hFlocal.integrable (ENNReal.one_le_ofReal.mpr hp.le)).norm
  have hconst : Integrable (fun _ : ℝ => A) (volume.restrict (Icc s t)) := integrable_const A
  have hbclosed : ∀ᵐ x ∂volume.restrict (Icc a b), |g x| ≤ A + B * |F x| := by
    simpa only [restrict_Ioo_eq_restrict_Icc] using hbound
  have hblocal := ae_restrict_of_ae_restrict_of_subset hsubset hbclosed
  have hfirst : |∫ x in s..t, g x| ≤ ∫ x in Icc s t, |g x| := by
    rw [intervalIntegral.integral_of_le hst, ← integral_Icc_eq_integral_Ioc]
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm (g : ℝ → ℝ))
  have hconstant : (∫ _x in Icc s t, A) = A * (t - s) := by
    rw [setIntegral_const, measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hst)]
    simp only [smul_eq_mul, mul_comm]
  calc
    |∫ x in s..t, g x| ≤ ∫ x in Icc s t, |g x| := hfirst
    _ ≤ ∫ x in Icc s t, A + B * |F x| :=
      integral_mono_ae hgabs (hconst.add (hFabs.const_mul B)) hblocal
    _ = A * (t - s) + B * ∫ x in Icc s t, |F x| := by
      rw [integral_add hconst (hFabs.const_mul B), hconstant, integral_const_mul]
    _ ≤ A * (t - s) + B *
        ((eLpNorm F (ENNReal.ofReal p) (volume.restrict (Ioo a b))).toReal *
          (t - s) ^ (1 - 1 / p)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (setIntegral_abs_le_eLpNorm_mul_sub_rpow hp hF hs ht hst) hB)
    _ = _ := by ring

/-- A genuine scalar `H¹` weak derivative and an `Lᵖ` forcing bound produce a
continuous representative with exact constant-one forced Hölder increments. -/
theorem exists_continuousOn_representative_with_forced_holder_increment
    {a b p A B : ℝ} (hab : a < b) {u g F : ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (Ioo a b)))
    (hg : MemLp g 2 (volume.restrict (Ioo a b)))
    (hweak : HasWeakDerivOnIoo a b u g)
    (hp : 1 < p)
    (hF : MemLp F (ENNReal.ofReal p) (volume.restrict (Ioo a b)))
    (_hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ᵐ t ∂volume.restrict (Ioo a b), |g t| ≤ A + B * |F t|) :
    ∃ v : ℝ → ℝ, ContinuousOn v (Icc a b) ∧
      u =ᵐ[volume.restrict (Ioo a b)] v ∧
      ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
        |v x - v y| ≤ A * |x - y| +
          B * (eLpNorm F (ENNReal.ofReal p) (volume.restrict (Ioo a b))).toReal *
            |x - y| ^ (1 - 1 / p) := by
  have hgclosed : MemLp g 2 (volume.restrict (Icc a b)) := by
    simpa only [restrict_Ioo_eq_restrict_Icc] using hg
  obtain ⟨v, hvcont, huv, hvinc⟩ :=
    exists_continuousOn_representative_of_hasWeakDerivOnIoo hab hu hgclosed hweak
  refine ⟨v, hvcont, huv, ?_⟩
  intro x hx y hy
  rcases le_total x y with hxy | hyx
  · have h := abs_intervalIntegral_le_forced_bound hp hg hF hB hbound hx hy hxy
    rw [← hvinc x hx y hy] at h
    rw [abs_sub_comm (v x) (v y), abs_sub_comm x y,
      abs_of_nonneg (sub_nonneg.mpr hxy)]
    exact h
  · have h := abs_intervalIntegral_le_forced_bound hp hg hF hB hbound hy hx hyx
    rw [← hvinc y hy x hx] at h
    rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact h

end

end PDE
