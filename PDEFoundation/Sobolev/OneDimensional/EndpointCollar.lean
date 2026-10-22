module

public import PDEFoundation.Sobolev.OneDimensional.ContinuousWeakIncrement

/-!
# Endpoint collar bounds for one-dimensional weak representatives

This module records the scale-sharp collar estimate for the positive part of
a continuous one-dimensional `H¹` representative above a prescribed endpoint
level.  The constant is exactly one.  These estimates are the quantitative
input for cutting off functions whose trace is bounded by that level.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory Set

noncomputable section

/-- If the left endpoint of a continuous one-dimensional weak representative
is at most `k`, then its positive part above `k` has the exact constant-one
`L²` collar bound on every left subinterval. -/
theorem setIntegral_sq_max_sub_const_le_left_endpoint_collar
    {a b c k : ℝ} (hab : a < b) (hc : c ∈ Icc a b) {v g : ℝ → ℝ}
    (hv : ContinuousOn v (Icc a b))
    (hvLp : MemLp v 2 (volume.restrict (Ioo a b)))
    (hg : MemLp g 2 (volume.restrict (Icc a b)))
    (hweak : HasWeakDerivOnIoo a b v g)
    (hva : v a ≤ k) :
    ∫ x in Icc a c, (max (v x - k) 0) ^ 2 ∂volume ≤
      (c - a) ^ 2 * ∫ x in Icc a c, |g x| ^ (2 : ℝ) ∂volume := by
  let A : ℝ := ∫ x in Icc a c, |g x| ^ (2 : ℝ) ∂volume
  have hA : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg fun x ↦ Real.rpow_nonneg (abs_nonneg (g x)) _
  have hAint : IntegrableOn (fun x ↦ |g x| ^ (2 : ℝ)) (Icc a c) volume := by
    simpa only [Real.norm_eq_abs] using!
      (hg.mono_measure
        (Measure.restrict_mono (Icc_subset_Icc le_rfl hc.2) le_rfl)).integrable_norm_rpow
          (by norm_num) (by norm_num)
  have htrunc_int : IntegrableOn (fun x ↦ (max (v x - k) 0) ^ 2)
      (Icc a c) volume := by
    have hcont : ContinuousOn (fun x ↦ max (v x - k) 0) (Icc a c) := by
      exact ((hv.mono (Icc_subset_Icc le_rfl hc.2)).sub continuousOn_const).sup continuousOn_const
    exact (hcont.pow 2).integrableOn_Icc
  have hconst_int : IntegrableOn (fun _x : ℝ ↦ (c - a) * A) (Icc a c) volume :=
    integrableOn_const (by rw [Real.volume_Icc]; simp)
  calc
    ∫ x in Icc a c, (max (v x - k) 0) ^ 2 ∂volume ≤
        ∫ _x in Icc a c, (c - a) * A ∂volume := by
      refine setIntegral_mono_ae_restrict htrunc_int hconst_int ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      have hinc := ContinuousOn.sq_abs_increment_le_of_hasWeakDerivOnIoo
        hab hv hvLp hg hweak (s := a) (t := x) ⟨le_rfl, hab.le⟩
        ⟨hx.1, hx.2.trans hc.2⟩ hx.1
      have hmax : max (v x - k) 0 ≤ |v x - v a| := by
        refine max_le ?_ (abs_nonneg _)
        exact (sub_le_sub_left hva (v x)).trans (le_abs_self _)
      have hsquare : (max (v x - k) 0) ^ 2 ≤ |v x - v a| ^ 2 := by
        exact pow_le_pow_left₀ (le_max_right _ _) hmax 2
      have hAmono : ∫ y in Icc a x, |g y| ^ (2 : ℝ) ∂volume ≤ A := by
        dsimp [A]
        exact setIntegral_mono_set hAint
          (Filter.Eventually.of_forall fun y ↦ Real.rpow_nonneg (abs_nonneg (g y)) _)
          (Filter.Eventually.of_forall fun y hy ↦ (Icc_subset_Icc le_rfl hx.2) hy)
      calc
        (max (v x - k) 0) ^ 2 ≤ |v x - v a| ^ 2 := hsquare
        _ ≤ (x - a) * ∫ y in Icc a x, |g y| ^ (2 : ℝ) ∂volume := hinc
        _ ≤ (x - a) * A :=
          mul_le_mul_of_nonneg_left hAmono (sub_nonneg.mpr hx.1)
        _ ≤ (c - a) * A :=
          mul_le_mul_of_nonneg_right (sub_le_sub_right hx.2 a) hA
    _ = (c - a) ^ 2 * A := by
      rw [setIntegral_const, measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hc.1)]
      simp only [smul_eq_mul]
      ring
    _ = _ := rfl

/-- If the right endpoint of a continuous one-dimensional weak representative
is at most `k`, then its positive part above `k` has the exact constant-one
`L²` collar bound on every right subinterval. -/
theorem setIntegral_sq_max_sub_const_le_right_endpoint_collar
    {a b c k : ℝ} (hab : a < b) (hc : c ∈ Icc a b) {v g : ℝ → ℝ}
    (hv : ContinuousOn v (Icc a b))
    (hvLp : MemLp v 2 (volume.restrict (Ioo a b)))
    (hg : MemLp g 2 (volume.restrict (Icc a b)))
    (hweak : HasWeakDerivOnIoo a b v g)
    (hvb : v b ≤ k) :
    ∫ x in Icc c b, (max (v x - k) 0) ^ 2 ∂volume ≤
      (b - c) ^ 2 * ∫ x in Icc c b, |g x| ^ (2 : ℝ) ∂volume := by
  let A : ℝ := ∫ x in Icc c b, |g x| ^ (2 : ℝ) ∂volume
  have hA : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg fun x ↦ Real.rpow_nonneg (abs_nonneg (g x)) _
  have hAint : IntegrableOn (fun x ↦ |g x| ^ (2 : ℝ)) (Icc c b) volume := by
    simpa only [Real.norm_eq_abs] using!
      (hg.mono_measure
        (Measure.restrict_mono (Icc_subset_Icc hc.1 le_rfl) le_rfl)).integrable_norm_rpow
          (by norm_num) (by norm_num)
  have htrunc_int : IntegrableOn (fun x ↦ (max (v x - k) 0) ^ 2)
      (Icc c b) volume := by
    have hcont : ContinuousOn (fun x ↦ max (v x - k) 0) (Icc c b) := by
      exact ((hv.mono (Icc_subset_Icc hc.1 le_rfl)).sub continuousOn_const).sup continuousOn_const
    exact (hcont.pow 2).integrableOn_Icc
  have hconst_int : IntegrableOn (fun _x : ℝ ↦ (b - c) * A) (Icc c b) volume :=
    integrableOn_const (by rw [Real.volume_Icc]; simp)
  calc
    ∫ x in Icc c b, (max (v x - k) 0) ^ 2 ∂volume ≤
        ∫ _x in Icc c b, (b - c) * A ∂volume := by
      refine setIntegral_mono_ae_restrict htrunc_int hconst_int ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      have hinc := ContinuousOn.sq_abs_increment_le_of_hasWeakDerivOnIoo
        hab hv hvLp hg hweak (s := x) (t := b)
        ⟨hc.1.trans hx.1, hx.2⟩ ⟨hab.le, le_rfl⟩ hx.2
      have hmax : max (v x - k) 0 ≤ |v b - v x| := by
        refine max_le ?_ (abs_nonneg _)
        calc
          v x - k ≤ v x - v b := sub_le_sub_left hvb (v x)
          _ ≤ |v b - v x| := by simpa only [abs_sub_comm] using le_abs_self (v x - v b)
      have hsquare : (max (v x - k) 0) ^ 2 ≤ |v b - v x| ^ 2 := by
        exact pow_le_pow_left₀ (le_max_right _ _) hmax 2
      have hAmono : ∫ y in Icc x b, |g y| ^ (2 : ℝ) ∂volume ≤ A := by
        dsimp [A]
        exact setIntegral_mono_set hAint
          (Filter.Eventually.of_forall fun y ↦ Real.rpow_nonneg (abs_nonneg (g y)) _)
          (Filter.Eventually.of_forall fun y hy ↦ (Icc_subset_Icc hx.1 le_rfl) hy)
      calc
        (max (v x - k) 0) ^ 2 ≤ |v b - v x| ^ 2 := hsquare
        _ ≤ (b - x) * ∫ y in Icc x b, |g y| ^ (2 : ℝ) ∂volume := hinc
        _ ≤ (b - x) * A :=
          mul_le_mul_of_nonneg_left hAmono (sub_nonneg.mpr hx.2)
        _ ≤ (b - c) * A :=
          mul_le_mul_of_nonneg_right (sub_le_sub_left hx.1 b) hA
    _ = (b - c) ^ 2 * A := by
      rw [setIntegral_const, measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hc.2)]
      simp only [smul_eq_mul]
      ring
    _ = _ := rfl

end

end PDE
