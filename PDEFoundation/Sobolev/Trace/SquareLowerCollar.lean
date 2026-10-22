module

public import PDEFoundation.Measure.AxisBoxVolume
public import PDEFoundation.Sobolev.OneDimensional.EndpointCollar
public import PDEFoundation.Sobolev.Trace.SquareCollarUnion
public import PDEFoundation.Sobolev.Trace.SquareNormalTrace

/-!
# Lower square-trace collar estimates

This module proves the lower-trace counterpart of `SquareCollar` directly
from the canonical normal slice representatives retained by
`SquareNormalTraceCertificate`.  In particular, it does not construct a
negated trace certificate: the endpoint inequality on each individual slice
is proved for `max (k - v) 0` itself.

Every estimate has constant one and the exact factor `δ²`.
-/

@[expose] public section

namespace PDE

open Filter MeasureTheory Set

noncomputable section

private theorem setIntegral_sq_max_const_sub_le_left_endpoint_collar
    {a b c k : ℝ} (hab : a < b) (hc : c ∈ Icc a b) {v g : ℝ → ℝ}
    (hv : ContinuousOn v (Icc a b))
    (hvLp : MemLp v 2 (volume.restrict (Ioo a b)))
    (hg : MemLp g 2 (volume.restrict (Icc a b)))
    (hweak : HasWeakDerivOnIoo a b v g)
    (hva : k ≤ v a) :
    ∫ x in Icc a c, (max (k - v x) 0) ^ 2 ∂volume ≤
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
  have htruncInt : IntegrableOn (fun x ↦ (max (k - v x) 0) ^ 2)
      (Icc a c) volume := by
    have hcont : ContinuousOn (fun x ↦ max (k - v x) 0) (Icc a c) := by
      exact (continuousOn_const.sub (hv.mono (Icc_subset_Icc le_rfl hc.2))).sup
        continuousOn_const
    exact (hcont.pow 2).integrableOn_Icc
  have hconstInt : IntegrableOn (fun _x : ℝ ↦ (c - a) * A) (Icc a c) volume :=
    integrableOn_const (by rw [Real.volume_Icc]; simp)
  calc
    ∫ x in Icc a c, (max (k - v x) 0) ^ 2 ∂volume ≤
        ∫ _x in Icc a c, (c - a) * A ∂volume := by
      refine setIntegral_mono_ae_restrict htruncInt hconstInt ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      have hinc := ContinuousOn.sq_abs_increment_le_of_hasWeakDerivOnIoo
        hab hv hvLp hg hweak (s := a) (t := x) ⟨le_rfl, hab.le⟩
        ⟨hx.1, hx.2.trans hc.2⟩ hx.1
      have hmax : max (k - v x) 0 ≤ |v x - v a| := by
        refine max_le ?_ (abs_nonneg _)
        calc
          k - v x ≤ v a - v x := sub_le_sub_right hva (v x)
          _ ≤ |v x - v a| := by simpa only [abs_sub_comm] using le_abs_self (v a - v x)
      have hsq : (max (k - v x) 0) ^ 2 ≤ |v x - v a| ^ 2 :=
        pow_le_pow_left₀ (le_max_right _ _) hmax 2
      have hAmono : ∫ y in Icc a x, |g y| ^ (2 : ℝ) ∂volume ≤ A := by
        dsimp [A]
        exact setIntegral_mono_set hAint
          (Filter.Eventually.of_forall fun y ↦ Real.rpow_nonneg (abs_nonneg (g y)) _)
          (Filter.Eventually.of_forall fun y hy ↦ (Icc_subset_Icc le_rfl hx.2) hy)
      calc
        (max (k - v x) 0) ^ 2 ≤ |v x - v a| ^ 2 := hsq
        _ ≤ (x - a) * ∫ y in Icc a x, |g y| ^ (2 : ℝ) ∂volume := hinc
        _ ≤ (x - a) * A := mul_le_mul_of_nonneg_left hAmono (sub_nonneg.mpr hx.1)
        _ ≤ (c - a) * A :=
          mul_le_mul_of_nonneg_right (sub_le_sub_right hx.2 a) hA
    _ = (c - a) ^ 2 * A := by
      rw [setIntegral_const, measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hc.1)]
      simp only [smul_eq_mul]
      ring
    _ = _ := rfl

private theorem setIntegral_sq_max_const_sub_le_right_endpoint_collar
    {a b c k : ℝ} (hab : a < b) (hc : c ∈ Icc a b) {v g : ℝ → ℝ}
    (hv : ContinuousOn v (Icc a b))
    (hvLp : MemLp v 2 (volume.restrict (Ioo a b)))
    (hg : MemLp g 2 (volume.restrict (Icc a b)))
    (hweak : HasWeakDerivOnIoo a b v g)
    (hvb : k ≤ v b) :
    ∫ x in Icc c b, (max (k - v x) 0) ^ 2 ∂volume ≤
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
  have htruncInt : IntegrableOn (fun x ↦ (max (k - v x) 0) ^ 2)
      (Icc c b) volume := by
    have hcont : ContinuousOn (fun x ↦ max (k - v x) 0) (Icc c b) := by
      exact (continuousOn_const.sub (hv.mono (Icc_subset_Icc hc.1 le_rfl))).sup
        continuousOn_const
    exact (hcont.pow 2).integrableOn_Icc
  have hconstInt : IntegrableOn (fun _x : ℝ ↦ (b - c) * A) (Icc c b) volume :=
    integrableOn_const (by rw [Real.volume_Icc]; simp)
  calc
    ∫ x in Icc c b, (max (k - v x) 0) ^ 2 ∂volume ≤
        ∫ _x in Icc c b, (b - c) * A ∂volume := by
      refine setIntegral_mono_ae_restrict htruncInt hconstInt ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      have hinc := ContinuousOn.sq_abs_increment_le_of_hasWeakDerivOnIoo
        hab hv hvLp hg hweak (s := x) (t := b)
        ⟨hc.1.trans hx.1, hx.2⟩ ⟨hab.le, le_rfl⟩ hx.2
      have hmax : max (k - v x) 0 ≤ |v b - v x| := by
        refine max_le ?_ (abs_nonneg _)
        calc
          k - v x ≤ v b - v x := sub_le_sub_right hvb (v x)
          _ ≤ |v b - v x| := le_abs_self _
      have hsq : (max (k - v x) 0) ^ 2 ≤ |v b - v x| ^ 2 :=
        pow_le_pow_left₀ (le_max_right _ _) hmax 2
      have hAmono : ∫ y in Icc x b, |g y| ^ (2 : ℝ) ∂volume ≤ A := by
        dsimp [A]
        exact setIntegral_mono_set hAint
          (Filter.Eventually.of_forall fun y ↦ Real.rpow_nonneg (abs_nonneg (g y)) _)
          (Filter.Eventually.of_forall fun y hy ↦ (Icc_subset_Icc hx.1 le_rfl) hy)
      calc
        (max (k - v x) 0) ^ 2 ≤ |v b - v x| ^ 2 := hsq
        _ ≤ (b - x) * ∫ y in Icc x b, |g y| ^ (2 : ℝ) ∂volume := hinc
        _ ≤ (b - x) * A := mul_le_mul_of_nonneg_left hAmono (sub_nonneg.mpr hx.2)
        _ ≤ (b - c) * A :=
          mul_le_mul_of_nonneg_right (sub_le_sub_left hx.1 b) hA
    _ = (b - c) ^ 2 * A := by
      rw [setIntegral_const, measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hc.2)]
      simp only [smul_eq_mul]
      ring
    _ = _ := rfl

namespace SquareNormalTraceCertificate

/-- A lower top trace bound controls the negative part below `k` in the top
collar, with exact coefficient `δ²`. -/
theorem setIntegral_sq_max_const_sub_le_top_collar
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {x₀ : Vec 2} {r δ k : ℝ}
    (C : SquareNormalTraceCertificate F u g x₀ r)
    (hδ : δ ∈ Icc 0 (2 * r))
    (htop : ∀ s ∈ Icc (x₀ 0 - r) (x₀ 0 + r),
      k ≤ C.traceProvenance.trace.top s) :
    ∫ x in axisBox ![x₀ 0 - r, x₀ 1 + r - δ]
        ![x₀ 0 + r, x₀ 1 + r], (max (k - u x) 0) ^ 2 ∂volume ≤
      δ ^ 2 * ∫ x in axisBox ![x₀ 0 - r, x₀ 1 + r - δ]
        ![x₀ 0 + r, x₀ 1 + r], (g x 1) ^ 2 ∂volume := by
  let a := x₀ 0 - r
  let b := x₀ 0 + r
  let c := x₀ 1 - r
  let d := x₀ 1 + r
  let q := d - δ
  let Q := axisBox ![a, q] ![b, d]
  let Q₀ := axisBox ![a, c] ![b, d]
  have hab : a < b := by dsimp [a, b]; linarith [C.radius_pos]
  have hcd : c < d := by dsimp [c, d]; linarith [C.radius_pos]
  have hq : q ∈ Icc c d := by
    dsimp [q, c, d]
    constructor <;> linarith [hδ.1, hδ.2]
  have hQ : Q ⊆ Q₀ := by
    apply axisBox_mono
    · intro i; fin_cases i <;> simp only [a, q]
      · exact le_rfl
      · exact hq.1
    · intro i; fin_cases i <;> rfl
  have huQ : MemL2On Q u := memLpOn_mono hQ C.normalSliceData.valueMemL2
  have hgQ : MemL2On Q (fun x => g x 1) :=
    memLpOn_mono hQ (C.normalSliceData.gradientMemL2 1)
  let : IsFiniteMeasure (volume.restrict Q) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (volume_axisBox_ne_top _ _).lt_top⟩
  have htruncQ : MemL2On Q (fun x => max (k - u x) 0) := by
    have hshift : MemLp (fun x => k - u x) 2 (volume.restrict Q) := by
      simpa only [Pi.sub_apply] using! (memLp_const k).sub huQ
    simpa only using hshift.pos_part
  have htruncInt : IntegrableOn (fun x => (max (k - u x) 0) ^ 2) Q volume := by
    simpa only [IntegrableOn] using htruncQ.integrable_sq
  have hgInt : IntegrableOn (fun x => (g x 1) ^ 2) Q volume := by
    simpa only [IntegrableOn] using hgQ.integrable_sq
  have houterTrunc : IntegrableOn
      (fun s => ∫ t in Ioo q d, (max (k - u (squarePoint s t)) 0) ^ 2)
      (Ioo a b) volume :=
    integrableOn_axisBox_innerIntegral_squarePoint htruncInt
  have houterGrad : IntegrableOn
      (fun s => ∫ t in Ioo q d, (g (squarePoint s t) 1) ^ 2)
      (Ioo a b) volume :=
    integrableOn_axisBox_innerIntegral_squarePoint hgInt
  have hnormal := C.ae_hasVerticalNormalSliceLimit
  have hraw := ae_verticalSliceRawL2DataAt C.normalSliceData
  have hinner : ∀ᵐ s ∂(volume.restrict (Ioo a b)),
      (∫ t in Ioo q d, (max (k - u (squarePoint s t)) 0) ^ 2) ≤
        δ ^ 2 * ∫ t in Ioo q d, (g (squarePoint s t) 1) ^ 2 := by
    filter_upwards [hnormal, hraw, ae_restrict_mem measurableSet_Ioo] with
      s hs hraws hsMem
    have hsIcc : s ∈ Icc (x₀ 0 - r) (x₀ 0 + r) := ⟨hsMem.1.le, hsMem.2.le⟩
    have hvLpIcc : MemLp (verticalSliceUniformLimit F s) 2
        (volume.restrict (Icc c d)) := hraws.valueMemL2.ae_eq hs.aeEq.symm
    have hvLp : MemLp (verticalSliceUniformLimit F s) 2
        (volume.restrict (Ioo c d)) :=
      hvLpIcc.mono_measure (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)
    have hvTop : k ≤ verticalSliceUniformLimit F s d := by
      rw [C.verticalSliceUniformLimit_eq_top]
      exact htop s hsIcc
    have hcollar := setIntegral_sq_max_const_sub_le_right_endpoint_collar
      hcd hq hs.continuousOn hvLp hraws.gradientMemL2 hs.hasWeakDeriv hvTop
    have hdq : d - q = δ := by dsimp [q]; ring
    have hae : (fun t => (max (k - verticalSliceUniformLimit F s t) 0) ^ 2)
        =ᵐ[volume.restrict (Ioo q d)]
        fun t => (max (k - u (squarePoint s t)) 0) ^ 2 := by
      refine (ae_restrict_of_ae_restrict_of_subset ?_ hs.aeEq).mono ?_
      · exact fun t ht => ⟨hq.1.trans ht.1.le, ht.2.le⟩
      · intro t ht
        change verticalSliceUniformLimit F s t = u (squarePoint s t) at ht
        change (max (k - verticalSliceUniformLimit F s t) 0) ^ 2 =
          (max (k - u (squarePoint s t)) 0) ^ 2
        rw [ht]
    calc
      (∫ t in Ioo q d, (max (k - u (squarePoint s t)) 0) ^ 2) =
          ∫ t in Icc q d, (max (k - verticalSliceUniformLimit F s t) 0) ^ 2 := by
        rw [integral_Icc_eq_integral_Ioo]
        exact (integral_congr_ae hae).symm
      _ ≤ δ ^ 2 * ∫ t in Icc q d, |g (squarePoint s t) 1| ^ (2 : ℝ) := by
        rw [← hdq]
        exact hcollar
      _ = δ ^ 2 * ∫ t in Ioo q d, (g (squarePoint s t) 1) ^ 2 := by
        rw [integral_Icc_eq_integral_Ioo]
        congr 2
        funext t
        rw [Real.rpow_two, sq_abs]
  have houter :
      (∫ s in Ioo a b, ∫ t in Ioo q d, (max (k - u (squarePoint s t)) 0) ^ 2) ≤
        ∫ s in Ioo a b, δ ^ 2 * ∫ t in Ioo q d, (g (squarePoint s t) 1) ^ 2 := by
    apply setIntegral_mono_ae_restrict houterTrunc
      (by simpa only [IntegrableOn] using houterGrad.const_mul (δ ^ 2))
    exact hinner
  change (∫ x in Q, (max (k - u x) 0) ^ 2) ≤ δ ^ 2 * ∫ x in Q, (g x 1) ^ 2
  rw [integralOn_axisBox_eq_integral_squarePoint htruncInt,
    integralOn_axisBox_eq_integral_squarePoint hgInt, ← MeasureTheory.integral_const_mul]
  exact houter

/-- A lower bottom trace bound controls the negative part below `k` in the
bottom collar, with exact coefficient `δ²`. -/
theorem setIntegral_sq_max_const_sub_le_bottom_collar
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {x₀ : Vec 2} {r δ k : ℝ}
    (C : SquareNormalTraceCertificate F u g x₀ r)
    (hδ : δ ∈ Icc 0 (2 * r))
    (hbottom : ∀ s ∈ Icc (x₀ 0 - r) (x₀ 0 + r),
      k ≤ C.traceProvenance.trace.bottom s) :
    ∫ x in axisBox ![x₀ 0 - r, x₀ 1 - r]
        ![x₀ 0 + r, x₀ 1 - r + δ], (max (k - u x) 0) ^ 2 ∂volume ≤
      δ ^ 2 * ∫ x in axisBox ![x₀ 0 - r, x₀ 1 - r]
        ![x₀ 0 + r, x₀ 1 - r + δ], (g x 1) ^ 2 ∂volume := by
  let a := x₀ 0 - r
  let b := x₀ 0 + r
  let c := x₀ 1 - r
  let d := x₀ 1 + r
  let q := c + δ
  let Q := axisBox ![a, c] ![b, q]
  let Q₀ := axisBox ![a, c] ![b, d]
  have hab : a < b := by dsimp [a, b]; linarith [C.radius_pos]
  have hcd : c < d := by dsimp [c, d]; linarith [C.radius_pos]
  have hq : q ∈ Icc c d := by
    dsimp [q, c, d]
    constructor <;> linarith [hδ.1, hδ.2]
  have hQ : Q ⊆ Q₀ := by
    apply axisBox_mono
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> simp only [q]
      · exact le_rfl
      · exact hq.2
  have huQ : MemL2On Q u := memLpOn_mono hQ C.normalSliceData.valueMemL2
  have hgQ : MemL2On Q (fun x => g x 1) :=
    memLpOn_mono hQ (C.normalSliceData.gradientMemL2 1)
  let : IsFiniteMeasure (volume.restrict Q) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (volume_axisBox_ne_top _ _).lt_top⟩
  have htruncQ : MemL2On Q (fun x => max (k - u x) 0) := by
    have hshift : MemLp (fun x => k - u x) 2 (volume.restrict Q) := by
      simpa only [Pi.sub_apply] using! (memLp_const k).sub huQ
    simpa only using hshift.pos_part
  have htruncInt : IntegrableOn (fun x => (max (k - u x) 0) ^ 2) Q volume := by
    simpa only [IntegrableOn] using htruncQ.integrable_sq
  have hgInt : IntegrableOn (fun x => (g x 1) ^ 2) Q volume := by
    simpa only [IntegrableOn] using hgQ.integrable_sq
  have houterTrunc : IntegrableOn
      (fun s => ∫ t in Ioo c q, (max (k - u (squarePoint s t)) 0) ^ 2)
      (Ioo a b) volume :=
    integrableOn_axisBox_innerIntegral_squarePoint htruncInt
  have houterGrad : IntegrableOn
      (fun s => ∫ t in Ioo c q, (g (squarePoint s t) 1) ^ 2)
      (Ioo a b) volume :=
    integrableOn_axisBox_innerIntegral_squarePoint hgInt
  have hnormal := C.ae_hasVerticalNormalSliceLimit
  have hraw := ae_verticalSliceRawL2DataAt C.normalSliceData
  have hinner : ∀ᵐ s ∂(volume.restrict (Ioo a b)),
      (∫ t in Ioo c q, (max (k - u (squarePoint s t)) 0) ^ 2) ≤
        δ ^ 2 * ∫ t in Ioo c q, (g (squarePoint s t) 1) ^ 2 := by
    filter_upwards [hnormal, hraw, ae_restrict_mem measurableSet_Ioo] with
      s hs hraws hsMem
    have hsIcc : s ∈ Icc (x₀ 0 - r) (x₀ 0 + r) := ⟨hsMem.1.le, hsMem.2.le⟩
    have hvLpIcc : MemLp (verticalSliceUniformLimit F s) 2
        (volume.restrict (Icc c d)) := hraws.valueMemL2.ae_eq hs.aeEq.symm
    have hvLp : MemLp (verticalSliceUniformLimit F s) 2
        (volume.restrict (Ioo c d)) :=
      hvLpIcc.mono_measure (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)
    have hvBottom : k ≤ verticalSliceUniformLimit F s c := by
      rw [C.verticalSliceUniformLimit_eq_bottom]
      exact hbottom s hsIcc
    have hcollar := setIntegral_sq_max_const_sub_le_left_endpoint_collar
      hcd hq hs.continuousOn hvLp hraws.gradientMemL2 hs.hasWeakDeriv hvBottom
    have hqc : q - c = δ := by dsimp [q]; ring
    have hae : (fun t => (max (k - verticalSliceUniformLimit F s t) 0) ^ 2)
        =ᵐ[volume.restrict (Ioo c q)]
        fun t => (max (k - u (squarePoint s t)) 0) ^ 2 := by
      refine (ae_restrict_of_ae_restrict_of_subset ?_ hs.aeEq).mono ?_
      · exact fun t ht => ⟨ht.1.le, ht.2.le.trans hq.2⟩
      · intro t ht
        change verticalSliceUniformLimit F s t = u (squarePoint s t) at ht
        change (max (k - verticalSliceUniformLimit F s t) 0) ^ 2 =
          (max (k - u (squarePoint s t)) 0) ^ 2
        rw [ht]
    calc
      (∫ t in Ioo c q, (max (k - u (squarePoint s t)) 0) ^ 2) =
          ∫ t in Icc c q, (max (k - verticalSliceUniformLimit F s t) 0) ^ 2 := by
        rw [integral_Icc_eq_integral_Ioo]
        exact (integral_congr_ae hae).symm
      _ ≤ δ ^ 2 * ∫ t in Icc c q, |g (squarePoint s t) 1| ^ (2 : ℝ) := by
        rw [← hqc]
        exact hcollar
      _ = δ ^ 2 * ∫ t in Ioo c q, (g (squarePoint s t) 1) ^ 2 := by
        rw [integral_Icc_eq_integral_Ioo]
        congr 2
        funext t
        rw [Real.rpow_two, sq_abs]
  have houter :
      (∫ s in Ioo a b, ∫ t in Ioo c q, (max (k - u (squarePoint s t)) 0) ^ 2) ≤
        ∫ s in Ioo a b, δ ^ 2 * ∫ t in Ioo c q, (g (squarePoint s t) 1) ^ 2 := by
    apply setIntegral_mono_ae_restrict houterTrunc
      (by simpa only [IntegrableOn] using houterGrad.const_mul (δ ^ 2))
    exact hinner
  change (∫ x in Q, (max (k - u x) 0) ^ 2) ≤ δ ^ 2 * ∫ x in Q, (g x 1) ^ 2
  rw [integralOn_axisBox_eq_integral_squarePoint htruncInt,
    integralOn_axisBox_eq_integral_squarePoint hgInt, ← MeasureTheory.integral_const_mul]
  exact houter

/-- A lower right trace bound controls the negative part below `k` in the
right collar, with exact coefficient `δ²`. -/
theorem setIntegral_sq_max_const_sub_le_right_collar
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {x₀ : Vec 2} {r δ k : ℝ}
    (C : SquareNormalTraceCertificate F u g x₀ r)
    (hδ : δ ∈ Icc 0 (2 * r))
    (hright : ∀ t ∈ Icc (x₀ 1 - r) (x₀ 1 + r),
      k ≤ C.traceProvenance.trace.right t) :
    ∫ x in axisBox ![x₀ 0 + r - δ, x₀ 1 - r]
        ![x₀ 0 + r, x₀ 1 + r], (max (k - u x) 0) ^ 2 ∂volume ≤
      δ ^ 2 * ∫ x in axisBox ![x₀ 0 + r - δ, x₀ 1 - r]
        ![x₀ 0 + r, x₀ 1 + r], (g x 0) ^ 2 ∂volume := by
  let a := x₀ 0 - r
  let b := x₀ 0 + r
  let c := x₀ 1 - r
  let d := x₀ 1 + r
  let q := b - δ
  let Q := axisBox ![q, c] ![b, d]
  let Q₀ := axisBox ![a, c] ![b, d]
  have hab : a < b := by dsimp [a, b]; linarith [C.radius_pos]
  have hcd : c < d := by dsimp [c, d]; linarith [C.radius_pos]
  have hq : q ∈ Icc a b := by
    dsimp [q, a, b]
    constructor <;> linarith [hδ.1, hδ.2]
  have hQ : Q ⊆ Q₀ := by
    apply axisBox_mono
    · intro i; fin_cases i <;> simp only [a, c, q]
      · exact hq.1
      · exact le_rfl
    · intro i; fin_cases i <;> rfl
  have huQ : MemL2On Q u := memLpOn_mono hQ C.normalSliceData.valueMemL2
  have hgQ : MemL2On Q (fun x => g x 0) :=
    memLpOn_mono hQ (C.normalSliceData.gradientMemL2 0)
  let : IsFiniteMeasure (volume.restrict Q) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (volume_axisBox_ne_top _ _).lt_top⟩
  have htruncQ : MemL2On Q (fun x => max (k - u x) 0) := by
    have hshift : MemLp (fun x => k - u x) 2 (volume.restrict Q) := by
      simpa only [Pi.sub_apply] using! (memLp_const k).sub huQ
    simpa only using hshift.pos_part
  have htruncInt : IntegrableOn (fun x => (max (k - u x) 0) ^ 2) Q volume := by
    simpa only [IntegrableOn] using htruncQ.integrable_sq
  have hgInt : IntegrableOn (fun x => (g x 0) ^ 2) Q volume := by
    simpa only [IntegrableOn] using hgQ.integrable_sq
  have houterTrunc : IntegrableOn
      (fun t => ∫ s in Ioo q b, (max (k - u (squarePoint s t)) 0) ^ 2)
      (Ioo c d) volume :=
    integrableOn_axisBox_outerSecond_innerIntegral_squarePoint htruncInt
  have houterGrad : IntegrableOn
      (fun t => ∫ s in Ioo q b, (g (squarePoint s t) 0) ^ 2)
      (Ioo c d) volume :=
    integrableOn_axisBox_outerSecond_innerIntegral_squarePoint hgInt
  have hnormal := C.ae_hasHorizontalNormalSliceLimit
  have hraw := ae_horizontalSliceRawL2DataAt C.normalSliceData
  have hinner : ∀ᵐ t ∂(volume.restrict (Ioo c d)),
      (∫ s in Ioo q b, (max (k - u (squarePoint s t)) 0) ^ 2) ≤
        δ ^ 2 * ∫ s in Ioo q b, (g (squarePoint s t) 0) ^ 2 := by
    filter_upwards [hnormal, hraw, ae_restrict_mem measurableSet_Ioo] with
      t ht hrawt htMem
    have htIcc : t ∈ Icc (x₀ 1 - r) (x₀ 1 + r) := ⟨htMem.1.le, htMem.2.le⟩
    have hvLpIcc : MemLp (horizontalSliceUniformLimit F t) 2
        (volume.restrict (Icc a b)) := hrawt.valueMemL2.ae_eq ht.aeEq.symm
    have hvLp : MemLp (horizontalSliceUniformLimit F t) 2
        (volume.restrict (Ioo a b)) :=
      hvLpIcc.mono_measure (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)
    have hvRight : k ≤ horizontalSliceUniformLimit F t b := by
      rw [C.horizontalSliceUniformLimit_eq_right]
      exact hright t htIcc
    have hcollar := setIntegral_sq_max_const_sub_le_right_endpoint_collar
      hab hq ht.continuousOn hvLp hrawt.gradientMemL2 ht.hasWeakDeriv hvRight
    have hbq : b - q = δ := by dsimp [q]; ring
    have hae : (fun s => (max (k - horizontalSliceUniformLimit F t s) 0) ^ 2)
        =ᵐ[volume.restrict (Ioo q b)]
        fun s => (max (k - u (squarePoint s t)) 0) ^ 2 := by
      refine (ae_restrict_of_ae_restrict_of_subset ?_ ht.aeEq).mono ?_
      · exact fun s hs => ⟨hq.1.trans hs.1.le, hs.2.le⟩
      · intro s hs
        change horizontalSliceUniformLimit F t s = u (squarePoint s t) at hs
        change (max (k - horizontalSliceUniformLimit F t s) 0) ^ 2 =
          (max (k - u (squarePoint s t)) 0) ^ 2
        rw [hs]
    calc
      (∫ s in Ioo q b, (max (k - u (squarePoint s t)) 0) ^ 2) =
          ∫ s in Icc q b, (max (k - horizontalSliceUniformLimit F t s) 0) ^ 2 := by
        rw [integral_Icc_eq_integral_Ioo]
        exact (integral_congr_ae hae).symm
      _ ≤ δ ^ 2 * ∫ s in Icc q b, |g (squarePoint s t) 0| ^ (2 : ℝ) := by
        rw [← hbq]
        exact hcollar
      _ = δ ^ 2 * ∫ s in Ioo q b, (g (squarePoint s t) 0) ^ 2 := by
        rw [integral_Icc_eq_integral_Ioo]
        congr 2
        funext s
        rw [Real.rpow_two, sq_abs]
  have houter :
      (∫ t in Ioo c d, ∫ s in Ioo q b, (max (k - u (squarePoint s t)) 0) ^ 2) ≤
        ∫ t in Ioo c d, δ ^ 2 * ∫ s in Ioo q b, (g (squarePoint s t) 0) ^ 2 := by
    apply setIntegral_mono_ae_restrict houterTrunc
      (by simpa only [IntegrableOn] using houterGrad.const_mul (δ ^ 2))
    exact hinner
  change (∫ x in Q, (max (k - u x) 0) ^ 2) ≤ δ ^ 2 * ∫ x in Q, (g x 0) ^ 2
  rw [integralOn_axisBox_eq_integral_outerSecond_squarePoint htruncInt,
    integralOn_axisBox_eq_integral_outerSecond_squarePoint hgInt,
    ← MeasureTheory.integral_const_mul]
  exact houter

/-- A lower left trace bound controls the negative part below `k` in the left
collar, with exact coefficient `δ²`. -/
theorem setIntegral_sq_max_const_sub_le_left_collar
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {x₀ : Vec 2} {r δ k : ℝ}
    (C : SquareNormalTraceCertificate F u g x₀ r)
    (hδ : δ ∈ Icc 0 (2 * r))
    (hleft : ∀ t ∈ Icc (x₀ 1 - r) (x₀ 1 + r),
      k ≤ C.traceProvenance.trace.left t) :
    ∫ x in axisBox ![x₀ 0 - r, x₀ 1 - r]
        ![x₀ 0 - r + δ, x₀ 1 + r], (max (k - u x) 0) ^ 2 ∂volume ≤
      δ ^ 2 * ∫ x in axisBox ![x₀ 0 - r, x₀ 1 - r]
        ![x₀ 0 - r + δ, x₀ 1 + r], (g x 0) ^ 2 ∂volume := by
  let a := x₀ 0 - r
  let b := x₀ 0 + r
  let c := x₀ 1 - r
  let d := x₀ 1 + r
  let q := a + δ
  let Q := axisBox ![a, c] ![q, d]
  let Q₀ := axisBox ![a, c] ![b, d]
  have hab : a < b := by dsimp [a, b]; linarith [C.radius_pos]
  have hcd : c < d := by dsimp [c, d]; linarith [C.radius_pos]
  have hq : q ∈ Icc a b := by
    dsimp [q, a, b]
    constructor <;> linarith [hδ.1, hδ.2]
  have hQ : Q ⊆ Q₀ := by
    apply axisBox_mono
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> simp only [q]
      · exact hq.2
      · exact le_rfl
  have huQ : MemL2On Q u := memLpOn_mono hQ C.normalSliceData.valueMemL2
  have hgQ : MemL2On Q (fun x => g x 0) :=
    memLpOn_mono hQ (C.normalSliceData.gradientMemL2 0)
  let : IsFiniteMeasure (volume.restrict Q) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (volume_axisBox_ne_top _ _).lt_top⟩
  have htruncQ : MemL2On Q (fun x => max (k - u x) 0) := by
    have hshift : MemLp (fun x => k - u x) 2 (volume.restrict Q) := by
      simpa only [Pi.sub_apply] using! (memLp_const k).sub huQ
    simpa only using hshift.pos_part
  have htruncInt : IntegrableOn (fun x => (max (k - u x) 0) ^ 2) Q volume := by
    simpa only [IntegrableOn] using htruncQ.integrable_sq
  have hgInt : IntegrableOn (fun x => (g x 0) ^ 2) Q volume := by
    simpa only [IntegrableOn] using hgQ.integrable_sq
  have houterTrunc : IntegrableOn
      (fun t => ∫ s in Ioo a q, (max (k - u (squarePoint s t)) 0) ^ 2)
      (Ioo c d) volume :=
    integrableOn_axisBox_outerSecond_innerIntegral_squarePoint htruncInt
  have houterGrad : IntegrableOn
      (fun t => ∫ s in Ioo a q, (g (squarePoint s t) 0) ^ 2)
      (Ioo c d) volume :=
    integrableOn_axisBox_outerSecond_innerIntegral_squarePoint hgInt
  have hnormal := C.ae_hasHorizontalNormalSliceLimit
  have hraw := ae_horizontalSliceRawL2DataAt C.normalSliceData
  have hinner : ∀ᵐ t ∂(volume.restrict (Ioo c d)),
      (∫ s in Ioo a q, (max (k - u (squarePoint s t)) 0) ^ 2) ≤
        δ ^ 2 * ∫ s in Ioo a q, (g (squarePoint s t) 0) ^ 2 := by
    filter_upwards [hnormal, hraw, ae_restrict_mem measurableSet_Ioo] with
      t ht hrawt htMem
    have htIcc : t ∈ Icc (x₀ 1 - r) (x₀ 1 + r) := ⟨htMem.1.le, htMem.2.le⟩
    have hvLpIcc : MemLp (horizontalSliceUniformLimit F t) 2
        (volume.restrict (Icc a b)) := hrawt.valueMemL2.ae_eq ht.aeEq.symm
    have hvLp : MemLp (horizontalSliceUniformLimit F t) 2
        (volume.restrict (Ioo a b)) :=
      hvLpIcc.mono_measure (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)
    have hvLeft : k ≤ horizontalSliceUniformLimit F t a := by
      rw [C.horizontalSliceUniformLimit_eq_left]
      exact hleft t htIcc
    have hcollar := setIntegral_sq_max_const_sub_le_left_endpoint_collar
      hab hq ht.continuousOn hvLp hrawt.gradientMemL2 ht.hasWeakDeriv hvLeft
    have hqa : q - a = δ := by dsimp [q]; ring
    have hae : (fun s => (max (k - horizontalSliceUniformLimit F t s) 0) ^ 2)
        =ᵐ[volume.restrict (Ioo a q)]
        fun s => (max (k - u (squarePoint s t)) 0) ^ 2 := by
      refine (ae_restrict_of_ae_restrict_of_subset ?_ ht.aeEq).mono ?_
      · exact fun s hs => ⟨hs.1.le, hs.2.le.trans hq.2⟩
      · intro s hs
        change horizontalSliceUniformLimit F t s = u (squarePoint s t) at hs
        change (max (k - horizontalSliceUniformLimit F t s) 0) ^ 2 =
          (max (k - u (squarePoint s t)) 0) ^ 2
        rw [hs]
    calc
      (∫ s in Ioo a q, (max (k - u (squarePoint s t)) 0) ^ 2) =
          ∫ s in Icc a q, (max (k - horizontalSliceUniformLimit F t s) 0) ^ 2 := by
        rw [integral_Icc_eq_integral_Ioo]
        exact (integral_congr_ae hae).symm
      _ ≤ δ ^ 2 * ∫ s in Icc a q, |g (squarePoint s t) 0| ^ (2 : ℝ) := by
        rw [← hqa]
        exact hcollar
      _ = δ ^ 2 * ∫ s in Ioo a q, (g (squarePoint s t) 0) ^ 2 := by
        rw [integral_Icc_eq_integral_Ioo]
        congr 2
        funext s
        rw [Real.rpow_two, sq_abs]
  have houter :
      (∫ t in Ioo c d, ∫ s in Ioo a q, (max (k - u (squarePoint s t)) 0) ^ 2) ≤
        ∫ t in Ioo c d, δ ^ 2 * ∫ s in Ioo a q, (g (squarePoint s t) 0) ^ 2 := by
    apply setIntegral_mono_ae_restrict houterTrunc
      (by simpa only [IntegrableOn] using houterGrad.const_mul (δ ^ 2))
    exact hinner
  change (∫ x in Q, (max (k - u x) 0) ^ 2) ≤ δ ^ 2 * ∫ x in Q, (g x 0) ^ 2
  rw [integralOn_axisBox_eq_integral_outerSecond_squarePoint htruncInt,
    integralOn_axisBox_eq_integral_outerSecond_squarePoint hgInt,
    ← MeasureTheory.integral_const_mul]
  exact houter

end SquareNormalTraceCertificate

private theorem integrableOn_sq_max_const_sub_of_axisBox_subset
    {u : Vec 2 → ℝ} {k : ℝ} {S Q : Set (Vec 2)}
    (hSQ : S ⊆ Q) (hu : MemL2On Q u)
    (hfinite : volume S ≠ ⊤) :
    IntegrableOn (fun x => (max (k - u x) 0) ^ 2) S volume := by
  let : IsFiniteMeasure (volume.restrict S) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hfinite.lt_top⟩
  have huS : MemL2On S u := memLpOn_mono hSQ hu
  have hshift : MemLp (fun x => k - u x) 2 (volume.restrict S) := by
    simpa only [Pi.sub_apply] using! (memLp_const k).sub huS
  have htrunc : MemL2On S (fun x => max (k - u x) 0) := by
    simpa only using hshift.pos_part
  simpa only [IntegrableOn] using htrunc.integrable_sq

/-- Combining the four direct lower side-collar bounds costs no geometric
constant.  This is deliberately proved from the original trace certificate,
not by negating its provenance: the certificate contains exact chosen normal
representatives, for which automatic negation is not available. -/
theorem SquareNormalTraceCertificate.setIntegral_sq_max_const_sub_le_square_collar_lower
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {x₀ : Vec 2} {r δ k : ℝ}
    (C : SquareNormalTraceCertificate F u g x₀ r)
    (hδ : δ ∈ Icc 0 (2 * r))
    (hleft : ∀ t ∈ Icc (x₀ 1 - r) (x₀ 1 + r),
      k ≤ C.traceProvenance.trace.left t)
    (hright : ∀ t ∈ Icc (x₀ 1 - r) (x₀ 1 + r),
      k ≤ C.traceProvenance.trace.right t)
    (hbottom : ∀ s ∈ Icc (x₀ 0 - r) (x₀ 0 + r),
      k ≤ C.traceProvenance.trace.bottom s)
    (htop : ∀ s ∈ Icc (x₀ 0 - r) (x₀ 0 + r),
      k ≤ C.traceProvenance.trace.top s) :
    ∫ x in centeredAxisCube x₀ r \
        axisBoxInteriorInset (x₀ 0 - r) (x₀ 0 + r)
          (x₀ 1 - r) (x₀ 1 + r) δ,
        (max (k - u x) 0) ^ 2 ∂volume ≤
      δ ^ 2 *
        ((∫ x in centeredSquareLeftCollar x₀ r δ, (g x 0) ^ 2 ∂volume) +
          (∫ x in centeredSquareRightCollar x₀ r δ, (g x 0) ^ 2 ∂volume) +
          (∫ x in centeredSquareBottomCollar x₀ r δ, (g x 1) ^ 2 ∂volume) +
          ∫ x in centeredSquareTopCollar x₀ r δ, (g x 1) ^ 2 ∂volume) := by
  let L := centeredSquareLeftCollar x₀ r δ
  let R := centeredSquareRightCollar x₀ r δ
  let B := centeredSquareBottomCollar x₀ r δ
  let T := centeredSquareTopCollar x₀ r δ
  have hL : L ⊆ centeredAxisCube x₀ r := fun x hx =>
    (centeredSquareCollar_subset_centeredAxisCube_diff_axisBoxInteriorInset hδ
      (Or.inl (Or.inl hx))).1
  have hR : R ⊆ centeredAxisCube x₀ r := fun x hx =>
    (centeredSquareCollar_subset_centeredAxisCube_diff_axisBoxInteriorInset hδ
      (Or.inl (Or.inr hx))).1
  have hB : B ⊆ centeredAxisCube x₀ r := fun x hx =>
    (centeredSquareCollar_subset_centeredAxisCube_diff_axisBoxInteriorInset hδ
      (Or.inr (Or.inl hx))).1
  have hT : T ⊆ centeredAxisCube x₀ r := fun x hx =>
    (centeredSquareCollar_subset_centeredAxisCube_diff_axisBoxInteriorInset hδ
      (Or.inr (Or.inr hx))).1
  have hcentered : centeredAxisCube x₀ r =
      axisBox ![x₀ 0 - r, x₀ 1 - r] ![x₀ 0 + r, x₀ 1 + r] := by
    unfold centeredAxisCube
    congr 1 <;> funext i <;> fin_cases i <;> rfl
  have hLBox : L ⊆ axisBox ![x₀ 0 - r, x₀ 1 - r]
      ![x₀ 0 + r, x₀ 1 + r] := by
    simpa only [hcentered] using hL
  have hRBox : R ⊆ axisBox ![x₀ 0 - r, x₀ 1 - r]
      ![x₀ 0 + r, x₀ 1 + r] := by
    simpa only [hcentered] using hR
  have hBBox : B ⊆ axisBox ![x₀ 0 - r, x₀ 1 - r]
      ![x₀ 0 + r, x₀ 1 + r] := by
    simpa only [hcentered] using hB
  have hTBox : T ⊆ axisBox ![x₀ 0 - r, x₀ 1 - r]
      ![x₀ 0 + r, x₀ 1 + r] := by
    simpa only [hcentered] using hT
  have hLInt : IntegrableOn (fun x => (max (k - u x) 0) ^ 2) L volume := by
    apply integrableOn_sq_max_const_sub_of_axisBox_subset hLBox
      C.normalSliceData.valueMemL2
    exact volume_axisBox_ne_top _ _
  have hRInt : IntegrableOn (fun x => (max (k - u x) 0) ^ 2) R volume := by
    apply integrableOn_sq_max_const_sub_of_axisBox_subset hRBox
      C.normalSliceData.valueMemL2
    exact volume_axisBox_ne_top _ _
  have hBInt : IntegrableOn (fun x => (max (k - u x) 0) ^ 2) B volume := by
    apply integrableOn_sq_max_const_sub_of_axisBox_subset hBBox
      C.normalSliceData.valueMemL2
    exact volume_axisBox_ne_top _ _
  have hTInt : IntegrableOn (fun x => (max (k - u x) 0) ^ 2) T volume := by
    apply integrableOn_sq_max_const_sub_of_axisBox_subset hTBox
      C.normalSliceData.valueMemL2
    exact volume_axisBox_ne_top _ _
  have hcover : centeredAxisCube x₀ r \
      axisBoxInteriorInset (x₀ 0 - r) (x₀ 0 + r)
        (x₀ 1 - r) (x₀ 1 + r) δ ⊆ (L ∪ R) ∪ (B ∪ T) :=
    centeredAxisCube_diff_axisBoxInteriorInset_subset_centeredSquareCollar x₀ r δ
  have hleft' := C.setIntegral_sq_max_const_sub_le_left_collar hδ hleft
  have hright' := C.setIntegral_sq_max_const_sub_le_right_collar hδ hright
  have hbottom' := C.setIntegral_sq_max_const_sub_le_bottom_collar hδ hbottom
  have htop' := C.setIntegral_sq_max_const_sub_le_top_collar hδ htop
  have hleftL : (∫ x in L, (max (k - u x) 0) ^ 2 ∂volume) ≤
      δ ^ 2 * ∫ x in L, (g x 0) ^ 2 ∂volume := by
    simpa only [L, centeredSquareLeftCollar] using hleft'
  have hrightR : (∫ x in R, (max (k - u x) 0) ^ 2 ∂volume) ≤
      δ ^ 2 * ∫ x in R, (g x 0) ^ 2 ∂volume := by
    simpa only [R, centeredSquareRightCollar] using hright'
  have hbottomB : (∫ x in B, (max (k - u x) 0) ^ 2 ∂volume) ≤
      δ ^ 2 * ∫ x in B, (g x 1) ^ 2 ∂volume := by
    simpa only [B, centeredSquareBottomCollar] using hbottom'
  have htopT : (∫ x in T, (max (k - u x) 0) ^ 2 ∂volume) ≤
      δ ^ 2 * ∫ x in T, (g x 1) ^ 2 ∂volume := by
    simpa only [T, centeredSquareTopCollar] using htop'
  calc
    ∫ x in centeredAxisCube x₀ r \
        axisBoxInteriorInset (x₀ 0 - r) (x₀ 0 + r)
          (x₀ 1 - r) (x₀ 1 + r) δ,
        (max (k - u x) 0) ^ 2 ∂volume ≤
        (∫ x in L, (max (k - u x) 0) ^ 2 ∂volume) +
          (∫ x in R, (max (k - u x) 0) ^ 2 ∂volume) +
          (∫ x in B, (max (k - u x) 0) ^ 2 ∂volume) +
          ∫ x in T, (max (k - u x) 0) ^ 2 ∂volume :=
      setIntegral_le_sum_four_of_subset_union hcover hLInt hRInt hBInt hTInt
        (fun x => sq_nonneg _)
    _ ≤ δ ^ 2 * (∫ x in L, (g x 0) ^ 2 ∂volume) +
          δ ^ 2 * (∫ x in R, (g x 0) ^ 2 ∂volume) +
          δ ^ 2 * (∫ x in B, (g x 1) ^ 2 ∂volume) +
          δ ^ 2 * ∫ x in T, (g x 1) ^ 2 ∂volume := by
      gcongr
    _ = δ ^ 2 *
        ((∫ x in L, (g x 0) ^ 2 ∂volume) +
          (∫ x in R, (g x 0) ^ 2 ∂volume) +
          (∫ x in B, (g x 1) ^ 2 ∂volume) +
          ∫ x in T, (g x 1) ^ 2 ∂volume) := by ring

end

end PDE
