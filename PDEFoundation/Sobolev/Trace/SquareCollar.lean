module

public import PDEFoundation.Measure.AxisBoxVolume
public import PDEFoundation.Sobolev.OneDimensional.EndpointCollar
public import PDEFoundation.Sobolev.Trace.SquareNormalTrace

/-!
# Collar estimates from certified square normal traces

The four-side trace alone is not enough to control a two-dimensional collar:
its values live on a set of planar measure zero.  This module uses
`SquareNormalTraceCertificate`, which retains the common smooth approximation
and hence supplies both almost-everywhere normal weak representatives and
their pointwise endpoint identifications with the traces.

The estimates below have constant one and the exact square of the collar
width.  They are intentionally stated for the raw representative `u`; the
Fubini argument transfers the one-dimensional canonical representatives back
to it almost everywhere in the collar.
-/

@[expose] public section

namespace PDE

open Filter MeasureTheory Set

noncomputable section

namespace SquareNormalTraceCertificate

/-- A top trace bounded above by `k` controls the positive part of the
certified representative in its top collar.  The normal derivative is the
second native coordinate, and the coefficient is exactly `δ²`. -/
theorem setIntegral_sq_max_sub_const_le_top_collar
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {x₀ : Vec 2} {r δ k : ℝ}
    (C : SquareNormalTraceCertificate F u g x₀ r)
    (hδ : δ ∈ Icc 0 (2 * r))
    (htop : ∀ s ∈ Icc (x₀ 0 - r) (x₀ 0 + r),
      C.traceProvenance.trace.top s ≤ k) :
    ∫ x in axisBox ![x₀ 0 - r, x₀ 1 + r - δ]
        ![x₀ 0 + r, x₀ 1 + r], (max (u x - k) 0) ^ 2 ∂volume ≤
      δ ^ 2 * ∫ x in axisBox ![x₀ 0 - r, x₀ 1 + r - δ]
        ![x₀ 0 + r, x₀ 1 + r], (g x 1) ^ 2 ∂volume := by
  let a := x₀ 0 - r
  let b := x₀ 0 + r
  let c := x₀ 1 - r
  let d := x₀ 1 + r
  let q := d - δ
  let Q := axisBox ![a, q] ![b, d]
  let Q₀ := axisBox ![a, c] ![b, d]
  have hab : a < b := by
    dsimp [a, b]
    linarith [C.radius_pos]
  have hcd : c < d := by
    dsimp [c, d]
    linarith [C.radius_pos]
  have hq : q ∈ Icc c d := by
    dsimp [q, c, d]
    constructor <;> linarith [hδ.1, hδ.2]
  have hQ : Q ⊆ Q₀ := by
    apply axisBox_mono
    · intro i
      fin_cases i <;> simp only [a, q]
      · exact le_rfl
      · exact hq.1
    · intro i
      fin_cases i <;> rfl
  have huQ : MemL2On Q u :=
    memLpOn_mono hQ C.normalSliceData.valueMemL2
  have hgQ : MemL2On Q (fun x => g x 1) :=
    memLpOn_mono hQ (C.normalSliceData.gradientMemL2 1)
  let : IsFiniteMeasure (volume.restrict Q) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact (volume_axisBox_ne_top _ _).lt_top⟩
  have htruncQ : MemL2On Q (fun x => max (u x - k) 0) := by
    have hshift : MemLp (fun x => u x - k) 2 (volume.restrict Q) := by
      simpa only [Pi.sub_apply] using! huQ.sub (memLp_const k)
    simpa only using hshift.pos_part
  have htruncInt : IntegrableOn (fun x => (max (u x - k) 0) ^ 2) Q volume := by
    simpa only [IntegrableOn] using htruncQ.integrable_sq
  have hgInt : IntegrableOn (fun x => (g x 1) ^ 2) Q volume := by
    simpa only [IntegrableOn] using hgQ.integrable_sq
  have houterTrunc : IntegrableOn
      (fun s => ∫ t in Ioo q d, (max (u (squarePoint s t) - k) 0) ^ 2)
      (Ioo a b) volume :=
    integrableOn_axisBox_innerIntegral_squarePoint htruncInt
  have houterGrad : IntegrableOn
      (fun s => ∫ t in Ioo q d, (g (squarePoint s t) 1) ^ 2)
      (Ioo a b) volume :=
    integrableOn_axisBox_innerIntegral_squarePoint hgInt
  have hnormal := C.ae_hasVerticalNormalSliceLimit
  have hraw := ae_verticalSliceRawL2DataAt C.normalSliceData
  have hinner : ∀ᵐ s ∂(volume.restrict (Ioo a b)),
      (∫ t in Ioo q d, (max (u (squarePoint s t) - k) 0) ^ 2) ≤
        δ ^ 2 * ∫ t in Ioo q d, (g (squarePoint s t) 1) ^ 2 := by
    filter_upwards [hnormal, hraw, ae_restrict_mem measurableSet_Ioo] with
      s hs hraws hs_mem
    have hsIcc : s ∈ Icc (x₀ 0 - r) (x₀ 0 + r) :=
      ⟨hs_mem.1.le, hs_mem.2.le⟩
    have hvLpIcc : MemLp (verticalSliceUniformLimit F s) 2
        (volume.restrict (Icc c d)) :=
      hraws.valueMemL2.ae_eq hs.aeEq.symm
    have hvLp : MemLp (verticalSliceUniformLimit F s) 2
        (volume.restrict (Ioo c d)) :=
      hvLpIcc.mono_measure (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)
    have hvTop : verticalSliceUniformLimit F s d ≤ k := by
      rw [C.verticalSliceUniformLimit_eq_top]
      exact htop s hsIcc
    have hcollar := setIntegral_sq_max_sub_const_le_right_endpoint_collar
      hcd hq hs.continuousOn hvLp hraws.gradientMemL2 hs.hasWeakDeriv hvTop
    have hdq : d - q = δ := by
      dsimp [q]
      ring
    have hae : (fun t => (max (verticalSliceUniformLimit F s t - k) 0) ^ 2)
        =ᵐ[volume.restrict (Ioo q d)]
        fun t => (max (u (squarePoint s t) - k) 0) ^ 2 := by
      refine (ae_restrict_of_ae_restrict_of_subset ?_ hs.aeEq).mono ?_
      · exact fun t ht => ⟨hq.1.trans ht.1.le, ht.2.le⟩
      · intro t ht
        change verticalSliceUniformLimit F s t = u (squarePoint s t) at ht
        change (max (verticalSliceUniformLimit F s t - k) 0) ^ 2 =
          (max (u (squarePoint s t) - k) 0) ^ 2
        rw [ht]
    calc
      (∫ t in Ioo q d, (max (u (squarePoint s t) - k) 0) ^ 2) =
          ∫ t in Icc q d,
            (max (verticalSliceUniformLimit F s t - k) 0) ^ 2 := by
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
      (∫ s in Ioo a b,
        ∫ t in Ioo q d, (max (u (squarePoint s t) - k) 0) ^ 2) ≤
        ∫ s in Ioo a b,
          δ ^ 2 * ∫ t in Ioo q d, (g (squarePoint s t) 1) ^ 2 := by
    apply setIntegral_mono_ae_restrict houterTrunc
      (by simpa only [IntegrableOn] using houterGrad.const_mul (δ ^ 2))
    exact hinner
  change (∫ x in Q, (max (u x - k) 0) ^ 2) ≤
    δ ^ 2 * ∫ x in Q, (g x 1) ^ 2
  rw [integralOn_axisBox_eq_integral_squarePoint htruncInt,
    integralOn_axisBox_eq_integral_squarePoint hgInt,
    ← MeasureTheory.integral_const_mul]
  exact houter

/-- A left trace bounded above by `k` controls the positive part of the
certified representative in its left collar.  The normal derivative is the
first native coordinate, and the coefficient is exactly `δ²`. -/
theorem setIntegral_sq_max_sub_const_le_left_collar
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {x₀ : Vec 2} {r δ k : ℝ}
    (C : SquareNormalTraceCertificate F u g x₀ r)
    (hδ : δ ∈ Icc 0 (2 * r))
    (hleft : ∀ t ∈ Icc (x₀ 1 - r) (x₀ 1 + r),
      C.traceProvenance.trace.left t ≤ k) :
    ∫ x in axisBox ![x₀ 0 - r, x₀ 1 - r]
        ![x₀ 0 - r + δ, x₀ 1 + r], (max (u x - k) 0) ^ 2 ∂volume ≤
      δ ^ 2 * ∫ x in axisBox ![x₀ 0 - r, x₀ 1 - r]
        ![x₀ 0 - r + δ, x₀ 1 + r], (g x 0) ^ 2 ∂volume := by
  let a := x₀ 0 - r
  let b := x₀ 0 + r
  let c := x₀ 1 - r
  let d := x₀ 1 + r
  let q := a + δ
  let Q := axisBox ![a, c] ![q, d]
  let Q₀ := axisBox ![a, c] ![b, d]
  have hab : a < b := by
    dsimp [a, b]
    linarith [C.radius_pos]
  have hcd : c < d := by
    dsimp [c, d]
    linarith [C.radius_pos]
  have hq : q ∈ Icc a b := by
    dsimp [q, a, b]
    constructor <;> linarith [hδ.1, hδ.2]
  have hQ : Q ⊆ Q₀ := by
    apply axisBox_mono
    · intro i
      fin_cases i <;> rfl
    · intro i
      fin_cases i <;> simp only [q]
      · exact hq.2
      · exact le_rfl
  have huQ : MemL2On Q u :=
    memLpOn_mono hQ C.normalSliceData.valueMemL2
  have hgQ : MemL2On Q (fun x => g x 0) :=
    memLpOn_mono hQ (C.normalSliceData.gradientMemL2 0)
  let : IsFiniteMeasure (volume.restrict Q) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact (volume_axisBox_ne_top _ _).lt_top⟩
  have htruncQ : MemL2On Q (fun x => max (u x - k) 0) := by
    have hshift : MemLp (fun x => u x - k) 2 (volume.restrict Q) := by
      simpa only [Pi.sub_apply] using! huQ.sub (memLp_const k)
    simpa only using hshift.pos_part
  have htruncInt : IntegrableOn (fun x => (max (u x - k) 0) ^ 2) Q volume := by
    simpa only [IntegrableOn] using htruncQ.integrable_sq
  have hgInt : IntegrableOn (fun x => (g x 0) ^ 2) Q volume := by
    simpa only [IntegrableOn] using hgQ.integrable_sq
  have houterTrunc : IntegrableOn
      (fun t => ∫ s in Ioo a q, (max (u (squarePoint s t) - k) 0) ^ 2)
      (Ioo c d) volume :=
    integrableOn_axisBox_outerSecond_innerIntegral_squarePoint htruncInt
  have houterGrad : IntegrableOn
      (fun t => ∫ s in Ioo a q, (g (squarePoint s t) 0) ^ 2)
      (Ioo c d) volume :=
    integrableOn_axisBox_outerSecond_innerIntegral_squarePoint hgInt
  have hnormal := C.ae_hasHorizontalNormalSliceLimit
  have hraw := ae_horizontalSliceRawL2DataAt C.normalSliceData
  have hinner : ∀ᵐ t ∂(volume.restrict (Ioo c d)),
      (∫ s in Ioo a q, (max (u (squarePoint s t) - k) 0) ^ 2) ≤
        δ ^ 2 * ∫ s in Ioo a q, (g (squarePoint s t) 0) ^ 2 := by
    filter_upwards [hnormal, hraw, ae_restrict_mem measurableSet_Ioo] with
      t ht hrawt ht_mem
    have htIcc : t ∈ Icc (x₀ 1 - r) (x₀ 1 + r) :=
      ⟨ht_mem.1.le, ht_mem.2.le⟩
    have hvLpIcc : MemLp (horizontalSliceUniformLimit F t) 2
        (volume.restrict (Icc a b)) :=
      hrawt.valueMemL2.ae_eq ht.aeEq.symm
    have hvLp : MemLp (horizontalSliceUniformLimit F t) 2
        (volume.restrict (Ioo a b)) :=
      hvLpIcc.mono_measure (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)
    have hvLeft : horizontalSliceUniformLimit F t a ≤ k := by
      rw [C.horizontalSliceUniformLimit_eq_left]
      exact hleft t htIcc
    have hcollar := setIntegral_sq_max_sub_const_le_left_endpoint_collar
      hab hq ht.continuousOn hvLp hrawt.gradientMemL2 ht.hasWeakDeriv hvLeft
    have hqa : q - a = δ := by
      dsimp [q]
      ring
    have hae : (fun s => (max (horizontalSliceUniformLimit F t s - k) 0) ^ 2)
        =ᵐ[volume.restrict (Ioo a q)]
        fun s => (max (u (squarePoint s t) - k) 0) ^ 2 := by
      refine (ae_restrict_of_ae_restrict_of_subset ?_ ht.aeEq).mono ?_
      · exact fun s hs => ⟨hs.1.le, hs.2.le.trans hq.2⟩
      · intro s hs
        change horizontalSliceUniformLimit F t s = u (squarePoint s t) at hs
        change (max (horizontalSliceUniformLimit F t s - k) 0) ^ 2 =
          (max (u (squarePoint s t) - k) 0) ^ 2
        rw [hs]
    calc
      (∫ s in Ioo a q, (max (u (squarePoint s t) - k) 0) ^ 2) =
          ∫ s in Icc a q,
            (max (horizontalSliceUniformLimit F t s - k) 0) ^ 2 := by
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
      (∫ t in Ioo c d,
        ∫ s in Ioo a q, (max (u (squarePoint s t) - k) 0) ^ 2) ≤
        ∫ t in Ioo c d,
          δ ^ 2 * ∫ s in Ioo a q, (g (squarePoint s t) 0) ^ 2 := by
    apply setIntegral_mono_ae_restrict houterTrunc
      (by simpa only [IntegrableOn] using houterGrad.const_mul (δ ^ 2))
    exact hinner
  change (∫ x in Q, (max (u x - k) 0) ^ 2) ≤
    δ ^ 2 * ∫ x in Q, (g x 0) ^ 2
  rw [integralOn_axisBox_eq_integral_outerSecond_squarePoint htruncInt,
    integralOn_axisBox_eq_integral_outerSecond_squarePoint hgInt,
    ← MeasureTheory.integral_const_mul]
  exact houter

/-- A right trace bounded above by `k` controls the positive part of the
certified representative in its right collar.  The normal derivative is the
first native coordinate, and the coefficient is exactly `δ²`. -/
theorem setIntegral_sq_max_sub_const_le_right_collar
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {x₀ : Vec 2} {r δ k : ℝ}
    (C : SquareNormalTraceCertificate F u g x₀ r)
    (hδ : δ ∈ Icc 0 (2 * r))
    (hright : ∀ t ∈ Icc (x₀ 1 - r) (x₀ 1 + r),
      C.traceProvenance.trace.right t ≤ k) :
    ∫ x in axisBox ![x₀ 0 + r - δ, x₀ 1 - r]
        ![x₀ 0 + r, x₀ 1 + r], (max (u x - k) 0) ^ 2 ∂volume ≤
      δ ^ 2 * ∫ x in axisBox ![x₀ 0 + r - δ, x₀ 1 - r]
        ![x₀ 0 + r, x₀ 1 + r], (g x 0) ^ 2 ∂volume := by
  let a := x₀ 0 - r
  let b := x₀ 0 + r
  let c := x₀ 1 - r
  let d := x₀ 1 + r
  let q := b - δ
  let Q := axisBox ![q, c] ![b, d]
  let Q₀ := axisBox ![a, c] ![b, d]
  have hab : a < b := by
    dsimp [a, b]
    linarith [C.radius_pos]
  have hcd : c < d := by
    dsimp [c, d]
    linarith [C.radius_pos]
  have hq : q ∈ Icc a b := by
    dsimp [q, a, b]
    constructor <;> linarith [hδ.1, hδ.2]
  have hQ : Q ⊆ Q₀ := by
    apply axisBox_mono
    · intro i
      fin_cases i <;> simp only [a, c, q]
      · exact hq.1
      · exact le_rfl
    · intro i
      fin_cases i <;> rfl
  have huQ : MemL2On Q u :=
    memLpOn_mono hQ C.normalSliceData.valueMemL2
  have hgQ : MemL2On Q (fun x => g x 0) :=
    memLpOn_mono hQ (C.normalSliceData.gradientMemL2 0)
  let : IsFiniteMeasure (volume.restrict Q) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact (volume_axisBox_ne_top _ _).lt_top⟩
  have htruncQ : MemL2On Q (fun x => max (u x - k) 0) := by
    have hshift : MemLp (fun x => u x - k) 2 (volume.restrict Q) := by
      simpa only [Pi.sub_apply] using! huQ.sub (memLp_const k)
    simpa only using hshift.pos_part
  have htruncInt : IntegrableOn (fun x => (max (u x - k) 0) ^ 2) Q volume := by
    simpa only [IntegrableOn] using htruncQ.integrable_sq
  have hgInt : IntegrableOn (fun x => (g x 0) ^ 2) Q volume := by
    simpa only [IntegrableOn] using hgQ.integrable_sq
  have houterTrunc : IntegrableOn
      (fun t => ∫ s in Ioo q b, (max (u (squarePoint s t) - k) 0) ^ 2)
      (Ioo c d) volume :=
    integrableOn_axisBox_outerSecond_innerIntegral_squarePoint htruncInt
  have houterGrad : IntegrableOn
      (fun t => ∫ s in Ioo q b, (g (squarePoint s t) 0) ^ 2)
      (Ioo c d) volume :=
    integrableOn_axisBox_outerSecond_innerIntegral_squarePoint hgInt
  have hnormal := C.ae_hasHorizontalNormalSliceLimit
  have hraw := ae_horizontalSliceRawL2DataAt C.normalSliceData
  have hinner : ∀ᵐ t ∂(volume.restrict (Ioo c d)),
      (∫ s in Ioo q b, (max (u (squarePoint s t) - k) 0) ^ 2) ≤
        δ ^ 2 * ∫ s in Ioo q b, (g (squarePoint s t) 0) ^ 2 := by
    filter_upwards [hnormal, hraw, ae_restrict_mem measurableSet_Ioo] with
      t ht hrawt ht_mem
    have htIcc : t ∈ Icc (x₀ 1 - r) (x₀ 1 + r) :=
      ⟨ht_mem.1.le, ht_mem.2.le⟩
    have hvLpIcc : MemLp (horizontalSliceUniformLimit F t) 2
        (volume.restrict (Icc a b)) :=
      hrawt.valueMemL2.ae_eq ht.aeEq.symm
    have hvLp : MemLp (horizontalSliceUniformLimit F t) 2
        (volume.restrict (Ioo a b)) :=
      hvLpIcc.mono_measure (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)
    have hvRight : horizontalSliceUniformLimit F t b ≤ k := by
      rw [C.horizontalSliceUniformLimit_eq_right]
      exact hright t htIcc
    have hcollar := setIntegral_sq_max_sub_const_le_right_endpoint_collar
      hab hq ht.continuousOn hvLp hrawt.gradientMemL2 ht.hasWeakDeriv hvRight
    have hbq : b - q = δ := by
      dsimp [q]
      ring
    have hae : (fun s => (max (horizontalSliceUniformLimit F t s - k) 0) ^ 2)
        =ᵐ[volume.restrict (Ioo q b)]
        fun s => (max (u (squarePoint s t) - k) 0) ^ 2 := by
      refine (ae_restrict_of_ae_restrict_of_subset ?_ ht.aeEq).mono ?_
      · exact fun s hs => ⟨hq.1.trans hs.1.le, hs.2.le⟩
      · intro s hs
        change horizontalSliceUniformLimit F t s = u (squarePoint s t) at hs
        change (max (horizontalSliceUniformLimit F t s - k) 0) ^ 2 =
          (max (u (squarePoint s t) - k) 0) ^ 2
        rw [hs]
    calc
      (∫ s in Ioo q b, (max (u (squarePoint s t) - k) 0) ^ 2) =
          ∫ s in Icc q b,
            (max (horizontalSliceUniformLimit F t s - k) 0) ^ 2 := by
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
      (∫ t in Ioo c d,
        ∫ s in Ioo q b, (max (u (squarePoint s t) - k) 0) ^ 2) ≤
        ∫ t in Ioo c d,
          δ ^ 2 * ∫ s in Ioo q b, (g (squarePoint s t) 0) ^ 2 := by
    apply setIntegral_mono_ae_restrict houterTrunc
      (by simpa only [IntegrableOn] using houterGrad.const_mul (δ ^ 2))
    exact hinner
  change (∫ x in Q, (max (u x - k) 0) ^ 2) ≤
    δ ^ 2 * ∫ x in Q, (g x 0) ^ 2
  rw [integralOn_axisBox_eq_integral_outerSecond_squarePoint htruncInt,
    integralOn_axisBox_eq_integral_outerSecond_squarePoint hgInt,
    ← MeasureTheory.integral_const_mul]
  exact houter

/-- A bottom trace bounded above by `k` controls the positive part of the
certified representative in its bottom collar.  The normal derivative is the
second native coordinate, and the coefficient is exactly `δ²`. -/
theorem setIntegral_sq_max_sub_const_le_bottom_collar
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {x₀ : Vec 2} {r δ k : ℝ}
    (C : SquareNormalTraceCertificate F u g x₀ r)
    (hδ : δ ∈ Icc 0 (2 * r))
    (hbottom : ∀ s ∈ Icc (x₀ 0 - r) (x₀ 0 + r),
      C.traceProvenance.trace.bottom s ≤ k) :
    ∫ x in axisBox ![x₀ 0 - r, x₀ 1 - r]
        ![x₀ 0 + r, x₀ 1 - r + δ], (max (u x - k) 0) ^ 2 ∂volume ≤
      δ ^ 2 * ∫ x in axisBox ![x₀ 0 - r, x₀ 1 - r]
        ![x₀ 0 + r, x₀ 1 - r + δ], (g x 1) ^ 2 ∂volume := by
  let a := x₀ 0 - r
  let b := x₀ 0 + r
  let c := x₀ 1 - r
  let d := x₀ 1 + r
  let q := c + δ
  let Q := axisBox ![a, c] ![b, q]
  let Q₀ := axisBox ![a, c] ![b, d]
  have hab : a < b := by
    dsimp [a, b]
    linarith [C.radius_pos]
  have hcd : c < d := by
    dsimp [c, d]
    linarith [C.radius_pos]
  have hq : q ∈ Icc c d := by
    dsimp [q, c, d]
    constructor <;> linarith [hδ.1, hδ.2]
  have hQ : Q ⊆ Q₀ := by
    apply axisBox_mono
    · intro i
      fin_cases i <;> rfl
    · intro i
      fin_cases i <;> simp only [q]
      · exact le_rfl
      · exact hq.2
  have huQ : MemL2On Q u :=
    memLpOn_mono hQ C.normalSliceData.valueMemL2
  have hgQ : MemL2On Q (fun x => g x 1) :=
    memLpOn_mono hQ (C.normalSliceData.gradientMemL2 1)
  let : IsFiniteMeasure (volume.restrict Q) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact (volume_axisBox_ne_top _ _).lt_top⟩
  have htruncQ : MemL2On Q (fun x => max (u x - k) 0) := by
    have hshift : MemLp (fun x => u x - k) 2 (volume.restrict Q) := by
      simpa only [Pi.sub_apply] using! huQ.sub (memLp_const k)
    simpa only using hshift.pos_part
  have htruncInt : IntegrableOn (fun x => (max (u x - k) 0) ^ 2) Q volume := by
    simpa only [IntegrableOn] using htruncQ.integrable_sq
  have hgInt : IntegrableOn (fun x => (g x 1) ^ 2) Q volume := by
    simpa only [IntegrableOn] using hgQ.integrable_sq
  have houterTrunc : IntegrableOn
      (fun s => ∫ t in Ioo c q, (max (u (squarePoint s t) - k) 0) ^ 2)
      (Ioo a b) volume :=
    integrableOn_axisBox_innerIntegral_squarePoint htruncInt
  have houterGrad : IntegrableOn
      (fun s => ∫ t in Ioo c q, (g (squarePoint s t) 1) ^ 2)
      (Ioo a b) volume :=
    integrableOn_axisBox_innerIntegral_squarePoint hgInt
  have hnormal := C.ae_hasVerticalNormalSliceLimit
  have hraw := ae_verticalSliceRawL2DataAt C.normalSliceData
  have hinner : ∀ᵐ s ∂(volume.restrict (Ioo a b)),
      (∫ t in Ioo c q, (max (u (squarePoint s t) - k) 0) ^ 2) ≤
        δ ^ 2 * ∫ t in Ioo c q, (g (squarePoint s t) 1) ^ 2 := by
    filter_upwards [hnormal, hraw, ae_restrict_mem measurableSet_Ioo] with
      s hs hraws hs_mem
    have hsIcc : s ∈ Icc (x₀ 0 - r) (x₀ 0 + r) :=
      ⟨hs_mem.1.le, hs_mem.2.le⟩
    have hvLpIcc : MemLp (verticalSliceUniformLimit F s) 2
        (volume.restrict (Icc c d)) :=
      hraws.valueMemL2.ae_eq hs.aeEq.symm
    have hvLp : MemLp (verticalSliceUniformLimit F s) 2
        (volume.restrict (Ioo c d)) :=
      hvLpIcc.mono_measure (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)
    have hvBottom : verticalSliceUniformLimit F s c ≤ k := by
      rw [C.verticalSliceUniformLimit_eq_bottom]
      exact hbottom s hsIcc
    have hcollar := setIntegral_sq_max_sub_const_le_left_endpoint_collar
      hcd hq hs.continuousOn hvLp hraws.gradientMemL2 hs.hasWeakDeriv hvBottom
    have hqc : q - c = δ := by
      dsimp [q]
      ring
    have hae : (fun t => (max (verticalSliceUniformLimit F s t - k) 0) ^ 2)
        =ᵐ[volume.restrict (Ioo c q)]
        fun t => (max (u (squarePoint s t) - k) 0) ^ 2 := by
      refine (ae_restrict_of_ae_restrict_of_subset ?_ hs.aeEq).mono ?_
      · exact fun t ht => ⟨ht.1.le, ht.2.le.trans hq.2⟩
      · intro t ht
        change verticalSliceUniformLimit F s t = u (squarePoint s t) at ht
        change (max (verticalSliceUniformLimit F s t - k) 0) ^ 2 =
          (max (u (squarePoint s t) - k) 0) ^ 2
        rw [ht]
    calc
      (∫ t in Ioo c q, (max (u (squarePoint s t) - k) 0) ^ 2) =
          ∫ t in Icc c q,
            (max (verticalSliceUniformLimit F s t - k) 0) ^ 2 := by
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
      (∫ s in Ioo a b,
        ∫ t in Ioo c q, (max (u (squarePoint s t) - k) 0) ^ 2) ≤
        ∫ s in Ioo a b,
          δ ^ 2 * ∫ t in Ioo c q, (g (squarePoint s t) 1) ^ 2 := by
    apply setIntegral_mono_ae_restrict houterTrunc
      (by simpa only [IntegrableOn] using houterGrad.const_mul (δ ^ 2))
    exact hinner
  change (∫ x in Q, (max (u x - k) 0) ^ 2) ≤
    δ ^ 2 * ∫ x in Q, (g x 1) ^ 2
  rw [integralOn_axisBox_eq_integral_squarePoint htruncInt,
    integralOn_axisBox_eq_integral_squarePoint hgInt,
    ← MeasureTheory.integral_const_mul]
  exact houter

end SquareNormalTraceCertificate

end

end PDE
