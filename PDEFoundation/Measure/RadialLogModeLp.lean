module

public import PDEFoundation.Analysis.RadialModeSmooth
public import PDEFoundation.Measure.EuclideanRadialLogMoment
public import PDEFoundation.Ambient.HilbertVec
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! # Finite exponent integrability of logarithmic radial modes -/

@[expose] public section

namespace PDE

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Literal gradient field of the coordinate logarithmic radial mode. -/
def radialLogGradientField {d : ℕ} (k : Fin d) (x : Vec d) : Vec d :=
  fun i => basisVec k i * Real.log (vecEuclideanNorm x) +
    x k * x i / vecNormSq x

private theorem measurable_log_vecEuclideanNorm {d : ℕ} :
    Measurable (fun x : Vec d => Real.log (vecEuclideanNorm x)) := by
  apply measurable_of_continuousOn_compl_singleton 0
  intro x hx
  have hx0 : x ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hx
  exact (continuous_vecEuclideanNorm.continuousAt.log
    (vecEuclideanNorm_pos_iff.mpr hx0).ne').continuousWithinAt

private theorem measurable_radialLogGradientField_apply {d : ℕ}
    (k i : Fin d) : Measurable (fun x => radialLogGradientField k x i) := by
  apply measurable_of_continuousOn_compl_singleton 0
  intro x hx
  have hx0 : x ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hx
  have hq : vecNormSq x ≠ 0 := fun h => hx0 (vecNormSq_eq_zero h)
  apply ContinuousAt.continuousWithinAt
  have hlog : ContinuousAt (fun y : Vec d => Real.log (vecEuclideanNorm y)) x :=
    continuous_vecEuclideanNorm.continuousAt.log
      (vecEuclideanNorm_pos_iff.mpr hx0).ne'
  have hdiv : ContinuousAt (fun y : Vec d => y k * y i / vecNormSq y) x := by
    apply ContinuousAt.div (by fun_prop) continuous_vecNormSq.continuousAt hq
  exact (continuousAt_const.mul hlog).add hdiv

private theorem abs_radial_ratio_le_one {d : ℕ} (k i : Fin d) (x : Vec d) :
    |x k * x i / vecNormSq x| ≤ 1 := by
  by_cases hx : x = 0
  · subst x
    simp
  · have hq : 0 < vecNormSq x :=
      lt_of_le_of_ne (vecNormSq_nonneg x)
        (Ne.symm (fun h => hx (vecNormSq_eq_zero h)))
    rw [abs_div, abs_of_pos hq, abs_mul]
    apply (div_le_one hq).2
    have hk := abs_apply_le_vecEuclideanNorm x k
    have hi := abs_apply_le_vecEuclideanNorm x i
    rw [← vecEuclideanNorm_sq]
    calc
      |x k| * |x i| ≤ vecEuclideanNorm x * vecEuclideanNorm x :=
        mul_le_mul hk hi (abs_nonneg _) (vecEuclideanNorm_nonneg _)
      _ = vecEuclideanNorm x ^ 2 := by ring

private theorem memLp_vecEuclideanNorm_of_coordinate
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {d : ℕ} {q : ℝ≥0∞} {g : α → Vec d}
    (hg : ∀ i, MemLp (fun x => g x i) q μ) :
    MemLp (fun x => vecEuclideanNorm (g x)) q μ := by
  have hHilbert : MemLp (fun x => (g x).toHilbertVec) q μ := by
    rw [memLp_piLp_iff]
    exact hg
  exact hHilbert.norm.ae_eq (Filter.Eventually.of_forall fun x =>
    Vec.vecEuclideanNorm_eq_norm_toHilbertVec (g x) |>.symm)

/-- The scalar logarithm of the Euclidean radius has every positive finite
real `Lᵖ` exponent on the native unit ball. -/
theorem memLp_log_vecEuclideanNorm_unitBall
    {d : ℕ} (hd : 0 < d) {p : ℝ} (hp : 0 < p) :
    MemLp (fun x : Vec d => Real.log (vecEuclideanNorm x))
      (ENNReal.ofReal p) (volume.restrict (euclideanBall 0 1)) := by
  let μ := volume.restrict (euclideanBall (0 : Vec d) 1)
  have hAES : AEStronglyMeasurable (fun x : Vec d => Real.log (vecEuclideanNorm x)) μ :=
    measurable_log_vecEuclideanNorm.aestronglyMeasurable
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le_of_gt hp
  have hpTop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  rw [← integrable_norm_rpow_iff hAES hp0 hpTop]
  rw [ENNReal.toReal_ofReal hp.le]
  apply (integrableOn_neg_log_vecEuclideanNorm_div_euclideanBall hd
    (by norm_num) hp).congr
  filter_upwards [self_mem_ae_restrict (measurableSet_euclideanBall 0 1)] with x hx
  by_cases hx0 : x = 0
  · subst x
    norm_num [vecEuclideanNorm, vecNormSq, vecDot]
  · have hn : 0 < vecEuclideanNorm x := vecEuclideanNorm_pos_iff.mpr hx0
    have hn1 : vecEuclideanNorm x < 1 := by
      simpa only [mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num : (0 : ℝ) < 1),
        sub_zero] using hx
    simp only [div_one]
    rw [Real.norm_eq_abs, abs_of_nonpos (Real.log_nonpos hn.le hn1.le)]

/-- The coordinate logarithmic mode itself has every positive finite real
`Lᵖ` exponent on the native unit ball. -/
theorem memLp_coordinate_mul_log_vecEuclideanNorm_unitBall
    {d : ℕ} (hd : 0 < d) (k : Fin d) {p : ℝ} (hp : 0 < p) :
    MemLp (fun x : Vec d => x k * Real.log (vecEuclideanNorm x))
      (ENNReal.ofReal p) (volume.restrict (euclideanBall 0 1)) := by
  apply (memLp_log_vecEuclideanNorm_unitBall hd hp).mono
  · exact (measurable_pi_apply k).mul measurable_log_vecEuclideanNorm
      |>.aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict (measurableSet_euclideanBall 0 1)] with x hx
    rw [norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    rw [Real.norm_eq_abs]
    have hx' : vecEuclideanNorm x < 1 := by
      simpa only [mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num : (0 : ℝ) < 1),
        sub_zero] using hx
    exact (abs_apply_le_vecEuclideanNorm x k).trans
      hx'.le

/-- Each coordinate of the literal logarithmic gradient field has every
positive finite real `Lᵖ` exponent on the native unit ball. -/
theorem memLp_radialLogGradientField_apply_unitBall
    {d : ℕ} (hd : 0 < d) (k i : Fin d) {p : ℝ} (hp : 0 < p) :
    MemLp (fun x : Vec d => radialLogGradientField k x i)
      (ENNReal.ofReal p) (volume.restrict (euclideanBall 0 1)) := by
  let μ := volume.restrict (euclideanBall (0 : Vec d) 1)
  let : IsFiniteMeasure μ := ⟨by
    simpa only [μ, Measure.restrict_apply_univ] using
      lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top (0 : Vec d) (by norm_num))⟩
  have hdom := (memLp_log_vecEuclideanNorm_unitBall hd hp).norm.add
    (memLp_const (1 : ℝ) : MemLp (fun _ : Vec d => (1 : ℝ)) (ENNReal.ofReal p) μ)
  apply hdom.mono
  · exact (measurable_radialLogGradientField_apply k i).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    change |radialLogGradientField k x i| ≤
      |(|Real.log (vecEuclideanNorm x)| + (1 : ℝ))|
    have hbasis : |basisVec k i| ≤ (1 : ℝ) := by
      by_cases hik : i = k <;> simp [basisVec_apply, hik]
    have hfirst : |basisVec k i * Real.log (vecEuclideanNorm x)| ≤
        |Real.log (vecEuclideanNorm x)| := by
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hbasis
        (abs_nonneg (Real.log (vecEuclideanNorm x)))
    calc
      |radialLogGradientField k x i| ≤
          |Real.log (vecEuclideanNorm x)| + |x k * x i / vecNormSq x| := by
        rw [radialLogGradientField]
        exact (abs_add_le _ _).trans (add_le_add hfirst le_rfl)
      _ ≤ |Real.log (vecEuclideanNorm x)| + 1 := by
        gcongr
        exact abs_radial_ratio_le_one k i x
      _ = |(|Real.log (vecEuclideanNorm x)| + (1 : ℝ))| := by
        exact (abs_of_nonneg (add_nonneg (abs_nonneg _) zero_le_one)).symm

/-- The native Euclidean magnitude of the literal logarithmic gradient field
has every positive finite real `Lᵖ` exponent on the native unit ball. -/
theorem memLp_vecEuclideanNorm_radialLogGradientField_unitBall
    {d : ℕ} (hd : 0 < d) (k : Fin d) {p : ℝ} (hp : 0 < p) :
    MemLp (fun x : Vec d => vecEuclideanNorm (radialLogGradientField k x))
      (ENNReal.ofReal p) (volume.restrict (euclideanBall 0 1)) :=
  memLp_vecEuclideanNorm_of_coordinate
    (fun i => memLp_radialLogGradientField_apply_unitBall hd k i hp)

end

end PDE
