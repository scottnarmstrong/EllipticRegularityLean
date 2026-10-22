module

public import PDEFoundation.Ambient.EuclideanNorm
public import PDEFoundation.Geometry.ConvexSegment
public import PDEFoundation.Geometry.EuclideanBall
public import PDEFoundation.Measure.EuclideanRadialPower
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The Riesz kernel collapse along segments

For a nonnegative measurable weight `g` and a point `x`, integrating `g` along the
segments from `x` to the points `y` of a set `S` of Euclidean radius at most `D`
around `x` is bounded by `D ^ d / d` times the Riesz potential `∫ |x - z|^(1-d) g z dz`.
The proof is a dilation change of variables for each segment parameter, followed by the
elementary integral in the segment parameter. Everything is done in `ℝ≥0∞`, so no
integrability hypotheses are needed.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE

variable {d : ℕ}

/-- The elementary parameter integral behind the kernel collapse. -/
theorem lintegral_segment_parameter_le {D r : ℝ} (hd : 0 < d) (hD : 0 < D) (hr : 0 < r) :
    ∫⁻ s in Ioc (0 : ℝ) 1,
        ENNReal.ofReal (s⁻¹ * (s ^ d)⁻¹) * (if r ≤ s * D then 1 else 0) ≤
      ENNReal.ofReal (D ^ d / (d * r ^ d)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  set a : ℝ := r / D with ha
  have ha0 : 0 < a := div_pos hr hD
  have hstep : ∫⁻ s in Ioc (0 : ℝ) 1,
        ENNReal.ofReal (s⁻¹ * (s ^ d)⁻¹) * (if r ≤ s * D then 1 else 0) ≤
      ∫⁻ s in Ioi a, ENNReal.ofReal (s ^ (-((d : ℝ) + 1))) := by
    calc _ ≤ ∫⁻ s in Ioc (0 : ℝ) 1,
            (Ici a).indicator (fun s => ENNReal.ofReal (s ^ (-((d : ℝ) + 1)))) s := by
          refine setLIntegral_mono (Measurable.indicator (by fun_prop) measurableSet_Ici) ?_
          intro s hs
          by_cases hsa : r ≤ s * D
          · have hsa' : a ≤ s := by
              rw [ha, div_le_iff₀ hD]; exact hsa
            simp only [indicator_of_mem (mem_Ici.2 hsa'), hsa, ↓reduceIte, mul_one]
            refine le_of_eq (by
              congr 1
              rw [Real.rpow_neg hs.1.le, Real.rpow_add hs.1, Real.rpow_natCast, Real.rpow_one]
              field_simp)
          · simp [hsa]
      _ ≤ ∫⁻ s, (Ici a).indicator (fun s => ENNReal.ofReal (s ^ (-((d : ℝ) + 1)))) s :=
          setLIntegral_le_lintegral _ _
      _ = ∫⁻ s in Ici a, ENNReal.ofReal (s ^ (-((d : ℝ) + 1))) :=
          lintegral_indicator measurableSet_Ici _
      _ = _ := setLIntegral_congr Ioi_ae_eq_Ici.symm
  refine hstep.trans ?_
  have hint : IntegrableOn (fun s : ℝ => s ^ (-((d : ℝ) + 1))) (Ioi a) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) ha0
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi a)] fun s : ℝ => s ^ (-((d : ℝ) + 1)) :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs =>
      Real.rpow_nonneg (ha0.trans hs).le _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn,
    integral_Ioi_rpow_of_lt (by linarith) ha0]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  have : -((d : ℝ) + 1) + 1 = -(d : ℝ) := by ring
  rw [this, Real.rpow_neg ha0.le, Real.rpow_natCast, ha, div_pow]
  field_simp

/-- Dilation about `x` by a positive factor `s` scales the Lebesgue lintegral by `(s ^ d)⁻¹`. -/
theorem lintegral_comp_dilation {H : Vec d → ℝ≥0∞} (hH : Measurable H) (x : Vec d) {s : ℝ}
    (hs : 0 < s) :
    ∫⁻ y, H (x + s • (y - x)) = ENNReal.ofReal ((s ^ d)⁻¹) * ∫⁻ z, H z := by
  have h1 : ∫⁻ y, H (x + s • (y - x)) = ∫⁻ w, H (x + s • w) :=
    lintegral_sub_right_eq_self (fun w => H (x + s • w)) x
  have h2 : ∫⁻ w, H (x + s • w) = ∫⁻ w, (fun z => H (x + z)) (s • w) := rfl
  have hmap := Measure.map_addHaar_smul (volume : Measure (Vec d)) hs.ne'
  have hfin : Module.finrank ℝ (Vec d) = d := by simp
  rw [h1, h2, ← lintegral_map (f := fun z => H (x + z)) (by fun_prop)
    (measurable_const_smul s), hmap, hfin, abs_of_pos (by positivity), lintegral_smul_measure,
    lintegral_add_left_eq_self (fun z => H z) x, smul_eq_mul]

private theorem vecEuclideanNorm_sub_dilation_of_pos (x y : Vec d) {s : ℝ} (hs : 0 < s) :
    vecEuclideanNorm (x - (x + s • (y - x))) = s * vecEuclideanNorm (x - y) := by
  have : x - (x + s • (y - x)) = s • (x - y) := by
    ext i; simp; ring
  rw [this, vecEuclideanNorm_smul, abs_of_pos hs]

/-- The weight along the segments at parameter `s`, truncated to `|x - z| ≤ s D`. -/
noncomputable def segmentSliceWeight (g : Vec d → ℝ≥0∞) (x : Vec d) (D s : ℝ) (z : Vec d) :
    ℝ≥0∞ :=
  if vecEuclideanNorm (x - z) ≤ s * D then
    ENNReal.ofReal (vecEuclideanNorm (x - z)) * g z else 0

theorem measurable_segmentSliceWeight {g : Vec d → ℝ≥0∞} (hg : Measurable g) (x : Vec d)
    (D s : ℝ) : Measurable (segmentSliceWeight g x D s) := by
  unfold segmentSliceWeight
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_le (continuous_vecEuclideanNorm.comp
      (continuous_const.sub continuous_id)).measurable measurable_const
  · exact (ENNReal.measurable_ofReal.comp (continuous_vecEuclideanNorm.comp
      (continuous_const.sub continuous_id)).measurable).mul hg

/-- The change of variables for one segment parameter. -/
theorem lintegral_segment_slice_le {g : Vec d → ℝ≥0∞} (hg : Measurable g) (x : Vec d) {D : ℝ}
    {S : Set (Vec d)} (hS : MeasurableSet S) (hSD : ∀ y ∈ S, vecEuclideanNorm (x - y) ≤ D)
    {s : ℝ} (hs : 0 < s) :
    ∫⁻ y in S, g (x + s • (y - x)) * ENNReal.ofReal (vecEuclideanNorm (x - y)) ≤
      ENNReal.ofReal (s⁻¹ * (s ^ d)⁻¹) * ∫⁻ z, segmentSliceWeight g x D s z := by
  have hpt : ∀ y ∈ S, g (x + s • (y - x)) * ENNReal.ofReal (vecEuclideanNorm (x - y)) =
      ENNReal.ofReal s⁻¹ * segmentSliceWeight g x D s (x + s • (y - x)) := by
    intro y hy
    have hn := vecEuclideanNorm_sub_dilation_of_pos x y hs
    have hle : vecEuclideanNorm (x - (x + s • (y - x))) ≤ s * D := by
      rw [hn]; exact mul_le_mul_of_nonneg_left (hSD y hy) hs.le
    simp only [segmentSliceWeight, hle, ↓reduceIte]
    rw [hn]
    rw [ENNReal.ofReal_mul hs.le, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
      inv_mul_cancel₀ hs.ne', ENNReal.ofReal_one, one_mul, mul_comm]
  calc ∫⁻ y in S, g (x + s • (y - x)) * ENNReal.ofReal (vecEuclideanNorm (x - y))
      = ∫⁻ y in S, ENNReal.ofReal s⁻¹ * segmentSliceWeight g x D s (x + s • (y - x)) :=
        setLIntegral_congr_fun hS hpt
    _ ≤ ∫⁻ y, ENNReal.ofReal s⁻¹ * segmentSliceWeight g x D s (x + s • (y - x)) :=
        setLIntegral_le_lintegral _ _
    _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_comp_dilation
          (measurable_segmentSliceWeight hg x D s) x hs, ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity)]

private theorem lintegral_time_collapse_pointwise (hd : 0 < d) {g : Vec d → ℝ≥0∞} {D : ℝ}
    (hD : 0 < D) (x z : Vec d) :
    ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (s⁻¹ * (s ^ d)⁻¹) *
        segmentSliceWeight g x D s z ≤
      ENNReal.ofReal (D ^ d / d) *
        (ENNReal.ofReal (vecEuclideanNorm (x - z) ^ ((1 : ℝ) - d)) * g z) := by
  set r := vecEuclideanNorm (x - z) with hr
  have hrnn : 0 ≤ r := vecEuclideanNorm_nonneg _
  rcases hrnn.eq_or_lt with hr0 | hrpos
  · have : ∀ s : ℝ, segmentSliceWeight g x D s z = 0 := by
      intro s; unfold segmentSliceWeight; rw [← hr, ← hr0]; simp
    simp [this]
  · have hW : ∀ s : ℝ, segmentSliceWeight g x D s z =
        (ENNReal.ofReal r * g z) * (if r ≤ s * D then 1 else 0) := by
      intro s; unfold segmentSliceWeight; rw [← hr]; split_ifs <;> simp
    have hcol := lintegral_segment_parameter_le (r := r) hd hD hrpos
    calc _ = ∫⁻ s in Ioc (0 : ℝ) 1, (ENNReal.ofReal r * g z) *
            (ENNReal.ofReal (s⁻¹ * (s ^ d)⁻¹) * (if r ≤ s * D then 1 else 0)) := by
          refine lintegral_congr fun s => ?_
          rw [hW]; ring
      _ = (ENNReal.ofReal r * g z) * ∫⁻ s in Ioc (0 : ℝ) 1,
            ENNReal.ofReal (s⁻¹ * (s ^ d)⁻¹) * (if r ≤ s * D then 1 else 0) := by
          rw [lintegral_const_mul]
          refine ENNReal.measurable_ofReal.comp (by fun_prop) |>.mul ?_
          exact Measurable.ite (measurableSet_le measurable_const (by fun_prop)) measurable_const
            measurable_const
      _ ≤ (ENNReal.ofReal r * g z) * ENNReal.ofReal (D ^ d / (d * r ^ d)) :=
          by gcongr
      _ = _ := by
          have hid : r * (D ^ d / (d * r ^ d)) = D ^ d / d * r ^ ((1 : ℝ) - d) := by
            rw [Real.rpow_sub hrpos, Real.rpow_one, Real.rpow_natCast]
            have : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
            have : r ^ d ≠ 0 := by positivity
            field_simp
          have hid' : ENNReal.ofReal r * ENNReal.ofReal (D ^ d / (d * r ^ d)) =
              ENNReal.ofReal (D ^ d / d) * ENNReal.ofReal (r ^ ((1 : ℝ) - d)) := by
            rw [← ENNReal.ofReal_mul hrnn, ← ENNReal.ofReal_mul (by positivity), hid]
          calc (ENNReal.ofReal r * g z) * ENNReal.ofReal (D ^ d / (d * r ^ d))
              = g z * (ENNReal.ofReal r * ENNReal.ofReal (D ^ d / (d * r ^ d))) := by ring
            _ = _ := by rw [hid']; ring

private theorem measurable_segmentSliceWeight_uncurry {g : Vec d → ℝ≥0∞} (hg : Measurable g)
    (x : Vec d) (D : ℝ) :
    Measurable (fun q : ℝ × Vec d => segmentSliceWeight g x D q.1 q.2) := by
  unfold segmentSliceWeight
  have hn : Continuous fun q : ℝ × Vec d => vecEuclideanNorm (x - q.2) :=
    continuous_vecEuclideanNorm.comp (continuous_const.sub continuous_snd)
  refine Measurable.ite (measurableSet_le hn.measurable (by fun_prop)) ?_ measurable_const
  exact (ENNReal.measurable_ofReal.comp hn.measurable).mul (hg.comp measurable_snd)

/-- Integration of a weight along the segments from `x` to the points of `S` is bounded by
`D ^ d / d` times the Riesz potential of the weight at `x`. -/
theorem lintegral_lintegral_segment_le_riesz (hd : 0 < d) {g : Vec d → ℝ≥0∞} (hg : Measurable g)
    (x : Vec d) {D : ℝ} (hD : 0 < D) {S : Set (Vec d)} (hS : MeasurableSet S)
    (hSD : ∀ y ∈ S, vecEuclideanNorm (x - y) ≤ D) :
    ∫⁻ y in S, ∫⁻ s in Ioc (0 : ℝ) 1,
        g (x + s • (y - x)) * ENNReal.ofReal (vecEuclideanNorm (x - y)) ≤
      ENNReal.ofReal (D ^ d / d) *
        ∫⁻ z, ENNReal.ofReal (vecEuclideanNorm (x - z) ^ ((1 : ℝ) - d)) * g z := by
  have hn : Continuous fun y : Vec d => vecEuclideanNorm (x - y) :=
    continuous_vecEuclideanNorm.comp (continuous_const.sub continuous_id)
  have hmeas1 : Measurable (Function.uncurry fun (y : Vec d) (s : ℝ) =>
      g (x + s • (y - x)) * ENNReal.ofReal (vecEuclideanNorm (x - y))) := by
    refine Measurable.mul (hg.comp ?_) (ENNReal.measurable_ofReal.comp (hn.measurable.comp
      measurable_fst))
    exact (by fun_prop : Measurable fun q : Vec d × ℝ => x + q.2 • (q.1 - x))
  rw [lintegral_lintegral_swap hmeas1.aemeasurable]
  calc _ ≤ ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (s⁻¹ * (s ^ d)⁻¹) *
          ∫⁻ z, segmentSliceWeight g x D s z :=
        setLIntegral_mono' measurableSet_Ioc fun s hs =>
          lintegral_segment_slice_le hg x hS hSD hs.1
    _ = ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ z, ENNReal.ofReal (s⁻¹ * (s ^ d)⁻¹) *
          segmentSliceWeight g x D s z := by
        refine lintegral_congr fun s => ?_
        rw [lintegral_const_mul _ (measurable_segmentSliceWeight hg x D s)]
    _ = ∫⁻ z, ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (s⁻¹ * (s ^ d)⁻¹) *
          segmentSliceWeight g x D s z := by
        refine lintegral_lintegral_swap ?_
        refine Measurable.aemeasurable ?_
        exact (ENNReal.measurable_ofReal.comp (by fun_prop :
          Measurable fun q : ℝ × Vec d => q.1⁻¹ * (q.1 ^ d)⁻¹)).mul
          (measurable_segmentSliceWeight_uncurry hg x D)
    _ ≤ ∫⁻ z, ENNReal.ofReal (D ^ d / d) *
          (ENNReal.ofReal (vecEuclideanNorm (x - z) ^ ((1 : ℝ) - d)) * g z) :=
        lintegral_mono fun z => lintegral_time_collapse_pointwise hd hD x z
    _ = _ := by rw [lintegral_const_mul']; exact ENNReal.ofReal_ne_top

/-- Centered radial integrals of the Riesz kernel over a round ball around `x`. -/
theorem lintegral_riesz_kernel_ball (x : Vec d) {R : ℝ} (hR : 0 < R) (s : ℝ) :
    ∫⁻ y in {y | vecEuclideanNorm (x - y) < R}, ENNReal.ofReal (vecEuclideanNorm (x - y) ^ s) =
      ∫⁻ z in euclideanBall (0 : Vec d) R, ENNReal.ofReal (vecEuclideanNorm z ^ s) := by
  have hset : MeasurableSet (euclideanBall (0 : Vec d) R) := by
    have : euclideanBall (0 : Vec d) R =
        {z : Vec d | vecEuclideanNorm z < R} := by
      ext z
      rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hR, sub_zero]; rfl
    rw [this]
    exact measurableSet_lt continuous_vecEuclideanNorm.measurable measurable_const
  have hmem : ∀ z : Vec d, z ∈ euclideanBall (0 : Vec d) R ↔ vecEuclideanNorm z < R := by
    intro z; rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hR, sub_zero]
  have hset' : MeasurableSet {y : Vec d | vecEuclideanNorm (x - y) < R} :=
    measurableSet_lt (continuous_vecEuclideanNorm.comp
      (continuous_const.sub continuous_id)).measurable measurable_const
  rw [← lintegral_indicator hset', ← lintegral_indicator hset]
  have := lintegral_sub_left_eq_self (μ := (volume : Measure (Vec d)))
    ((euclideanBall (0 : Vec d) R).indicator fun z => ENNReal.ofReal (vecEuclideanNorm z ^ s)) x
  rw [← this]
  refine lintegral_congr fun y => ?_
  by_cases hy : vecEuclideanNorm (x - y) < R
  · simp [Set.indicator, hy, (hmem _).2 hy]
  · simp [Set.indicator, hy, mt (hmem _).1 hy]

/-- The Riesz kernel is integrable on round balls. -/
theorem lintegral_riesz_kernel_ball_lt_top (hd : 0 < d) (x : Vec d) {R : ℝ} (hR : 0 < R) :
    ∫⁻ y in {y | vecEuclideanNorm (x - y) < R},
        ENNReal.ofReal (vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d)) < ∞ := by
  rw [lintegral_riesz_kernel_ball x hR]
  have h := (integrableOn_vecEuclideanNorm_rpow_euclideanBall_iff hd (s := (1 : ℝ) - d) hR).2
    (by linarith)
  exact Integrable.lintegral_lt_top h

end PDE
