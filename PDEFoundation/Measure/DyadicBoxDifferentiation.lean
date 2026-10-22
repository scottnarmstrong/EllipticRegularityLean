module

public import PDEFoundation.Measure.DyadicBoxAverageComparison
public import PDEFoundation.Measure.FiniteVectorMean
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.MeasureTheory.Covering.Differentiation

@[expose] public section

namespace PDE
open BoxIntegral MeasureTheory Filter Set
open scoped Topology ENNReal

/-- Positive geometric radii tend to zero from above. -/
theorem tendsto_dyadic_supRadius_nhdsGT {d : ℕ} (I : Box (Fin d)) (hd : 0 < d) :
    Tendsto (fun n : ℕ => ‖I.upper - I.lower‖ / (2 : ℝ) ^ n) atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (show (0:ℝ) ≤ 1/2 by norm_num) (show (1:ℝ)/2 < 1 by norm_num)).const_mul
      ‖I.upper - I.lower‖
    simpa only [mul_zero, div_pow, one_pow, div_eq_mul_inv, one_mul, inv_pow] using h
  · exact Eventually.of_forall fun n => dyadicBoxAtDepth_radius_pos I hd n

/-- Actual scalar averages on every literal dyadic generation converge at
almost every point of a root box for locally integrable data. -/
theorem ae_tendsto_integralAverage_dyadicBoxAtDepth_of_locallyIntegrable
    {d : ℕ} (I : Box (Fin d)) (hd : 0 < d) {f : Vec d → ℝ}
    (hf : LocallyIntegrable f volume) :
    ∀ᵐ x ∂volume.restrict (I : Set (Vec d)), ∀ hx : x ∈ (I : Set (Vec d)),
      Tendsto (fun n => integralAverage (dyadicBoxAtDepth I x hx n : Set (Vec d)) f)
        atTop (𝓝 (f x)) := by
  have hLeb := (Besicovitch.vitaliFamily (volume : Measure (Vec d))).ae_tendsto_average_norm_sub hf
  filter_upwards [ae_restrict_of_ae hLeb] with x hxLeb
  intro hx
  let r : ℕ → ℝ := fun n => ‖I.upper - I.lower‖ / (2 : ℝ) ^ n
  let C := (2 * ‖I.upper - I.lower‖) ^ d / (volume (I : Set (Vec d))).toReal
  have hclosed := hxLeb.comp ((Besicovitch.tendsto_filterAt volume x).comp
    (tendsto_dyadic_supRadius_nhdsGT I hd))
  have hclosed' : Tendsto
      (fun n => integralAverage (Metric.closedBall x (r n)) (fun y => |f y - f x|))
      atTop (𝓝 0) := by
    simpa only [r, Real.norm_eq_abs, setAverage_eq, measureReal_def, integralAverage,
      smul_eq_mul] using! hclosed
  have hdom := hclosed'.const_mul C
  rw [mul_zero] at hdom
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) _ hdom
  intro n
  rw [Real.norm_eq_abs]
  let Q : Set (Vec d) := dyadicBoxAtDepth I x hx n
  let B : Set (Vec d) := Metric.closedBall x (r n)
  have hBInt : IntegrableOn f B volume := hf.integrableOn_isCompact (isCompact_closedBall x _)
  have hBTop : volume B < ∞ := (isCompact_closedBall x (r n)).measure_lt_top
  have hQInt := hBInt.mono_set (dyadicBoxAtDepth_subset_closedBall I x hx n)
  have hQpos : 0 < volume Q := by
    exact ENNReal.toReal_pos_iff.mp (volume_box_toReal_pos (dyadicBoxAtDepth I x hx n)) |>.1
  have hQtop : volume Q < ∞ :=
    volume_dyadicDescendant_lt_top I (dyadicPathAtDepth I x hx n)
  have hdevInt : IntegrableOn (fun y => |f y - f x|) B volume := by
    simpa only [Real.norm_eq_abs] using! (hBInt.sub (integrableOn_const hBTop.ne)).norm
  exact (abs_integralAverage_sub_le_integralAverage_abs_sub (f x) hQInt hQpos hQtop).trans
    (integralAverage_dyadicBoxAtDepth_le_closedBall_of_nonneg I x hx n hd hdevInt
      (fun y _ => abs_nonneg _))

/-- Root-integrable data are differentiated by their actual dyadic averages;
the global differentiation theorem is applied to the literal zero extension. -/
theorem ae_tendsto_integralAverage_dyadicBoxAtDepth
    {d : ℕ} (I : Box (Fin d)) (hd : 0 < d) {f : Vec d → ℝ}
    (hf : IntegrableOn f (I : Set (Vec d)) volume) :
    ∀ᵐ x ∂volume.restrict (I : Set (Vec d)), ∀ hx : x ∈ (I : Set (Vec d)),
      Tendsto (fun n => integralAverage (dyadicBoxAtDepth I x hx n : Set (Vec d)) f)
        atTop (𝓝 (f x)) := by
  let f₀ := (I : Set (Vec d)).indicator f
  have hf₀ : LocallyIntegrable f₀ volume :=
    (hf.integrable_indicator I.measurableSet_coe).locallyIntegrable
  have hdiff := ae_tendsto_integralAverage_dyadicBoxAtDepth_of_locallyIntegrable I hd hf₀
  filter_upwards [hdiff] with x hxDiff
  intro hx
  have hpoint : f₀ x = f x := Set.indicator_of_mem hx f
  have hmeans : ∀ n,
      integralAverage (dyadicBoxAtDepth I x hx n : Set (Vec d)) f₀ =
        integralAverage (dyadicBoxAtDepth I x hx n : Set (Vec d)) f := by
    intro n
    unfold integralAverage
    congr 1
    apply setIntegral_congr_fun (dyadicBoxAtDepth I x hx n).measurableSet_coe
    intro y hy
    exact Set.indicator_of_mem
      (dyadicDescendant_le I (dyadicPathAtDepth I x hx n) hy) f
  simpa only [hpoint, hmeans] using hxDiff hx

/-- Coordinatewise L2 data with an arbitrary finite output dimension are
recovered almost everywhere by the actual dyadic vector means. -/
theorem ae_tendsto_coordinateVectorAverage_dyadicBoxAtDepth
    {d m : ℕ} (I : Box (Fin d)) (hd : 0 < d) {g : Vec d → Vec m}
    (hg : ∀ i : Fin m, MemLp (fun x => g x i) 2 (volumeOn (I : Set (Vec d)))) :
    ∀ᵐ x ∂volume.restrict (I : Set (Vec d)), ∀ hx : x ∈ (I : Set (Vec d)),
      Tendsto (fun n => coordinateVectorAverage (dyadicBoxAtDepth I x hx n : Set (Vec d)) g)
        atTop (𝓝 (g x)) := by
  let : IsFiniteMeasure (volumeOn (I : Set (Vec d))) :=
    isFiniteMeasure_restrict.mpr (I.measure_coe_lt_top volume).ne
  have hcoords : ∀ i : Fin m, ∀ᵐ x ∂volume.restrict (I : Set (Vec d)),
      ∀ hx : x ∈ (I : Set (Vec d)),
        Tendsto (fun n => integralAverage (dyadicBoxAtDepth I x hx n : Set (Vec d))
          (fun y => g y i)) atTop (𝓝 (g x i)) := fun i =>
    ae_tendsto_integralAverage_dyadicBoxAtDepth I hd ((hg i).integrable (by norm_num))
  filter_upwards [ae_all_iff.mpr hcoords] with x hxCoords
  intro hx
  apply tendsto_pi_nhds.mpr
  intro i
  exact hxCoords i hx

end PDE
