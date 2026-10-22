module

public import PDEFoundation.FunctionalInequalities.SobolevSharpOne.SmoothLimit
public import PDEFoundation.FunctionalInequalities.SobolevSharpOne.LayerCakeMinkowski
public import PDEFoundation.FunctionalInequalities.SobolevSharpOne.Density
public import PDEFoundation.FunctionalInequalities.BrunnMinkowskiProof

/-!
# Assembly of the sharp `p = 1` Sobolev inequality for `d ≥ 2`
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory Set

namespace PDE.SobolevSharp

theorem exponent_eq {d : ℕ} (hd : 2 ≤ d) :
    ((d : ℝ≥0∞) / ((d : ℝ≥0∞) - 1)) = ENNReal.ofReal ((d : ℝ) / ((d : ℝ) - 1)) := by
  have h1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have h2 : (1 : ℝ) < d := by exact_mod_cast (by omega : 1 < d)
  rw [ENNReal.ofReal_div_of_pos (by linarith), ENNReal.ofReal_natCast,
    ENNReal.ofReal_sub _ zero_le_one, ENNReal.ofReal_natCast, ENNReal.ofReal_one]

theorem const_eq {d : ℕ} (hd : 1 ≤ d) :
    ENNReal.ofReal (((d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal ^ ((1 : ℝ) / d))⁻¹) =
      ((d : ℝ≥0∞) * volume (euclideanBall (0 : Vec d) 1) ^ ((1 : ℝ) / d))⁻¹ := by
  have hpos := volume_euclideanBall_toReal_pos (0 : Vec d) (R := 1) one_pos
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_mul hd0.le,
    ENNReal.ofReal_natCast, ← ENNReal.ofReal_rpow_of_nonneg hpos.le (by positivity),
    ENNReal.ofReal_toReal (volume_euclideanBall_ne_top (0 : Vec d) zero_le_one)]

theorem sobolev_sharp_one_of_two_le (d : ℕ) (hd : 2 ≤ d)
    (u : W1pFunction (Set.univ : Set (Vec d)) 1) :
    eLpNorm u.toFun ((d : ℝ≥0∞) / ((d : ℝ≥0∞) - 1)) volume ≤
      ENNReal.ofReal (((d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal ^ ((1 : ℝ) / d))⁻¹) *
        eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 1 volume := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (1 : ℝ) < d := by exact_mod_cast (by omega : 1 < d)
  have hd0 : (0 : ℝ) < d := by linarith
  set V := volume (euclideanBall (0 : Vec d) 1) with hV
  have hVne : V ≠ ∞ := volume_euclideanBall_ne_top _ zero_le_one
  have hVpos : 0 < V := volume_euclideanBall_pos _ one_pos
  have hc0 : (d : ℝ≥0∞) * V ^ ((1 : ℝ) / d) ≠ 0 := by
    refine mul_ne_zero (by exact_mod_cast (by omega : d ≠ 0)) ?_
    exact (ENNReal.rpow_pos hVpos hVne).ne'
  have hctop : (d : ℝ≥0∞) * V ^ ((1 : ℝ) / d) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top d)
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) hVne)
  rw [const_eq hd1, exponent_eq hd]
  refine eLpNorm_le_of_forall_compactSmooth (ENNReal.inv_ne_top.mpr hc0) ?_ u
  intro ψ hψ hc
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by exact_mod_cast le_top)
  have hq : (1 : ℝ) ≤ (d : ℝ) / ((d : ℝ) - 1) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hcont : Continuous ψ := hψ1.continuous
  have step1 : eLpNorm ψ (ENNReal.ofReal ((d : ℝ) / ((d : ℝ) - 1))) volume ≤
      ∫⁻ s in Ioi (0 : ℝ), volume {x | s ≤ |ψ x|} ^ (((d : ℝ) - 1) / d) := by
    have hm : Measurable fun x => |ψ x| := hcont.abs.measurable
    have := eLpNorm_le_lintegral_meas_lt_rpow volume hm (fun x => abs_nonneg _) hq
    have habs : eLpNorm (fun x => |ψ x|) (ENNReal.ofReal ((d : ℝ) / ((d : ℝ) - 1))) volume =
        eLpNorm ψ (ENNReal.ofReal ((d : ℝ) / ((d : ℝ) - 1))) volume := by
      simpa only [Real.norm_eq_abs] using eLpNorm_norm (μ := volume) (f := ψ) hcont.aestronglyMeasurable
        (p := ENNReal.ofReal ((d : ℝ) / ((d : ℝ) - 1)))
    rw [← habs]
    refine this.trans (lintegral_mono fun s => ?_)
    have : 1 / ((d : ℝ) / ((d : ℝ) - 1)) = ((d : ℝ) - 1) / d := by
      field_simp
    rw [this]
    exact ENNReal.rpow_le_rpow (measure_mono fun x (hx : s < |ψ x|) => hx.le) (by
      have : (0 : ℝ) < d - 1 := by linarith
      positivity)
  have step2 := sharp_layer_bound (d := d) hd
    (fun A B hA hB hAn hBn => PDE.BrunnMinkowskiProof.result d (by omega) A B hA hB hAn hBn) hψ1 hc
  have hgrad : eLpNorm (fun x => vecEuclideanNorm (classicalGradient ψ x)) 1 volume =
      ∫⁻ x, ENNReal.ofReal (gradNorm ψ x) := by
    change eLpNorm (gradNorm ψ) 1 volume = _
    rw [eLpNorm_one_eq_lintegral_enorm (continuous_gradNorm hψ1).aestronglyMeasurable]
    refine lintegral_congr fun x => ?_
    exact Real.enorm_eq_ofReal (vecEuclideanNorm_nonneg _)
  rw [hgrad]
  refine step1.trans ?_
  exact (ENNReal.mul_le_iff_le_inv hc0 hctop).mp step2

end PDE.SobolevSharp
