module

public import PDEFoundation.Sobolev.Mean
public import PDEFoundation.Measure.BallVolume
public import PDEFoundation.Geometry.ConvexDomain
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Basic facts for the Poincaré inequality with an adjusted mean

* the difference of means as an average of the centered function over `E`;
* a Hölder bound `∫_S |f| ≤ |S|^{1 - 1/q} ‖f‖_{L^q(B)}` for subsets `S ⊆ B`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.PoincareAdjustMean

open MeasureTheory

variable {d : ℕ}

/-- The difference of the means over `E ⊆ B` and `B` is the average over `E` of the centered
function `f - (f)_B`. -/
theorem avg_sub_avg {B E : Set (Vec d)} {f : Vec d → ℝ} (hEB : E ⊆ B)
    (hf : IntegrableOn f B volume) (hE0 : volume E ≠ 0) (hEt : volume E ≠ ⊤) :
    integralAverage E f - integralAverage B f =
      (volume E).toReal⁻¹ * ∫ x in E, (f x - integralAverage B f) := by
  have hfE : IntegrableOn f E volume := hf.mono_set hEB
  have hpos : (volume E).toReal ≠ 0 := (ENNReal.toReal_pos hE0 hEt).ne'
  rw [integral_sub hfE (integrableOn_const hEt), setIntegral_const, integralAverage]
  simp only [Measure.real, smul_eq_mul]
  field_simp

/-- The centered function has zero integral over `B`. -/
theorem integral_sub_average {B : Set (Vec d)} {f : Vec d → ℝ} (hf : IntegrableOn f B volume) (hB0 : volume B ≠ 0) (hBt : volume B ≠ ⊤) :
    ∫ x in B, (f x - integralAverage B f) = 0 := by
  have h := avg_sub_avg (subset_refl B) hf hB0 hBt
  rw [sub_self] at h
  have hpos : (volume B).toReal⁻¹ ≠ 0 := inv_ne_zero (ENNReal.toReal_pos hB0 hBt).ne'
  exact (mul_eq_zero.mp h.symm).resolve_left hpos

/-- Hölder on a subset. -/
theorem setIntegral_abs_le {B S : Set (Vec d)} (hS : MeasurableSet S) (hSB : S ⊆ B)
    (hSt : volume S ≠ ⊤) {f : Vec d → ℝ} {q : ℝ} (hq : 1 ≤ q)
    (hf : MemLp f (ENNReal.ofReal q) (volume.restrict B)) :
    ∫ x in S, |f x| ≤ (volume S).toReal ^ (1 - 1 / q) *
      (eLpNorm f (ENNReal.ofReal q) (volume.restrict B)).toReal := by
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by simpa using ENNReal.ofReal_le_ofReal hq
  have hfS : MemLp f (ENNReal.ofReal q) (volume.restrict S) :=
    hf.mono_measure (Measure.restrict_mono hSB le_rfl)
  have hint : Integrable f (volume.restrict S) := by
    have : IsFiniteMeasure (volume.restrict S) :=
      ⟨by simpa [Measure.restrict_apply_univ] using hSt.lt_top⟩
    exact MemLp.integrable hq1 hfS
  have hE1 : eLpNorm f 1 (volume.restrict S) =
      ENNReal.ofReal (∫ x in S, |f x|) := by
    rw [eLpNorm_one_eq_lintegral_enorm hint.aestronglyMeasurable, ofReal_integral_eq_lintegral_ofReal hint.abs
      (Filter.Eventually.of_forall fun x => abs_nonneg _)]
    refine lintegral_congr fun x => ?_
    rw [Real.enorm_eq_ofReal_abs]
  have hH := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict S)
    (p := 1) (q := ENNReal.ofReal q) hq1 hfS.aestronglyMeasurable
  have hmono : eLpNorm f (ENNReal.ofReal q) (volume.restrict S) ≤
      eLpNorm f (ENNReal.ofReal q) (volume.restrict B) :=
    eLpNorm_mono_measure f (Measure.restrict_mono hSB le_rfl)
  have hqpos : 0 < q := by linarith
  rw [hE1] at hH
  have hexp : (1 / (1 : ℝ≥0∞).toReal - 1 / (ENNReal.ofReal q).toReal) = 1 - 1 / q := by
    rw [ENNReal.toReal_ofReal hqpos.le]; simp
  rw [hexp] at hH
  have hexp0 : 0 ≤ 1 - 1 / q := by
    have : 1 / q ≤ 1 := by rw [div_le_one hqpos]; exact hq
    linarith
  have hfin : eLpNorm f (ENNReal.ofReal q) (volume.restrict B) ≠ ⊤ := hf.eLpNorm_ne_top
  have hSfin : (volume.restrict S) Set.univ ^ (1 - 1 / q) ≠ ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact ENNReal.rpow_ne_top_of_nonneg hexp0 hSt
  have hR : ENNReal.ofReal (∫ x in S, |f x|) ≤
      eLpNorm f (ENNReal.ofReal q) (volume.restrict B) * (volume S) ^ (1 - 1 / q) := by
    refine hH.trans ?_
    rw [Measure.restrict_apply_univ]
    gcongr
  have hnn : 0 ≤ ∫ x in S, |f x| := setIntegral_nonneg hS (fun x _ => abs_nonneg _)
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top hfin (ENNReal.rpow_ne_top_of_nonneg hexp0 hSt)) hR
  rw [ENNReal.toReal_ofReal hnn, ENNReal.toReal_mul, ← ENNReal.toReal_rpow] at this
  linarith [mul_comm (eLpNorm f (ENNReal.ofReal q) (volume.restrict B)).toReal
    ((volume S).toReal ^ (1 - 1 / q))]

end PDE.PoincareAdjustMean
