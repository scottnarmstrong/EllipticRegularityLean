module

public import PDEFoundation.Analysis.Inequalities.Trudinger.Distribution
public import PDEFoundation.Analysis.Inequalities.Bridges.ExponentLowering
public import PDEFoundation.Sobolev.Inequalities.ConvexRiesz
public import PDEFoundation.Sobolev.W1p.ZeroGradient
public import PDEFoundation.Sobolev.W1p.EuclideanGradient

/-!
# The Trudinger inequality (Proposition 1.18)
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE
namespace Trudinger

/-- The Trudinger inequality (Proposition 1.18). -/
theorem exists_trudinger_constant_full (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : W1pFunction (euclideanBall (0 : Vec d) 1) (ENNReal.ofReal d),
      ∀ t : ℝ, 0 < t →
        (volume {z ∈ euclideanBall (0 : Vec d) 1 |
            t < |u.toFun z - integralAverage (euclideanBall (0 : Vec d) 1) u.toFun|}).toReal ≤
          (if (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal d)
                (volumeOn (euclideanBall (0 : Vec d) 1))).toReal = 0 then 0 else
            C * Real.exp (-(1 / C) * (t / (eLpNorm (fun x => vecEuclideanNorm (u.grad x))
                (ENNReal.ofReal d) (volumeOn (euclideanBall (0 : Vec d) 1))).toReal) ^
                ((d : ℝ) / ((d : ℝ) - 1)))) := by
  refine ⟨trudingerConst d, trudingerConst_pos hd, fun u t ht => ?_⟩
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hB : MeasurableSet (unitBall d) := measurableSet_euclideanBall _ _
  have hUopen := isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) (one_pos : (0 : ℝ) < 1)
  have hvolpos := volume_euclideanBall_pos (0 : Vec d) (one_pos : (0 : ℝ) < 1)
  have hvolne := volume_euclideanBall_ne_top (0 : Vec d) (zero_le_one : (0 : ℝ) ≤ 1)
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal d := ENNReal.one_le_ofReal.2 (by linarith)
  have hpne : ENNReal.ofReal d ≠ ⊤ := ENNReal.ofReal_ne_top
  have hp0 : ENNReal.ofReal d ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  set G : Vec d → ℝ := fun x => vecEuclideanNorm (u.grad x) with hGdef
  have hGmem : MemLp G (ENNReal.ofReal d) (volumeOn (unitBall d)) :=
    u.gradMemLp.memLp_vecEuclideanNorm
  set E := eLpNorm G (ENNReal.ofReal d) (volumeOn (unitBall d)) with hE
  have hEne : E ≠ ⊤ := hGmem.eLpNorm_ne_top
  change _ ≤ (if E.toReal = 0 then 0 else _)
  split_ifs with hN0
  · -- vanishing gradient
    have hE0 : E = 0 := by
      rcases ENNReal.toReal_eq_zero_iff _ |>.1 hN0 with h | h
      · exact h
      · exact absurd h hEne
    have hG0 : G =ᵐ[volumeOn (unitBall d)] 0 :=
      (eLpNorm_eq_zero_iff hp0).1 hE0
    have hgrad : u.grad =ᵐ[volumeOn (unitBall d)] 0 := by
      filter_upwards [hG0] with x hx
      exact vecEuclideanNorm_eq_zero_iff.1 hx
    have hconst := W1pFunction.ae_eq_integralAverage_of_grad_ae_eq_zero hp1 hpne hUopen hvolpos
      (lt_top_iff_ne_top.2 hvolne) u hgrad
    have hae := (ae_restrict_iff' hB).1 hconst
    have hnull : volume {z | z ∈ unitBall d ∧ t < |u.toFun z - integralAverage (unitBall d) u.toFun|}
        = 0 := by
      refine measure_mono_null (fun z hz => ?_) (ae_iff.1 hae)
      intro hzz
      obtain ⟨hz1, hz2⟩ := hz
      rw [hzz hz1, sub_self, abs_zero] at hz2
      linarith
    change (volume {z | z ∈ unitBall d ∧ t < |u.toFun z - integralAverage (unitBall d) u.toFun|}).toReal
      ≤ 0
    rw [hnull]; simp
  · have hNpos : 0 < E.toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hN0)
    set N := E.toReal with hNdef
    have hEN : E = ENNReal.ofReal N := (ENNReal.ofReal_toReal hEne).symm
    -- measurable nonnegative representative of the gradient magnitude
    have hmeas : AEMeasurable G (volumeOn (unitBall d)) := hGmem.aestronglyMeasurable.aemeasurable
    set G' : Vec d → ℝ := fun y => |hmeas.mk G y| with hG'def
    have hG'm : Measurable G' := continuous_abs.measurable.comp hmeas.measurable_mk
    have hG'nn : ∀ y, 0 ≤ G' y := fun y => abs_nonneg _
    have hGG' : G' =ᵐ[volumeOn (unitBall d)] G := by
      filter_upwards [hmeas.ae_eq_mk] with y hy
      simp only [hG'def, ← hy]
      exact abs_of_nonneg (vecEuclideanNorm_nonneg _)
    have hLd : ∫⁻ y in unitBall d, ENNReal.ofReal (G' y) ^ (d : ℝ) =
        ENNReal.ofReal N ^ (d : ℝ) := by
      have h1 : ∫⁻ y in unitBall d, ENNReal.ofReal (G' y) ^ (d : ℝ) =
          ∫⁻ y, ‖G y‖ₑ ^ (d : ℝ) ∂(volumeOn (unitBall d)) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hGG'] with y hy
        rw [hy, Real.enorm_eq_ofReal (vecEuclideanNorm_nonneg _)]
      rw [h1, lintegral_rpow_enorm_eq_rpow_eLpNorm' hd0, ← hEN, hE,
        eLpNorm_eq_eLpNorm' hp0 hpne hGmem.aestronglyMeasurable, ENNReal.toReal_ofReal hd0.le]
    have hL1 : ∫⁻ y in unitBall d, ENNReal.ofReal (G' y) ≤
        ENNReal.ofReal N * volume (unitBall d) ^ (((d : ℝ) - 1) / d) := by
      have h1 : ∫⁻ y in unitBall d, ENNReal.ofReal (G' y) =
          eLpNorm G 1 (volumeOn (unitBall d)) := by
        rw [eLpNorm_one_eq_lintegral_enorm hGmem.aestronglyMeasurable]
        refine lintegral_congr_ae ?_
        filter_upwards [hGG'] with y hy
        rw [hy, Real.enorm_eq_ofReal (vecEuclideanNorm_nonneg _)]
      rw [h1]
      refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp1 hGmem.aestronglyMeasurable).trans ?_
      rw [Measure.restrict_apply_univ, ENNReal.toReal_ofReal hd0.le]
      simp only [ENNReal.toReal_one, div_one]
      have : (1 : ℝ) - 1 / d = ((d : ℝ) - 1) / d := by field_simp
      rw [this]
      exact mul_le_mul' (le_of_eq (hE.symm.trans hEN)) le_rfl
    -- Riesz bound
    have hRiesz := abs_sub_integralAverage_ae_le_riesz (V := unitBall d) (S := unitBall d)
      (D := 2 * 1) hUopen (hasEuclideanDiameterLE_euclideanBall (0 : Vec d) one_pos)
      (Ch1Bridges.W1pFunction.lower (U := unitBall d) hvolne hp1 u) hB
      subset_rfl hvolpos
    have hw : ∀ᵐ x ∂volumeOn (unitBall d),
        |u.toFun x - integralAverage (unitBall d) u.toFun| ≤ rieszConst d *
          ∫ y in unitBall d, vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d) * G' y := by
      filter_upwards [hRiesz] with x hx
      have hI : ∫ y in unitBall d, vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d) * G' y =
          ∫ y in unitBall d, vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d) *
            vecEuclideanNorm (u.grad y) := by
        refine integral_congr_ae ?_
        filter_upwards [hGG'] with y hy
        rw [hy]
      rw [hI]
      have hc : (2 * 1 : ℝ) ^ d / (d * (volume (unitBall d)).toReal) = rieszConst d := by
        rw [rieszConst, unitVol, mul_one]
      simpa only [Ch1Bridges.W1pFunction.lower_toFun, Ch1Bridges.W1pFunction.lower_grad, hc] using hx
    exact distribution_le hd hG'm hG'nn hNpos hLd hL1 hw ht
