module

public import PDEFoundation.Analysis.Inequalities.PoincareAdjustMean.Holder

/-!
# Mean-difference bound for `θ ≥ 1/2` (elementary, all dimensions)

`|(u)_B - (u)_E| ≤ M |log θ|^{1/2} ‖∇u‖_{L²(B)}` when `|E| ≥ θ|B|` and `θ ≥ 1/2`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.PoincareAdjustMean

open MeasureTheory

/-- Mean-difference bound in the regime `θ ≥ 1/2`. -/
theorem exists_meanDiff_bound_half (d : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ θ : ℝ, 1 / 2 ≤ θ → θ < 1 →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      ∀ E : Set (Vec d), MeasurableSet E → E ⊆ euclideanBall (0 : Vec d) 1 →
        ENNReal.ofReal θ * volume (euclideanBall (0 : Vec d) 1) ≤ volume E →
        |integralAverage (euclideanBall (0 : Vec d) 1) u.toFun - integralAverage E u.toFun| ≤
          M * Real.sqrt |Real.log θ| *
            (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2
              (volume.restrict (euclideanBall (0 : Vec d) 1))).toReal := by
  have hBpos : 0 < volume (euclideanBall (0 : Vec d) 1) := volume_euclideanBall_pos 0 one_pos
  have hBtop : volume (euclideanBall (0 : Vec d) 1) ≠ ⊤ := volume_euclideanBall_ne_top 0 zero_le_one
  have hBm : MeasurableSet (euclideanBall (0 : Vec d) 1) := measurableSet_euclideanBall 0 1
  set V : ℝ := (volume (euclideanBall (0 : Vec d) 1)).toReal with hV
  have hVpos : 0 < V := ENNReal.toReal_pos hBpos.ne' hBtop
  refine ⟨2 * ((2 : ℝ) ^ d * 2) * (V ^ (1 / (2 : ℝ)))⁻¹, by positivity,
    fun θ hθ2 hθ1 u E hE hEB hθE => ?_⟩
  have hθ0 : 0 < θ := by linarith
  have hE0 : volume E ≠ 0 := by
    intro h
    rw [h, nonpos_iff_eq_zero] at hθE
    rcases mul_eq_zero.1 hθE with h1 | h1
    · simp at h1; linarith
    · exact hBpos.ne' h1
  have hEt : volume E ≠ ⊤ := ne_top_of_le_ne_top hBtop (measure_mono hEB)
  have hEV : θ * V ≤ (volume E).toReal := by
    have := ENNReal.toReal_mono hEt hθE
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hθ0.le] at this
  have hEpos : 0 < (volume E).toReal := ENNReal.toReal_pos hE0 hEt
  set g := (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2
    (volume.restrict (euclideanBall (0 : Vec d) 1))).toReal with hg
  have hg0 : 0 ≤ g := ENNReal.toReal_nonneg
  set w := fun x => u.toFun x - integralAverage (euclideanBall (0 : Vec d) 1) u.toFun with hw
  have hwi : IntegrableOn w (euclideanBall (0 : Vec d) 1) volume :=
    (memLp_centered u).integrable (by norm_num)
  have hzero := integral_sub_average (integrableOn_ball u) hBpos.ne' hBtop
  have hdiff := setIntegral_sdiff₀ (μ := volume) (f := w) hE.nullMeasurableSet hwi hEB
  have hDm : MeasurableSet (euclideanBall (0 : Vec d) 1 \ E) := hBm.diff hE
  have hDt : volume (euclideanBall (0 : Vec d) 1 \ E) ≠ ⊤ :=
    ne_top_of_le_ne_top hBtop (measure_mono Set.sdiff_subset)
  have hML2 : MemLp w (ENNReal.ofReal 2) (volume.restrict (euclideanBall (0 : Vec d) 1)) := by
    simpa only [ENNReal.ofReal_ofNat] using memLp_centered u
  have hH := setIntegral_abs_le hDm Set.sdiff_subset hDt (by norm_num : (1 : ℝ) ≤ 2) hML2
  have hN : (eLpNorm w (ENNReal.ofReal 2) (volume.restrict (euclideanBall (0 : Vec d) 1))).toReal ≤
      (2 : ℝ) ^ d * 2 * g := by
    simpa only [ENNReal.ofReal_ofNat] using toReal_eLpNorm_centered_le u
  have hDvol : (volume (euclideanBall (0 : Vec d) 1 \ E)).toReal ≤ (1 - θ) * V := by
    rw [measure_sdiff hEB hE.nullMeasurableSet hEt, ENNReal.toReal_sub_of_le
      (measure_mono hEB) hBtop]
    linarith
  have hDvol0 : 0 ≤ (volume (euclideanBall (0 : Vec d) 1 \ E)).toReal := ENNReal.toReal_nonneg
  have hΔ := avg_sub_avg hEB (integrableOn_ball u) hE0 hEt
  have hΔ' : |integralAverage (euclideanBall (0 : Vec d) 1) u.toFun - integralAverage E u.toFun| =
      (volume E).toReal⁻¹ * |∫ x in E, w x| := by
    rw [abs_sub_comm, hΔ, abs_mul, abs_of_pos (inv_pos.2 hEpos)]
  have hint : |∫ x in E, w x| ≤ ((1 - θ) * V) ^ (1 / (2 : ℝ)) * ((2 : ℝ) ^ d * 2 * g) := by
    have hI : ∫ x in E, w x = -∫ x in (euclideanBall (0 : Vec d) 1 \ E), w x := by
      rw [hdiff]; simp only [hw] at hzero ⊢; linarith
    rw [hI, abs_neg]
    have h2 : |∫ x in (euclideanBall (0 : Vec d) 1 \ E), w x| ≤
        ∫ x in (euclideanBall (0 : Vec d) 1 \ E), |w x| := by
      simpa using abs_integral_le_integral_abs (μ := volume.restrict (euclideanBall (0 : Vec d) 1 \ E))
        (f := w)
    have hexp : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    rw [hexp] at hH
    refine h2.trans (hH.trans ?_)
    have hpw : (volume (euclideanBall (0 : Vec d) 1 \ E)).toReal ^ (1 / (2 : ℝ)) ≤
        ((1 - θ) * V) ^ (1 / (2 : ℝ)) := Real.rpow_le_rpow hDvol0 hDvol (by norm_num)
    exact mul_le_mul hpw hN ENNReal.toReal_nonneg (by positivity)
  have hlog : 1 - θ ≤ |Real.log θ| := by
    have h1 := Real.log_le_sub_one_of_pos hθ0
    have h2 : Real.log θ < 0 := Real.log_neg hθ0 hθ1
    rw [abs_of_neg h2]; linarith
  have hsq1 : Real.sqrt (1 - θ) ≤ Real.sqrt |Real.log θ| := Real.sqrt_le_sqrt hlog
  have hs : 0 < Real.sqrt V := Real.sqrt_pos.2 hVpos
  have hss : Real.sqrt V * Real.sqrt V = V := Real.mul_self_sqrt hVpos.le
  have hrp : ((1 - θ) * V) ^ (1 / (2 : ℝ)) = Real.sqrt (1 - θ) * Real.sqrt V := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by linarith)]
  have hVrp : V ^ (1 / (2 : ℝ)) = Real.sqrt V := by rw [← Real.sqrt_eq_rpow]
  rw [hrp] at hint
  rw [hΔ', hVrp]
  have hEinv : (volume E).toReal⁻¹ ≤ 2 / V := by
    rw [inv_le_comm₀ hEpos (by positivity), inv_div]
    nlinarith
  generalize Real.sqrt V = s at hs hss hint ⊢
  calc (volume E).toReal⁻¹ * |∫ x in E, w x|
      ≤ (2 / V) * (Real.sqrt (1 - θ) * s * ((2 : ℝ) ^ d * 2 * g)) := by
        exact mul_le_mul hEinv hint (abs_nonneg _) (by positivity)
    _ = 2 * ((2 : ℝ) ^ d * 2) * s⁻¹ * Real.sqrt (1 - θ) * g := by
        rw [← hss]; field_simp
    _ ≤ 2 * ((2 : ℝ) ^ d * 2) * s⁻¹ * Real.sqrt |Real.log θ| * g := by
        have : 0 ≤ 2 * ((2 : ℝ) ^ d * 2) * s⁻¹ * g := by positivity
        nlinarith

end PDE.PoincareAdjustMean
