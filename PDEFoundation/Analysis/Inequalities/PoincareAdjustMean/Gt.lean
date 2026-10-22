module

public import PDEFoundation.Analysis.Inequalities.PoincareAdjustMean.Assemble
public import PDEFoundation.Analysis.Inequalities.PoincareAdjustMean.Sobolev

/-!
# Poincaré inequality with an adjusted mean, `d ≥ 3` (unconditional)
-/

@[expose] public section

open scoped ENNReal

namespace PDE.PoincareAdjustMean

open MeasureTheory

/-- Mean-difference bound for `d ≥ 3`: constant times `θ^{(2-d)/(2d)} ‖∇u‖_{L²}`. -/
theorem exists_meanDiff_bound_gt (d : ℕ) (hd : 3 ≤ d) :
    ∃ M : ℝ, 0 < M ∧ ∀ θ : ℝ, 0 < θ → θ < 1 →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      ∀ E : Set (Vec d), MeasurableSet E → E ⊆ euclideanBall (0 : Vec d) 1 →
        ENNReal.ofReal θ * volume (euclideanBall (0 : Vec d) 1) ≤ volume E →
        |integralAverage (euclideanBall (0 : Vec d) 1) u.toFun - integralAverage E u.toFun| ≤
          M * θ ^ (((2 : ℝ) - d) / (2 * d)) *
            (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2
              (volume.restrict (euclideanBall (0 : Vec d) 1))).toReal := by
  obtain ⟨K, hK, hS⟩ := exists_sobolev_bound d hd
  have hpos : 0 < volume (euclideanBall (0 : Vec d) 1) := volume_euclideanBall_pos 0 one_pos
  have htop : volume (euclideanBall (0 : Vec d) 1) ≠ ⊤ := volume_euclideanBall_ne_top 0 zero_le_one
  set V : ℝ := (volume (euclideanBall (0 : Vec d) 1)).toReal with hV
  have hVpos : 0 < V := ENNReal.toReal_pos hpos.ne' htop
  have hdR : (2 : ℝ) < d := by exact_mod_cast (by omega : 2 < d)
  set q : ℝ := 2 * d / ((d : ℝ) - 2) with hq
  have hd2 : 0 < (d : ℝ) - 2 := by linarith
  have hq1 : 1 ≤ q := by
    rw [hq, le_div_iff₀ hd2]; linarith
  have hqexp : -(1 / q) = ((2 : ℝ) - d) / (2 * d) := by
    rw [hq]; field_simp; ring
  refine ⟨V ^ (-(1 / q)) * K, by positivity, fun θ hθ0 hθ1 u E hE hEB hθE => ?_⟩
  obtain ⟨hML, hbd⟩ := hS u
  have hE0 : volume E ≠ 0 := by
    intro h
    rw [h, nonpos_iff_eq_zero] at hθE
    rcases mul_eq_zero.1 hθE with h1 | h1
    · simp at h1; linarith
    · exact hpos.ne' h1
  have hEt : volume E ≠ ⊤ := ne_top_of_le_ne_top htop (measure_mono hEB)
  have hEV : θ * V ≤ (volume E).toReal := by
    have := ENNReal.toReal_mono hEt hθE
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hθ0.le] at this
  have h1 := abs_avg_sub_avg_le u hE hEB hE0 hEt hq1 hML
  have hEpos : 0 < (volume E).toReal := ENNReal.toReal_pos hE0 hEt
  have h2 : (volume E).toReal ^ (-(1 / q)) ≤ (θ * V) ^ (-(1 / q)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hEV (by
      have : 0 < 1 / q := by positivity
      linarith)
  rw [Real.mul_rpow hθ0.le hVpos.le] at h2
  rw [← hqexp]
  refine h1.trans ?_
  calc (volume E).toReal ^ (-(1 / q)) *
        (eLpNorm (fun x => u.toFun x - integralAverage (euclideanBall (0 : Vec d) 1) u.toFun)
          (ENNReal.ofReal q) (volume.restrict (euclideanBall (0 : Vec d) 1))).toReal
      ≤ (θ ^ (-(1 / q)) * V ^ (-(1 / q))) * (K * (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2
          (volume.restrict (euclideanBall (0 : Vec d) 1))).toReal) := by
        gcongr
    _ = _ := by ring

/-- The Poincaré inequality with an adjusted mean, `d ≥ 3` (unconditional). -/
theorem exists_poincare_adjustmean_constant_gt (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ : ℝ, 0 < θ → θ < 1 →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      ∀ E : Set (Vec d), MeasurableSet E → E ⊆ euclideanBall (0 : Vec d) 1 →
        ENNReal.ofReal θ * volume (euclideanBall (0 : Vec d) 1) ≤ volume E →
        eLpNorm (fun x => u.toFun x - integralAverage E u.toFun) 2
            (volumeOn (euclideanBall (0 : Vec d) 1)) ≤
          ENNReal.ofReal (C * (if d = 2 then Real.sqrt (1 + |Real.log θ|)
              else θ ^ (((2 : ℝ) - d) / (2 * d)))) *
            eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2
              (volumeOn (euclideanBall (0 : Vec d) 1)) ∧
        ENNReal.ofReal |integralAverage (euclideanBall (0 : Vec d) 1) u.toFun -
            integralAverage E u.toFun| ≤
          ENNReal.ofReal (C * (if d = 2 then Real.sqrt |Real.log θ|
              else θ ^ (((2 : ℝ) - d) / (2 * d)))) *
            eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2
              (volumeOn (euclideanBall (0 : Vec d) 1)) := by
  obtain ⟨M, hM, hbd⟩ := exists_meanDiff_bound_gt d hd
  have hd2 : d ≠ 2 := by omega
  set V : ℝ := (volume (euclideanBall (0 : Vec d) 1)).toReal with hV
  have hVpos : 0 < V := ENNReal.toReal_pos (volume_euclideanBall_pos 0 one_pos).ne'
    (volume_euclideanBall_ne_top 0 zero_le_one)
  refine ⟨(2 : ℝ) ^ d * 2 + V ^ (1 / (2 : ℝ)) * M + M, by positivity,
    fun θ hθ0 hθ1 u E hE hEB hθE => ?_⟩
  simp only [hd2, ite_false]
  have hf1 : 1 ≤ θ ^ (((2 : ℝ) - d) / (2 * d)) := by
    apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hθ0 hθ1.le
    have : (0 : ℝ) < d := by positivity
    have h2 : (2 : ℝ) - d ≤ 0 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast (by omega : 2 ≤ d)
      linarith
    exact div_nonpos_of_nonpos_of_nonneg h2 (by positivity)
  have hf0 : 0 ≤ θ ^ (((2 : ℝ) - d) / (2 * d)) := by linarith
  have hb := hbd θ hθ0 hθ1 u E hE hEB hθE
  obtain ⟨A1, A2⟩ := assemble u hM.le hf0 le_rfl hf1 hb
  set f := θ ^ (((2 : ℝ) - d) / (2 * d))
  set G := eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2
    (volume.restrict (euclideanBall (0 : Vec d) 1))
  have hVM : 0 ≤ V ^ (1 / (2 : ℝ)) * M := by positivity
  have h2d : (0 : ℝ) ≤ (2 : ℝ) ^ d * 2 := by positivity
  constructor
  · refine A1.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
    nlinarith
  · refine A2.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
    nlinarith

end PDE.PoincareAdjustMean
