module

public import PDEFoundation.Analysis.Inequalities.PoincareAdjustMean.Holder

/-!
# Assembly of the two conclusions of the adjusted-mean Poincaré inequality

From the `L²` Poincaré bound for `w = u - (u)_B` and a bound on the difference of the means, the
`L²` estimate for `u - (u)_E` and the estimate for the difference of the means follow.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.PoincareAdjustMean

open MeasureTheory

variable {d : ℕ}

/-- Assembly: both conclusions from a mean-difference bound. -/
theorem assemble (u : H1Function (euclideanBall (0 : Vec d) 1)) {E : Set (Vec d)}
    {M f₂ f₁ : ℝ} (hM0 : 0 ≤ M) (hf₂ : 0 ≤ f₂) (hf₂₁ : f₂ ≤ f₁) (hf₁ : 1 ≤ f₁)
    (hΔ : |integralAverage (euclideanBall (0 : Vec d) 1) u.toFun - integralAverage E u.toFun| ≤
      M * f₂ * (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2
        (volume.restrict (euclideanBall (0 : Vec d) 1))).toReal) :
    eLpNorm (fun x => u.toFun x - integralAverage E u.toFun) 2
        (volume.restrict (euclideanBall (0 : Vec d) 1)) ≤
      ENNReal.ofReal (((2 : ℝ) ^ d * 2 + (volume (euclideanBall (0 : Vec d) 1)).toReal ^ (1 / (2 : ℝ)) * M) * f₁) *
        eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2
          (volume.restrict (euclideanBall (0 : Vec d) 1)) ∧
    ENNReal.ofReal |integralAverage (euclideanBall (0 : Vec d) 1) u.toFun - integralAverage E u.toFun| ≤
      ENNReal.ofReal (M * f₂) *
        eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2
          (volume.restrict (euclideanBall (0 : Vec d) 1)) := by
  set G := eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2 (volume.restrict (euclideanBall (0 : Vec d) 1)) with hG
  have hGfin : G ≠ ⊤ := (memLp_grad u).eLpNorm_ne_top
  have hGeq : G = ENNReal.ofReal G.toReal := (ENNReal.ofReal_toReal hGfin).symm
  set g := G.toReal with hg
  have hg0 : 0 ≤ g := ENNReal.toReal_nonneg
  set Δ := integralAverage (euclideanBall (0 : Vec d) 1) u.toFun - integralAverage E u.toFun with hΔdef
  have hf₂1 : 0 ≤ f₁ := by linarith
  constructor
  · -- L² estimate
    have hw := memLp_centered u
    have hwfin : eLpNorm (fun x => u.toFun x - integralAverage (euclideanBall (0 : Vec d) 1) u.toFun) 2 (volume.restrict (euclideanBall (0 : Vec d) 1)) ≠ ⊤ :=
      hw.eLpNorm_ne_top
    have hsplit : (fun x => u.toFun x - integralAverage E u.toFun) =
        (fun x => u.toFun x - integralAverage (euclideanBall (0 : Vec d) 1) u.toFun) + fun _ => Δ := by
      funext x; simp only [Pi.add_apply, hΔdef]; ring
    have hP := toReal_eLpNorm_centered_le u
    have hT : eLpNorm (fun x => u.toFun x - integralAverage E u.toFun) 2 (volume.restrict (euclideanBall (0 : Vec d) 1)) ≤
        eLpNorm (fun x => u.toFun x - integralAverage (euclideanBall (0 : Vec d) 1) u.toFun) 2 (volume.restrict (euclideanBall (0 : Vec d) 1)) +
          eLpNorm (fun _ : Vec d => Δ) 2 (volume.restrict (euclideanBall (0 : Vec d) 1)) := by
      rw [hsplit]
      exact eLpNorm_add_le (by norm_num)
    have hc : eLpNorm (fun _ : Vec d => Δ) 2 (volume.restrict (euclideanBall (0 : Vec d) 1)) =
        ENNReal.ofReal (|Δ| * (volume (euclideanBall (0 : Vec d) 1)).toReal ^ (1 / (2 : ℝ))) := by
      rw [eLpNorm_const _ (by norm_num) (by
        intro h
        have := congrArg (fun m => m Set.univ) h
        simp at this
        exact (volume_euclideanBall_pos (d := d) 0 one_pos).ne' this)]
      simp only [Measure.restrict_apply_univ, ENNReal.toReal_ofNat, Real.enorm_eq_ofReal_abs]
      rw [ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg
        (by norm_num), ENNReal.ofReal_toReal (volume_euclideanBall_ne_top 0 zero_le_one)]
    have hwe : eLpNorm (fun x => u.toFun x - integralAverage (euclideanBall (0 : Vec d) 1) u.toFun) 2 (volume.restrict (euclideanBall (0 : Vec d) 1)) ≤
        ENNReal.ofReal ((2 : ℝ) ^ d * 2 * g) := by
      rw [← ENNReal.ofReal_toReal hwfin]
      exact ENNReal.ofReal_le_ofReal hP
    have hω : 0 ≤ (volume (euclideanBall (0 : Vec d) 1)).toReal ^ (1 / (2 : ℝ)) := by positivity
    have hΔ' : |Δ| * (volume (euclideanBall (0 : Vec d) 1)).toReal ^ (1 / (2 : ℝ)) ≤
        (volume (euclideanBall (0 : Vec d) 1)).toReal ^ (1 / (2 : ℝ)) * M * f₂ * g := by
      have := mul_le_mul_of_nonneg_right hΔ hω
      linarith [mul_comm (M * f₂ * g) ((volume (euclideanBall (0 : Vec d) 1)).toReal ^ (1 / (2 : ℝ))), mul_assoc
        ((volume (euclideanBall (0 : Vec d) 1)).toReal ^ (1 / (2 : ℝ))) M f₂]
    calc _ ≤ _ := hT
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ d * 2 * g) +
          ENNReal.ofReal ((volume (euclideanBall (0 : Vec d) 1)).toReal ^ (1 / (2 : ℝ)) * M * f₂ * g) := by
        rw [hc]; exact add_le_add hwe (ENNReal.ofReal_le_ofReal hΔ')
      _ = ENNReal.ofReal ((2 : ℝ) ^ d * 2 * g + (volume (euclideanBall (0 : Vec d) 1)).toReal ^ (1 / (2 : ℝ)) * M * f₂ * g) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ ≤ ENNReal.ofReal (((2 : ℝ) ^ d * 2 + (volume (euclideanBall (0 : Vec d) 1)).toReal ^ (1 / (2 : ℝ)) * M) * f₁ * g) := by
        apply ENNReal.ofReal_le_ofReal
        have h1 : (2 : ℝ) ^ d * 2 * g ≤ (2 : ℝ) ^ d * 2 * f₁ * g := by
          have : (0 : ℝ) ≤ (2 : ℝ) ^ d * 2 * g := by positivity
          nlinarith
        have h2 : (volume (euclideanBall (0 : Vec d) 1)).toReal ^ (1 / (2 : ℝ)) * M * f₂ * g ≤
            (volume (euclideanBall (0 : Vec d) 1)).toReal ^ (1 / (2 : ℝ)) * M * f₁ * g := by
          have : 0 ≤ (volume (euclideanBall (0 : Vec d) 1)).toReal ^ (1 / (2 : ℝ)) * M * g := by positivity
          nlinarith
        nlinarith
      _ = _ := by
        rw [hGeq, ← ENNReal.ofReal_mul (by positivity)]
  · rw [hGeq, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hΔ

end PDE.PoincareAdjustMean
