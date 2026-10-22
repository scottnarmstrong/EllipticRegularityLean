module

public import PDEFoundation.Analysis.Inequalities.PoincareAdjustMean.Setup

/-!
# Mean-difference bounds by Hölder's inequality
-/

@[expose] public section

open scoped ENNReal

namespace PDE.PoincareAdjustMean

open MeasureTheory

variable {d : ℕ}

/-- `|(u)_B - (u)_E| ≤ |E|^{-1/q} ‖u - (u)_B‖_{L^q(B)}` when the latter is finite. -/
theorem abs_avg_sub_avg_le (u : H1Function (euclideanBall (0 : Vec d) 1))
    {E : Set (Vec d)} (hE : MeasurableSet E) (hEB : E ⊆ euclideanBall (0 : Vec d) 1)
    (hE0 : volume E ≠ 0) (hEt : volume E ≠ ⊤) {q : ℝ} (hq : 1 ≤ q)
    (hML : MemLp (fun x => u.toFun x - integralAverage (euclideanBall (0 : Vec d) 1) u.toFun)
      (ENNReal.ofReal q) (volume.restrict (euclideanBall (0 : Vec d) 1))) :
    |integralAverage (euclideanBall (0 : Vec d) 1) u.toFun - integralAverage E u.toFun| ≤
      (volume E).toReal ^ (-(1 / q)) *
        (eLpNorm (fun x => u.toFun x - integralAverage (euclideanBall (0 : Vec d) 1) u.toFun)
          (ENNReal.ofReal q) (volume.restrict (euclideanBall (0 : Vec d) 1))).toReal := by
  have hEpos : 0 < (volume E).toReal := ENNReal.toReal_pos hE0 hEt
  rw [abs_sub_comm, avg_sub_avg hEB (integrableOn_ball u) hE0 hEt, abs_mul,
    abs_of_pos (inv_pos.2 hEpos)]
  have h1 := setIntegral_abs_le hE hEB hEt hq hML
  have h2 : |∫ x in E, (u.toFun x - integralAverage (euclideanBall (0 : Vec d) 1) u.toFun)| ≤
      ∫ x in E, |u.toFun x - integralAverage (euclideanBall (0 : Vec d) 1) u.toFun| := by
    simpa using abs_integral_le_integral_abs (μ := volume.restrict E)
      (f := fun x => u.toFun x - integralAverage (euclideanBall (0 : Vec d) 1) u.toFun)
  have hN : 0 ≤ (eLpNorm (fun x => u.toFun x - integralAverage (euclideanBall (0 : Vec d) 1) u.toFun)
      (ENNReal.ofReal q) (volume.restrict (euclideanBall (0 : Vec d) 1))).toReal := ENNReal.toReal_nonneg
  calc (volume E).toReal⁻¹ * |∫ x in E, (u.toFun x - integralAverage (euclideanBall (0 : Vec d) 1) u.toFun)|
      ≤ (volume E).toReal⁻¹ * ((volume E).toReal ^ (1 - 1 / q) *
          (eLpNorm (fun x => u.toFun x - integralAverage (euclideanBall (0 : Vec d) 1) u.toFun)
            (ENNReal.ofReal q) (volume.restrict (euclideanBall (0 : Vec d) 1))).toReal) := by
        gcongr; exact h2.trans h1
    _ = _ := by
        rw [← mul_assoc, ← Real.rpow_neg_one, ← Real.rpow_add hEpos]
        congr 2; ring

end PDE.PoincareAdjustMean
