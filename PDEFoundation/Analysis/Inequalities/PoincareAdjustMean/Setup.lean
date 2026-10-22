module

public import PDEFoundation.Analysis.Inequalities.PoincareAdjustMean.Basic
public import PDEFoundation.Sobolev.Inequalities.ConvexPoincareL2
public import PDEFoundation.Measure.LpPower

/-!
# Unit-ball setup for the Poincaré inequality with an adjusted mean

Membership of the centered function in `L²(B₁)`, and the `L²` Poincaré bound
`‖u - (u)_B‖_{L²(B)} ≤ 2^{d+1} ‖∇u‖_{L²(B)}` in real form.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.PoincareAdjustMean

open MeasureTheory

variable {d : ℕ}

theorem ball_isOpenBoundedConvexDomain (d : ℕ) :
    IsOpenBoundedConvexDomain (euclideanBall (0 : Vec d) 1) :=
  isOpenBoundedConvexDomain_euclideanBall 0 one_pos

instance ball_isFiniteMeasure (d : ℕ) :
    IsFiniteMeasure (volume.restrict (euclideanBall (0 : Vec d) 1)) :=
  (ball_isOpenBoundedConvexDomain d).isFiniteMeasure_volumeOn

theorem memLp_two (u : H1Function (euclideanBall (0 : Vec d) 1)) :
    MemLp u.toFun 2 (volume.restrict (euclideanBall (0 : Vec d) 1)) := u.memL2

theorem integrableOn_ball (u : H1Function (euclideanBall (0 : Vec d) 1)) :
    IntegrableOn u.toFun (euclideanBall (0 : Vec d) 1) volume :=
  (memLp_two u).integrable (by norm_num)

theorem memLp_centered (u : H1Function (euclideanBall (0 : Vec d) 1)) :
    MemLp (fun x => u.toFun x - integralAverage (euclideanBall (0 : Vec d) 1) u.toFun) 2
      (volume.restrict (euclideanBall (0 : Vec d) 1)) :=
  (memLp_two u).sub (memLp_const _)

theorem memLp_grad (u : H1Function (euclideanBall (0 : Vec d) 1)) :
    MemLp (fun x => vecEuclideanNorm (u.grad x)) 2
      (volume.restrict (euclideanBall (0 : Vec d) 1)) :=
  u.gradMemL2.memLp_vecEuclideanNorm

/-- The real `L²` Poincaré inequality on the unit ball for the centered function. -/
theorem toReal_eLpNorm_centered_le (u : H1Function (euclideanBall (0 : Vec d) 1)) :
    (eLpNorm (fun x => u.toFun x - integralAverage (euclideanBall (0 : Vec d) 1) u.toFun) 2
        (volume.restrict (euclideanBall (0 : Vec d) 1))).toReal ≤
      (2 : ℝ) ^ d * 2 *
        (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2
          (volume.restrict (euclideanBall (0 : Vec d) 1))).toReal := by
  have hP := centeredPoincare_sq_on_boundedConvexDomain (ball_isOpenBoundedConvexDomain d)
    (hasEuclideanDiameterLE_euclideanBall 0 one_pos) (by norm_num)
    (euclideanBall_nonempty 0 one_pos) u
  have h1 := toReal_eLpNorm_two_sq_eq_integral_sq (memLp_centered u)
  have h2 := toReal_eLpNorm_two_sq_eq_integral_sq (memLp_grad u)
  simp only [vecEuclideanNorm_sq] at h2
  have hsq : (eLpNorm (fun x => u.toFun x - integralAverage (euclideanBall (0 : Vec d) 1) u.toFun) 2
        (volume.restrict (euclideanBall (0 : Vec d) 1))).toReal ^ 2 ≤
      ((2 : ℝ) ^ d * 2 * (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2
          (volume.restrict (euclideanBall (0 : Vec d) 1))).toReal) ^ 2 := by
    rw [h1, mul_pow, h2]
    simpa [mul_comm] using hP
  exact le_of_sq_le_sq hsq (by positivity)

end PDE.PoincareAdjustMean
