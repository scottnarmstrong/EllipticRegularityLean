module

public import PDEFoundation.PDE.HarmonicComparisonMaximal
public import PDEFoundation.PDE.WeakForcingCongruence

/-! # Retained harmonic comparison with literal zero extension -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

/-- The literal zero extension agrees with the original field almost
everywhere on the positive-radius equation ball. -/
theorem euclideanBall_indicator_ae_eq_forcing
    {d : ℕ} (F : Vec d → Vec d) (z : Vec d) (R : ℝ) :
    F =ᵐ[volumeOn (euclideanBall z R)] (euclideanBall z R).indicator F := by
  filter_upwards [ae_restrict_mem (isOpen_euclideanBall z R).measurableSet] with x hx
  exact (Set.indicator_of_mem hx F).symm

/-- The harmonic comparison with exactly the zero extension appearing in
the manuscript, and with the exact dimension-dependent constant. -/
theorem centeredVectorMeanL2_weakLaplacian_retained_excess_zeroExtension
    {d : ℕ} (hd : 0 < d) {z : Vec d} {R : ℝ} (hR : 0 < R)
    (u : H1Function (euclideanBall z R)) {F : Vec d → Vec d}
    (hF : MemVectorL2On (euclideanBall z R) F)
    (hsol : IsWeakDivergenceFormSolutionOn (fun _ => (1 : Mat d))
      (euclideanBall z R) u 0 F)
    {r : ℝ} (hr : 0 < r) (hrR : r ≤ R) {x : Vec d} (hx : x ∈ euclideanBall z r) :
    ENNReal.ofReal (centeredVectorMeanL2 (euclideanBall z r) u.grad) ≤
      ENNReal.ofReal ((r / R) * centeredVectorMeanL2 (euclideanBall z R) u.grad) +
        ENNReal.ofReal (((d : ℝ) + 2) / 2 * (1 + 2 / (d : ℝ)) ^ ((d : ℝ) / 2)) *
          quadraticBallMaximal ((euclideanBall z R).indicator F) x := by
  have heq := euclideanBall_indicator_ae_eq_forcing F z R
  have hFzero : MemVectorL2On (euclideanBall z R) ((euclideanBall z R).indicator F) := by
    intro i
    have hcoord : (fun y => F y i) =ᵐ[volumeOn (euclideanBall z R)]
        fun y => ((euclideanBall z R).indicator F) y i := by
      filter_upwards [heq] with y hy
      exact congrFun hy i
    exact MemLp.ae_eq hcoord (hF i)
  exact centeredVectorMeanL2_weakLaplacian_retained_excess
    hd hR u hFzero (hsol.of_ae_eq_forcing heq) hr hrR hx

end PDE
