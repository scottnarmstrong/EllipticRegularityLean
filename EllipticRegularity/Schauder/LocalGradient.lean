module

public import EllipticRegularity.Schauder.Iteration
public import PDEFoundation.Regularity.GradientScale

/-! # Local gradient control from a forcing scale bound -/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Read the actual perturbative dyadic estimate at every local radius. The
forcing scale premise of this internal helper is discharged from `Lᵖ` data
in the continuous-coefficient application. -/
theorem schauder_local_gradient_bound_of_forcing_scale
    (hd : 0 < d) {z : Vec d} {R α delta M : ℝ}
    (hR : 0 < R) (hα0 : 0 < α) (hα1 : α < 1) (hdelta : 0 ≤ delta)
    (hsmall : delta ≤ (2 : ℝ) ^ (-3 - (d : ℝ) / 2) * (1 - α))
    (hM : 0 ≤ M) {a : CoeffField d}
    (u : H1Function (euclideanBall z R)) {F : Vec d → Vec d}
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall z R)))
    (hclose : ∀ᵐ x ∂volumeOn (euclideanBall z R), IsMatrixPerturbationLE delta (a x) 1)
    (hF : MemVectorL2On (euclideanBall z R) F)
    (hsol : IsWeakDivergenceFormSolutionOn a (euclideanBall z R) u 0 F)
    (hforce : ∀ r : ℝ, 0 < r → r ≤ R → r ^ (1 - α) *
      Real.sqrt (integralAverage (euclideanBall z r) (fun x => vecNormSq (F x))) ≤ M) :
    ∀ r : ℝ, 0 < r → r ≤ R → r ^ (1 - α) *
      Real.sqrt (integralAverage (euclideanBall z r) (fun x => vecNormSq (u.grad x))) ≤
      (2 : ℝ) ^ ((d : ℝ) / 2) *
        (R ^ (1 - α) * Real.sqrt (integralAverage (euclideanBall z R)
          (fun x => vecNormSq (u.grad x))) +
          8 * ((2 : ℝ) ^ ((d : ℝ) / 2) * M) / (1 - α)) := by
  have hdyadic := schauder_dyadic_gradient_bound hd hR hα0 hα1 hdelta hsmall
    hM u ha hclose hF hsol (fun n =>
      hforce _ (dyadicRadius_pos hR n) (dyadicRadius_le hR.le n))
  exact sqrt_integralAverage_vecNormSq_of_dyadic_scale_bound z hR hα1
    u.gradMemL2 hdyadic

end

end PDE
