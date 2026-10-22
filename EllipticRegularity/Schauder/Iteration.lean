module

public import PDEFoundation.PDE.PerturbativeScale
public import PDEFoundation.Analysis.ForcedIteration
public import PDEFoundation.Analysis.SchauderArithmetic
public import PDEFoundation.Analysis.DyadicRadius

/-!
# Forced dyadic gradient iteration

This is the actual weak-equation iteration. A displayed scale bound on the
forcing is retained as a helper input and is discharged by the `L^p` forcing
estimate in the source-facing theorem.
-/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Dyadic gradient control for an actual weak solution, conditional only on
the displayed normalized forcing scale bound. -/
theorem schauder_dyadic_gradient_bound
    (hd : 0 < d) {z : Vec d} {R α delta M : ℝ}
    (hR : 0 < R) (hα0 : 0 < α) (hα1 : α < 1) (hdelta : 0 ≤ delta)
    (hsmall : delta ≤ (2 : ℝ) ^ (-3 - (d : ℝ) / 2) * (1 - α))
    (hM : 0 ≤ M) {a : CoeffField d}
    (u : H1Function (euclideanBall z R)) {F : Vec d → Vec d}
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall z R)))
    (hclose : ∀ᵐ x ∂volumeOn (euclideanBall z R), IsMatrixPerturbationLE delta (a x) 1)
    (hF : MemVectorL2On (euclideanBall z R) F)
    (hsol : IsWeakDivergenceFormSolutionOn a (euclideanBall z R) u 0 F)
    (hforce : ∀ n : ℕ, dyadicRadius R n ^ (1 - α) *
      Real.sqrt (integralAverage (euclideanBall z (dyadicRadius R n))
        (fun x => vecNormSq (F x))) ≤ M) :
    ∀ n : ℕ, dyadicRadius R n ^ (1 - α) *
      Real.sqrt (integralAverage (euclideanBall z (dyadicRadius R n))
        (fun x => vecNormSq (u.grad x))) ≤
      R ^ (1 - α) * Real.sqrt (integralAverage (euclideanBall z R)
        (fun x => vecNormSq (u.grad x))) +
        8 * ((2 : ℝ) ^ ((d : ℝ) / 2) * M) / (1 - α) := by
  let X : ℕ → ℝ := fun n => dyadicRadius R n ^ (1 - α) *
    Real.sqrt (integralAverage (euclideanBall z (dyadicRadius R n))
      (fun x => vecNormSq (u.grad x)))
  let D : ℝ := (2 : ℝ) ^ ((d : ℝ) / 2)
  have hXnonneg (n : ℕ) : 0 ≤ X n :=
    mul_nonneg (Real.rpow_nonneg (dyadicRadius_pos hR n).le _) (Real.sqrt_nonneg _)
  have hD : 0 ≤ D := Real.rpow_nonneg (by norm_num) _
  have hhalf : 0 ≤ (1 / 2 : ℝ) ^ (1 - α) := Real.rpow_nonneg (by norm_num) _
  have hhalf_le : (1 / 2 : ℝ) ^ (1 - α) ≤ 1 :=
    Real.rpow_le_one (by norm_num) (by norm_num) (by linarith)
  have hcontract := schauder_smallness_implies_contraction hα0 hα1 hsmall
  have hstep (n : ℕ) : X (n + 1) ≤ (1 - (1 - α) / 8) * X n + D * M := by
    let r := dyadicRadius R n
    have hr : 0 < r := dyadicRadius_pos hR n
    have hsub : euclideanBall z r ⊆ euclideanBall z R :=
      euclideanBall_mono hr.le (dyadicRadius_le hR.le n)
    let v := u.restrict (isOpen_euclideanBall z r) hsub
    have hclose' := ae_restrict_of_ae_restrict_of_subset hsub hclose
    have ha' (i j : Fin d) : AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall z r)) :=
      (ha i j).mono_measure (Measure.restrict_mono hsub le_rfl)
    have hF' : MemVectorL2On (euclideanBall z r) F := fun i => memLpOn_mono hsub (hF i)
    have hs := sqrt_integralAverage_vecNormSq_grad_half_le hd hr hdelta v
      ha' hclose' hF' (hsol.restrict (isOpen_euclideanBall z R)
        (isOpen_euclideanBall z r) hsub)
    have hs' : X (n + 1) ≤
        (1 + 2 * delta * D) * (1 / 2 : ℝ) ^ (1 - α) * X n + D * M := by
      have hraw := mul_le_mul_of_nonneg_left hs
        (Real.rpow_nonneg (by positivity : 0 ≤ r / 2) (1 - α))
      have hforce' := mul_le_mul_of_nonneg_left (hforce n) hD
      have hXn : 0 ≤ X n := hXnonneg n
      have hcoef : (1 + delta * D) ≤ (1 + 2 * delta * D) := by
        nlinarith only [mul_nonneg hdelta hD]
      have hgrad' := mul_le_mul_of_nonneg_right hcoef
        (mul_nonneg hhalf hXn)
      have hforcing : (1 / 2 : ℝ) ^ (1 - α) * D *
          (r ^ (1 - α) * Real.sqrt (integralAverage (euclideanBall z r)
            (fun x => vecNormSq (F x)))) ≤ D * M := by
        calc
          _ ≤ D * (r ^ (1 - α) * Real.sqrt (integralAverage (euclideanBall z r)
              (fun x => vecNormSq (F x)))) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_of_le_one_left hD hhalf_le) (by positivity)
          _ ≤ _ := hforce'
      dsimp only [v] at hraw
      simp only [H1Function.restrict_grad] at hraw
      dsimp only [X]
      rw [show r / 2 = (1 / 2 : ℝ) * r by ring,
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2) hr.le] at hraw
      rw [dyadicRadius_succ]
      change (r / 2) ^ (1 - α) *
        Real.sqrt (integralAverage (euclideanBall z (r / 2))
          (fun x => vecNormSq (u.grad x))) ≤ _
      rw [show r / 2 = (1 / 2 : ℝ) * r by ring,
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2) hr.le]
      change (1 / 2 : ℝ) ^ (1 - α) * r ^ (1 - α) *
        Real.sqrt (integralAverage (euclideanBall z ((1 / 2 : ℝ) * r))
          (fun x => vecNormSq (u.grad x))) ≤ _ at hraw
      dsimp only [X] at hgrad'
      dsimp only [r] at hraw hforcing
      nlinarith only [hraw, hgrad', hforcing]
    exact hs'.trans (add_le_add
      (mul_le_mul_of_nonneg_right hcontract (hXnonneg n)) le_rfl)
  have hbound := forcedIteration_alpha_bound hα0 hα1 (mul_nonneg hD hM)
    (hXnonneg 0) hstep
  simpa only [X, D, dyadicRadius_zero] using hbound

end

end PDE
