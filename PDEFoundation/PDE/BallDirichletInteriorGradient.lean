module

public import PDEFoundation.Measure.LpMonoMeasure
public import PDEFoundation.PDE.BallDirichletGradient

/-! # The interior gradient of the actual ball Dirichlet solution -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Restrict the canonical ball Dirichlet gradient to the concentric half ball. -/
def ballDirichletInteriorGradientCLM
    {d : ℕ} (hd : 0 < d) (z : Vec d) (R : ℝ) (hR : 0 < R)
    (a : CoeffField d) (delta : ℝ)
    (hdelta : 0 ≤ delta) (hdeltaOne : delta < 1)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall z R)))
    (hclose : ∀ᵐ x ∂volumeOn (euclideanBall z R),
      IsMatrixPerturbationLE delta (a x) (1 : Mat d)) :
    HilbertVectorLp (euclideanBall z R) 2 →L[ℝ]
      HilbertVectorLp (euclideanBall z (R / 2)) 2 :=
  (lpMonoMeasure _ _ (Measure.restrict_mono
    (euclideanBall_mono (by linarith : 0 ≤ R / 2) (by linarith)) le_rfl)).comp
      (ballDirichletGradientCLM hd z R hR a delta hdelta hdeltaOne ha hclose)

/-- The interior solution-gradient map obeys the same coercive energy bound. -/
theorem norm_ballDirichletInteriorGradientCLM_le
    {d : ℕ} (hd : 0 < d) (z : Vec d) (R : ℝ) (hR : 0 < R)
    (a : CoeffField d) (delta : ℝ)
    (hdelta : 0 ≤ delta) (hdeltaOne : delta < 1)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall z R)))
    (hclose : ∀ᵐ x ∂volumeOn (euclideanBall z R),
      IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (F : HilbertVectorLp (euclideanBall z R) 2) :
    ‖ballDirichletInteriorGradientCLM hd z R hR a delta hdelta hdeltaOne ha hclose F‖ ≤
      (1 - delta)⁻¹ * ‖F‖ := by
  exact (norm_lpMonoMeasure_le
    (volumeOn (euclideanBall z R)) (volumeOn (euclideanBall z (R / 2)))
    (Measure.restrict_mono
      (euclideanBall_mono (by linarith : 0 ≤ R / 2) (by linarith)) le_rfl)
    (ballDirichletGradientCLM hd z R hR a delta hdelta hdeltaOne ha hclose F)).trans
    (norm_ballDirichletGradientCLM_le hd z R hR a delta hdelta hdeltaOne ha hclose F)

/-- The interior operator has a genuine zero-boundary weak solution whose
full gradient is the canonical ball output and whose interior gradient
represents the restricted output almost everywhere. -/
theorem exists_ballDirichletInteriorGradient_solution
    {d : ℕ} (hd : 0 < d) (z : Vec d) (R : ℝ) (hR : 0 < R)
    (a : CoeffField d) (delta : ℝ)
    (hdelta : 0 ≤ delta) (hdeltaOne : delta < 1)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall z R)))
    (hclose : ∀ᵐ x ∂volumeOn (euclideanBall z R),
      IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (F : Vec d → Vec d) (hF : MemVectorL2On (euclideanBall z R) F) :
    ∃ w : H10Function (euclideanBall z R),
      w.toH1Function.gradMemL2.toHilbertVectorLp =
        ballDirichletGradientCLM hd z R hR a delta hdelta hdeltaOne ha hclose
          hF.toHilbertVectorLp ∧
      (⇑(ballDirichletInteriorGradientCLM hd z R hR a delta hdelta hdeltaOne ha hclose
          hF.toHilbertVectorLp) =ᵐ[volumeOn (euclideanBall z (R / 2))]
        toHilbertVecField w.toH1Function.grad) ∧
      IsWeakDivergenceFormH10SolutionOn a (euclideanBall z R) w.toH1Function 0 F := by
  obtain ⟨w, hw, hsol⟩ := exists_ballDirichletGradient_solution
    hd z R hR a delta hdelta hdeltaOne ha hclose F hF
  have hnative : w.toH1Function.gradMemL2.toHilbertVectorLp =
      h10GradientCLM (isOpen_euclideanBall z R)
        (w.toH10Graph (isOpen_euclideanBall z R)) := by
    rfl
  have hclass := hnative.trans hw
  refine ⟨w, hclass, ?_, hsol⟩
  have hsub : euclideanBall z (R / 2) ⊆ euclideanBall z R :=
    euclideanBall_mono (by linarith) (by linarith)
  have hrestriction := coeFn_lpMonoMeasure_ae
    (volumeOn (euclideanBall z R)) (volumeOn (euclideanBall z (R / 2)))
    (Measure.restrict_mono hsub le_rfl)
    (ballDirichletGradientCLM hd z R hR a delta hdelta hdeltaOne ha hclose
      hF.toHilbertVectorLp)
  have hgradAE : ⇑(ballDirichletGradientCLM hd z R hR a delta hdelta hdeltaOne ha hclose
      hF.toHilbertVectorLp) =ᵐ[volumeOn (euclideanBall z (R / 2))]
      toHilbertVecField w.toH1Function.grad := by
    rw [← hclass]
    exact w.toH1Function.gradMemL2.coeFn_toHilbertVectorLp.filter_mono
      (ae_mono (Measure.restrict_mono hsub le_rfl))
  exact hrestriction.trans hgradAE

end

end PDE
