module

public import PDEFoundation.PDE.HarmonicReplacement
public import PDEFoundation.PDE.PerturbativeTesting
public import PDEFoundation.Sobolev.H1.ClosedGradientDirichletOperator

@[expose] public section

open scoped ENNReal RealInnerProductSpace

namespace PDE

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The canonical zero-boundary solution-gradient operator on a native round
ball for coefficients close to the identity. -/
def ballDirichletGradientCLM
    (hd : 0 < d) (z : Vec d) (R : ℝ) (hR : 0 < R)
    (a : CoeffField d) (delta : ℝ)
    (hdelta : 0 ≤ delta) (hdeltaOne : delta < 1)
    (ha : ∀ i j, AEMeasurable
      (fun x => a x i j) (volumeOn (euclideanBall z R)))
    (hclose : ∀ᵐ x ∂volumeOn (euclideanBall z R),
      IsMatrixPerturbationLE delta (a x) (1 : Mat d)) :
    HilbertVectorLp (euclideanBall z R) (2 : ℝ≥0∞) →L[ℝ]
      HilbertVectorLp (euclideanBall z R) (2 : ℝ≥0∞) :=
  closedGradientDirichletOperator (isOpen_euclideanBall z R) (2 * R)
    (h10Graph_value_norm_le_two_mul_radius_gradient_norm hd hR)
    a delta hdelta hdeltaOne ha hclose

theorem ballDirichletGradientCLM_mem_range
    (hd : 0 < d) (z : Vec d) (R : ℝ) (hR : 0 < R)
    (a : CoeffField d) (delta : ℝ)
    (hdelta : 0 ≤ delta) (hdeltaOne : delta < 1)
    (ha : ∀ i j, AEMeasurable
      (fun x => a x i j) (volumeOn (euclideanBall z R)))
    (hclose : ∀ᵐ x ∂volumeOn (euclideanBall z R),
      IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (F : HilbertVectorLp (euclideanBall z R) (2 : ℝ≥0∞)) :
    ballDirichletGradientCLM hd z R hR a delta hdelta hdeltaOne ha hclose F ∈
      closedGradientSubspace (isOpen_euclideanBall z R) :=
  closedGradientDirichletOperator_mem_range (isOpen_euclideanBall z R) (2 * R)
    (h10Graph_value_norm_le_two_mul_radius_gradient_norm hd hR)
    a delta hdelta hdeltaOne ha hclose F

theorem norm_ballDirichletGradientCLM_le
    (hd : 0 < d) (z : Vec d) (R : ℝ) (hR : 0 < R)
    (a : CoeffField d) (delta : ℝ)
    (hdelta : 0 ≤ delta) (hdeltaOne : delta < 1)
    (ha : ∀ i j, AEMeasurable
      (fun x => a x i j) (volumeOn (euclideanBall z R)))
    (hclose : ∀ᵐ x ∂volumeOn (euclideanBall z R),
      IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (F : HilbertVectorLp (euclideanBall z R) (2 : ℝ≥0∞)) :
    ‖ballDirichletGradientCLM hd z R hR a delta hdelta hdeltaOne ha hclose F‖ ≤
      (1 - delta)⁻¹ * ‖F‖ :=
  norm_closedGradientDirichletOperator_le (isOpen_euclideanBall z R) (2 * R)
    (h10Graph_value_norm_le_two_mul_radius_gradient_norm hd hR)
    a delta hdelta hdeltaOne ha hclose F

/-- The ball operator applied to native `L²` forcing has an actual
zero-boundary representative satisfying the safe all-`H¹₀` weak equation. -/
theorem exists_ballDirichletGradient_solution
    (hd : 0 < d) (z : Vec d) (R : ℝ) (hR : 0 < R)
    (a : CoeffField d) (delta : ℝ)
    (hdelta : 0 ≤ delta) (hdeltaOne : delta < 1)
    (ha : ∀ i j, AEMeasurable
      (fun x => a x i j) (volumeOn (euclideanBall z R)))
    (hclose : ∀ᵐ x ∂volumeOn (euclideanBall z R),
      IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (F : Vec d → Vec d) (hF : MemVectorL2On (euclideanBall z R) F) :
    ∃ w : H10Function (euclideanBall z R),
      h10GradientCLM (isOpen_euclideanBall z R)
          (w.toH10Graph (isOpen_euclideanBall z R)) =
        ballDirichletGradientCLM hd z R hR a delta hdelta hdeltaOne ha hclose
          hF.toHilbertVectorLp ∧
      IsWeakDivergenceFormH10SolutionOn a (euclideanBall z R)
        w.toH1Function 0 F := by
  let hU := isOpen_euclideanBall z R
  let TF := ballDirichletGradientCLM hd z R hR a delta hdelta hdeltaOne ha hclose
    hF.toHilbertVectorLp
  have hmem : TF ∈ closedGradientSubspace hU :=
    ballDirichletGradientCLM_mem_range hd z R hR a delta hdelta hdeltaOne ha hclose _
  obtain ⟨q, hq⟩ := hmem
  obtain ⟨w, hw⟩ := H10Graph.exists_toH10Function hU q
  have hwgrad : h10GradientCLM hU (w.toH10Graph hU) = TF := by
    rw [hw]
    exact hq
  refine ⟨w, hwgrad, ?_⟩
  intro φ
  let hflux : MemVectorL2On (euclideanBall z R)
      (fun x => matVecMul (a x) (w.toH1Function.grad x)) :=
    memVectorL2On_matVecMul_of_isMatrixPerturbationLE ha hclose
      w.toH1Function.gradMemL2
  refine ⟨{
    flux_integrable := integrableOn_vecDot_of_memVectorL2On hflux
      φ.toH1Function.gradMemL2
    source_integrable := by simp
    forcing_integrable := integrableOn_vecDot_of_memVectorL2On hF
      φ.toH1Function.gradMemL2 }, ?_⟩
  have hweak := closedGradientDirichletOperator_weak hU (2 * R)
    (h10Graph_value_norm_le_two_mul_radius_gradient_norm hd hR)
    a delta hdelta hdeltaOne ha hclose hF.toHilbertVectorLp (φ.toH10Graph hU)
  change inner ℝ
      (coefficientGradientActionCLM a delta hdelta ha hclose TF)
      (h10GradientCLM hU (φ.toH10Graph hU)) =
    -inner ℝ hF.toHilbertVectorLp
      (h10GradientCLM hU (φ.toH10Graph hU)) at hweak
  have hwclass : h10GradientCLM hU (w.toH10Graph hU) = TF := hwgrad
  have hwcoe : ⇑TF =ᵐ[volumeOn (euclideanBall z R)]
      toHilbertVecField w.toH1Function.grad := by
    rw [← hwclass]
    exact w.toH1Function.toW1pFunction.coeFn_toW1pGraph_snd
  have hφcoe : ⇑(h10GradientCLM hU (φ.toH10Graph hU))
      =ᵐ[volumeOn (euclideanBall z R)]
      toHilbertVecField φ.toH1Function.grad :=
    φ.toH1Function.toW1pFunction.coeFn_toW1pGraph_snd
  have hfluxcoe :
      ⇑(coefficientGradientActionCLM a delta hdelta ha hclose TF)
        =ᵐ[volumeOn (euclideanBall z R)]
      toHilbertVecField (fun x => matVecMul (a x) (w.toH1Function.grad x)) := by
    filter_upwards [coefficientGradientActionCLM_coeFn
      a delta hdelta ha hclose TF, hwcoe] with x hx hG
    rw [hx, hG]
    rfl
  have hleft := setIntegral_vecDot_eq_inner_of_ae_eq
    (coefficientGradientActionCLM a delta hdelta ha hclose TF)
    (h10GradientCLM hU (φ.toH10Graph hU))
    (fun x => matVecMul (a x) (w.toH1Function.grad x))
    φ.toH1Function.grad hfluxcoe hφcoe
  have hright := setIntegral_vecDot_eq_inner_of_ae_eq
    hF.toHilbertVectorLp (h10GradientCLM hU (φ.toH10Graph hU))
    F φ.toH1Function.grad hF.coeFn_toHilbertVectorLp hφcoe
  simp only [Pi.zero_apply, zero_mul, integral_zero, zero_sub]
  rw [hleft, hright]
  exact hweak

end

end PDE
