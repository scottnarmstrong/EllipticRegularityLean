module

public import PDEFoundation.PDE.BallDirichletGradient

@[expose] public section

open scoped ENNReal RealInnerProductSpace

namespace PDE

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Any safe weak solution with zero boundary values has the gradient selected
by the canonical ball Dirichlet operator. -/
theorem h10Gradient_eq_ballDirichletGradientCLM_of_weakSolution
    (hd : 0 < d) (z : Vec d) (R : ℝ) (hR : 0 < R)
    (a : CoeffField d) (delta : ℝ)
    (hdelta : 0 ≤ delta) (hdeltaOne : delta < 1)
    (ha : ∀ i j, AEMeasurable
      (fun x => a x i j) (volumeOn (euclideanBall z R)))
    (hclose : ∀ᵐ x ∂volumeOn (euclideanBall z R),
      IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (F : Vec d → Vec d) (hF : MemVectorL2On (euclideanBall z R) F)
    (w : H10Function (euclideanBall z R))
    (hsol : IsWeakDivergenceFormSolutionOn a (euclideanBall z R)
      w.toH1Function 0 F) :
    h10GradientCLM (isOpen_euclideanBall z R)
        (w.toH10Graph (isOpen_euclideanBall z R)) =
      ballDirichletGradientCLM hd z R hR a delta hdelta hdeltaOne ha hclose
        hF.toHilbertVectorLp := by
  let U := euclideanBall z R
  let hU := isOpen_euclideanBall z R
  let g : HilbertVectorLp U (2 : ℝ≥0∞) :=
    h10GradientCLM hU (w.toH10Graph hU)
  let T : HilbertVectorLp U (2 : ℝ≥0∞) :=
    ballDirichletGradientCLM hd z R hR a delta hdelta hdeltaOne ha hclose
      hF.toHilbertVectorLp
  let hflux : MemVectorL2On U
      (fun x => matVecMul (a x) (w.toH1Function.grad x)) :=
    memVectorL2On_matVecMul_of_isMatrixPerturbationLE ha hclose
      w.toH1Function.gradMemL2
  let hL2 : IsWeakDivergenceFormL2SolutionOn a U w.toH1Function 0 F := {
    flux_memL2 := hflux
    source_memL2 := MeasureTheory.MemLp.zero
    forcing_memL2 := hF
    identity := fun φ => (hsol φ).2 }
  have hH10 : IsWeakDivergenceFormH10SolutionOn a U w.toH1Function 0 F :=
    hL2.toH10SolutionOn
  have hgcoe : ⇑g =ᵐ[volumeOn U]
      toHilbertVecField w.toH1Function.grad :=
    w.toH1Function.toW1pFunction.coeFn_toW1pGraph_snd
  have hgmem : g ∈ closedGradientSubspace hU := by
    exact ⟨w.toH10Graph hU, rfl⟩
  have hTmem : T ∈ closedGradientSubspace hU :=
    ballDirichletGradientCLM_mem_range hd z R hR a delta hdelta hdeltaOne
      ha hclose hF.toHilbertVectorLp
  have hdiffmem : g - T ∈ closedGradientSubspace hU := sub_mem hgmem hTmem
  obtain ⟨q, hq⟩ := hdiffmem
  obtain ⟨φ, hφ⟩ := H10Graph.exists_toH10Function hU q
  have hqgrad : h10GradientCLM hU (φ.toH10Graph hU) = g - T := by
    rw [hφ]
    exact hq
  have hφcoe : ⇑(h10GradientCLM hU (φ.toH10Graph hU)) =ᵐ[volumeOn U]
      toHilbertVecField φ.toH1Function.grad :=
    φ.toH1Function.toW1pFunction.coeFn_toW1pGraph_snd
  have hagcoe :
      ⇑(coefficientGradientActionCLM a delta hdelta ha hclose g) =ᵐ[volumeOn U]
      toHilbertVecField
        (fun x => matVecMul (a x) (w.toH1Function.grad x)) := by
    filter_upwards [coefficientGradientActionCLM_coeFn
      a delta hdelta ha hclose g, hgcoe] with x hx hgx
    rw [hx, hgx]
    rfl
  have hleft := setIntegral_vecDot_eq_inner_of_ae_eq
    (coefficientGradientActionCLM a delta hdelta ha hclose g)
    (h10GradientCLM hU (φ.toH10Graph hU))
    (fun x => matVecMul (a x) (w.toH1Function.grad x))
    φ.toH1Function.grad hagcoe hφcoe
  have hright := setIntegral_vecDot_eq_inner_of_ae_eq
    hF.toHilbertVectorLp (h10GradientCLM hU (φ.toH10Graph hU))
    F φ.toH1Function.grad hF.coeFn_toHilbertVectorLp hφcoe
  have hwNative := (hH10 φ).2
  simp only [Pi.zero_apply, zero_mul, integral_zero, zero_sub] at hwNative
  have hwHilbert :
      inner ℝ (coefficientGradientActionCLM a delta hdelta ha hclose g)
          (g - T) = -inner ℝ hF.toHilbertVectorLp (g - T) := by
    rw [← hqgrad, ← hleft, ← hright]
    exact hwNative
  have hTHilbert := closedGradientDirichletOperator_weak hU (2 * R)
    (h10Graph_value_norm_le_two_mul_radius_gradient_norm hd hR)
    a delta hdelta hdeltaOne ha hclose hF.toHilbertVectorLp
      (φ.toH10Graph hU)
  change inner ℝ (coefficientGradientActionCLM a delta hdelta ha hclose T)
      (h10GradientCLM hU (φ.toH10Graph hU)) =
    -inner ℝ hF.toHilbertVectorLp
      (h10GradientCLM hU (φ.toH10Graph hU)) at hTHilbert
  rw [hqgrad] at hTHilbert
  have hzero : inner ℝ
      (coefficientGradientActionCLM a delta hdelta ha hclose (g - T))
      (g - T) = 0 := by
    rw [map_sub, inner_sub_left, hwHilbert, hTHilbert]
    ring
  have hcoercive := one_sub_mul_norm_sq_le_inner_coefficientGradientActionCLM
    a delta hdelta ha hclose (g - T)
  rw [hzero] at hcoercive
  have hnormzero : ‖g - T‖ = 0 := by
    have hpos : 0 < 1 - delta := sub_pos.mpr hdeltaOne
    have hprod : (1 - delta) * ‖g - T‖ ^ 2 = 0 :=
      le_antisymm hcoercive (mul_nonneg hpos.le (sq_nonneg _))
    have hsquare : ‖g - T‖ ^ 2 = 0 :=
      (mul_eq_zero.mp hprod).resolve_left hpos.ne'
    exact sq_eq_zero_iff.mp hsquare
  have : g = T := sub_eq_zero.mp (norm_eq_zero.mp hnormzero)
  exact this

end

end PDE
