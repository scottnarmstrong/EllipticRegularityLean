module

public import PDEFoundation.PDE.BallDirichletGradient
public import PDEFoundation.Sobolev.H1.Algebra

/-! # Affine Dirichlet solutions for perturbative coefficients -/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

/-- On the unit ball, solve the affine Dirichlet problem with boundary datum
represented by `u`. The correction belongs to `H¹₀`, and the resulting weak
solution is the literal sum `u + w`. -/
theorem exists_add_h10_isWeakDivergenceFormSolutionOn_unitBall
    {d : ℕ} (hd : 0 < d)
    (u : H1Function (euclideanBall (0 : Vec d) 1))
    (a : CoeffField d) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hdeltaOne : delta < 1)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec d) 1)))
    (hclose : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
      IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (F : Vec d → Vec d) (hF : MemVectorL2On (euclideanBall (0 : Vec d) 1) F) :
    ∃ w : H10Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1)
        (u + w.toH1Function) 0 F := by
  let U := euclideanBall (0 : Vec d) 1
  let Au : Vec d → Vec d := fun x => matVecMul (a x) (u.grad x)
  let H : Vec d → Vec d := fun x => F x + Au x
  have hAu : MemVectorL2On U Au :=
    memVectorL2On_matVecMul_of_isMatrixPerturbationLE ha hclose u.gradMemL2
  have hH : MemVectorL2On U H := fun i => (hF i).add (hAu i)
  obtain ⟨w, _hwgrad, hw⟩ := exists_ballDirichletGradient_solution
    hd (0 : Vec d) 1 (by norm_num) a delta hdelta hdeltaOne ha hclose H hH
  refine ⟨w, ?_⟩
  have hwSmooth : IsWeakDivergenceFormSolutionOn a U w.toH1Function 0 H :=
    hw.toIsWeakDivergenceFormSolutionOn (isOpen_euclideanBall _ _)
  intro φ
  let v : H1Function U := u + w.toH1Function
  have hav : MemVectorL2On U (fun x => matVecMul (a x) (v.grad x)) :=
    memVectorL2On_matVecMul_of_isMatrixPerturbationLE ha hclose v.gradMemL2
  let hdata : DivergenceFormL2DataOn a U v 0 F :=
    ⟨hav, MeasureTheory.MemLp.zero, hF⟩
  refine ⟨hdata.testable φ, ?_⟩
  have hAuInt := integrableOn_vecDot_weakTestFunction_grad hAu φ
  have hawInt := integrableOn_vecDot_weakTestFunction_grad
    (memVectorL2On_matVecMul_of_isMatrixPerturbationLE ha hclose
      w.toH1Function.gradMemL2) φ
  have hFInt := integrableOn_vecDot_weakTestFunction_grad hF φ
  have hleft : (∫ x in U,
      vecDot (matVecMul (a x) (v.grad x)) (φ.grad x)) =
      (∫ x in U, vecDot (Au x) (φ.grad x)) +
        ∫ x in U,
          vecDot (matVecMul (a x) (w.toH1Function.grad x)) (φ.grad x) := by
    rw [← integral_add hAuInt hawInt]
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [v, Au]
    rw [H1Function.add_grad]
    classical
    change vecDot ((a x).mulVec (u.grad x + w.toH1Function.grad x))
      (φ.grad x) = _
    rw [Matrix.mulVec_add]
    change (∑ i, ((a x).mulVec (u.grad x) i +
      (a x).mulVec (w.toH1Function.grad x) i) * φ.grad x i) = _
    simp only [vecDot, add_mul, Finset.sum_add_distrib, matVecMul,
      Matrix.mulVec, dotProduct]
  have hright : (∫ x in U, vecDot (H x) (φ.grad x)) =
      (∫ x in U, vecDot (F x) (φ.grad x)) +
        ∫ x in U, vecDot (Au x) (φ.grad x) := by
    rw [← integral_add hFInt hAuInt]
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [H]
    simp only [vecDot, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hwIdentity := (hwSmooth φ).2
  simp only [Pi.zero_apply, zero_mul, integral_zero, zero_sub] at hwIdentity ⊢
  change (∫ x in U, vecDot (matVecMul (a x) (v.grad x)) (φ.grad x)) = _
  rw [hleft, hright] at *
  linarith

end

end PDE
