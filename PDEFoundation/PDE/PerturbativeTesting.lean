module

public import PDEFoundation.PDE.PerturbationL2
public import PDEFoundation.PDE.WeakDivergenceForm
public import PDEFoundation.Sobolev.H1.Algebra

/-!
# Testing a perturbative equation against its harmonic replacement error

The smooth weak equation extends to genuine zero-boundary tests using the
proved `L²` flux bound. Harmonic orthogonality then identifies the squared
error energy with the coefficient-perturbation and forcing pairings.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

/-- Identity closeness supplies all data needed for the proved extension of
the smooth weak equation to zero-boundary Sobolev tests. -/
theorem IsWeakDivergenceFormSolutionOn.toH10SolutionOn_of_isMatrixPerturbationLE
    {a : CoeffField d} {delta : ℝ} {u : H1Function U} {F : Vec d → Vec d}
    (hsol : IsWeakDivergenceFormSolutionOn a U u 0 F)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hclose : ∀ᵐ x ∂volumeOn U, IsMatrixPerturbationLE delta (a x) 1)
    (hF : MemVectorL2On U F) : IsWeakDivergenceFormH10SolutionOn a U u 0 F := by
  let hL2 : IsWeakDivergenceFormL2SolutionOn a U u 0 F := {
    flux_memL2 := memVectorL2On_matVecMul_of_isMatrixPerturbationLE ha hclose u.gradMemL2
    source_memL2 := MeasureTheory.MemLp.zero
    forcing_memL2 := hF
    identity := fun φ => (hsol φ).2
  }
  exact hL2.toH10SolutionOn

private theorem vecDot_sub_left (x y z : Vec d) :
    vecDot (x - y) z = vecDot x z - vecDot y z := by
  simp only [vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private theorem matVecMul_sub_identity (A : Mat d) (x : Vec d) :
    matVecMul (A - 1) x = matVecMul A x - x := by
  classical
  change (A - 1).mulVec x = A.mulVec x - x
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]

/-- Exact replacement-error energy identity. Its orthogonality premise is
supplied by the constructed harmonic replacement, and its weak equation is
the actual all-`H¹₀` test identity. -/
theorem setIntegral_vecNormSq_grad_eq_neg_perturbation_pairings
    {a : CoeffField d} {delta : ℝ} {u : H1Function U} {F : Vec d → Vec d}
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hclose : ∀ᵐ x ∂volumeOn U, IsMatrixPerturbationLE delta (a x) 1)
    (hF : MemVectorL2On U F)
    (hsol : IsWeakDivergenceFormSolutionOn a U u 0 F)
    (w : H10Function U)
    (horth : ∫ x in U,
      vecDot (u.grad x - w.toH1Function.grad x) (w.toH1Function.grad x) = 0) :
    (∫ x in U, vecNormSq (w.toH1Function.grad x)) =
      -(∫ x in U,
        vecDot (matVecMul (a x - 1) (u.grad x)) (w.toH1Function.grad x)) -
      ∫ x in U, vecDot (F x) (w.toH1Function.grad x) := by
  have hflux := memVectorL2On_matVecMul_of_isMatrixPerturbationLE ha hclose u.gradMemL2
  have hfluxInt := integrableOn_vecDot_of_memVectorL2On hflux w.toH1Function.gradMemL2
  have huInt := integrableOn_vecDot_of_memVectorL2On u.gradMemL2 w.toH1Function.gradMemL2
  have hwInt := integrableOn_vecNormSq_of_memVectorL2On w.toH1Function.gradMemL2
  have hweak := (hsol.toH10SolutionOn_of_isMatrixPerturbationLE ha hclose hF w).2
  simp only [Pi.zero_apply, zero_mul, integral_zero, zero_sub] at hweak
  have horth' :
      (∫ x in U, vecDot (u.grad x) (w.toH1Function.grad x)) -
        (∫ x in U, vecNormSq (w.toH1Function.grad x)) = 0 := by
    simp only [vecDot_sub_left] at horth
    change (∫ x in U, vecDot (u.grad x) (w.toH1Function.grad x) -
      vecNormSq (w.toH1Function.grad x)) = 0 at horth
    rw [integral_sub huInt hwInt] at horth
    exact horth
  have hpert : (∫ x in U,
      vecDot (matVecMul (a x - 1) (u.grad x)) (w.toH1Function.grad x)) =
      (∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (w.toH1Function.grad x)) -
        ∫ x in U, vecDot (u.grad x) (w.toH1Function.grad x) := by
    simp only [matVecMul_sub_identity, vecDot_sub_left, integral_sub hfluxInt huInt]
  rw [hpert, hweak]
  linarith only [horth']

end

end PDE
