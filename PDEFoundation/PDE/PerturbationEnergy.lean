module

public import PDEFoundation.PDE.PerturbativeTesting
public import PDEFoundation.Sobolev.H1.VectorL2Bounds
public import PDEFoundation.Sobolev.H1.MeanEnergy

/-!
# Energy of the harmonic replacement error

Testing the actual equation with its zero-boundary replacement error gives
the Euclidean `L²` estimate with coefficient `delta`. The identity matrix
term is isolated using harmonic orthogonality, so no coercivity loss occurs.
-/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

/-- The harmonic replacement error obeys the sharp perturbative energy bound.
The orthogonality is the one supplied by Dirichlet harmonic replacement. -/
theorem sqrt_setIntegral_vecNormSq_replacement_error_le
    {a : CoeffField d} {delta : ℝ} (hdelta : 0 ≤ delta)
    {u : H1Function U} {F : Vec d → Vec d}
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hclose : ∀ᵐ x ∂volumeOn U, IsMatrixPerturbationLE delta (a x) 1)
    (hF : MemVectorL2On U F)
    (hsol : IsWeakDivergenceFormSolutionOn a U u 0 F)
    (w : H10Function U)
    (horth : ∫ x in U,
      vecDot (u.grad x - w.toH1Function.grad x) (w.toH1Function.grad x) = 0) :
    Real.sqrt (∫ x in U, vecNormSq (w.toH1Function.grad x)) ≤
      delta * Real.sqrt (∫ x in U, vecNormSq (u.grad x)) +
        Real.sqrt (∫ x in U, vecNormSq (F x)) := by
  have hid := setIntegral_vecNormSq_grad_eq_neg_perturbation_pairings
    ha hclose hF hsol w horth
  have hpert := abs_setIntegral_vecDot_le_mul_of_ae_vecEuclideanNorm_le
    u.gradMemL2
    (memVectorL2On_matVecMul_sub_identity_of_isMatrixPerturbationLE
      ha hclose u.gradMemL2)
    w.toH1Function.gradMemL2 hdelta
    (ae_vecEuclideanNorm_matVecMul_sub_identity_le_of_isMatrixPerturbationLE hclose)
  have hpair : (∫ x in U,
      vecDot (w.toH1Function.grad x) (matVecMul (a x - 1) (u.grad x))) =
      ∫ x in U, vecDot (matVecMul (a x - 1) (u.grad x))
        (w.toH1Function.grad x) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => vecDot_comm _ _
  rw [hpair] at hpert
  have hforce := abs_setIntegral_vecDot_le_sqrt_setIntegral_vecNormSq_mul
    hF w.toH1Function.gradMemL2
  have henergy : (∫ x in U, vecNormSq (w.toH1Function.grad x)) ≤
      (delta * Real.sqrt (∫ x in U, vecNormSq (u.grad x)) +
        Real.sqrt (∫ x in U, vecNormSq (F x))) *
          Real.sqrt (∫ x in U, vecNormSq (w.toH1Function.grad x)) := by
    have hnegpert := neg_le_abs (∫ x in U,
      vecDot (matVecMul (a x - 1) (u.grad x)) (w.toH1Function.grad x))
    have hnegforce := neg_le_abs (∫ x in U,
      vecDot (F x) (w.toH1Function.grad x))
    calc
      _ = -(∫ x in U, vecDot (matVecMul (a x - 1) (u.grad x))
          (w.toH1Function.grad x)) -
          ∫ x in U, vecDot (F x) (w.toH1Function.grad x) := hid
      _ ≤ _ := by nlinarith only [hpert, hforce, hnegpert, hnegforce]
  have hsquare := Real.sq_sqrt (x := ∫ x in U, vecNormSq (w.toH1Function.grad x))
    (integral_nonneg fun x =>
    vecNormSq_nonneg (w.toH1Function.grad x))
  have hnonneg : 0 ≤ delta * Real.sqrt (∫ x in U, vecNormSq (u.grad x)) +
      Real.sqrt (∫ x in U, vecNormSq (F x)) := by positivity
  have hwpos := Real.sqrt_nonneg (∫ x in U, vecNormSq (w.toH1Function.grad x))
  nlinarith only [henergy, hsquare, hnonneg, hwpos]

/-- The same replacement bound in normalized mean energy. -/
theorem sqrt_integralAverage_vecNormSq_replacement_error_le
    {a : CoeffField d} {delta : ℝ} (hdelta : 0 ≤ delta)
    {u : H1Function U} {F : Vec d → Vec d}
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hclose : ∀ᵐ x ∂volumeOn U, IsMatrixPerturbationLE delta (a x) 1)
    (hF : MemVectorL2On U F)
    (hsol : IsWeakDivergenceFormSolutionOn a U u 0 F)
    (w : H10Function U)
    (horth : ∫ x in U,
      vecDot (u.grad x - w.toH1Function.grad x) (w.toH1Function.grad x) = 0) :
    Real.sqrt (integralAverage U (fun x => vecNormSq (w.toH1Function.grad x))) ≤
      delta * Real.sqrt (integralAverage U (fun x => vecNormSq (u.grad x))) +
        Real.sqrt (integralAverage U (fun x => vecNormSq (F x))) := by
  simp only [sqrt_integralAverage_vecNormSq_eq]
  have h := div_le_div_of_nonneg_right
    (sqrt_setIntegral_vecNormSq_replacement_error_le hdelta ha hclose hF hsol w horth)
    (Real.sqrt_nonneg (volume U).toReal)
  simpa only [add_div, mul_div_assoc] using h

end

end PDE
