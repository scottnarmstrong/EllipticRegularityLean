module

public import PDEFoundation.PDE.LaplacianOscillationStep
public import PDEFoundation.Analysis.RetainedExcessIteration

/-! # Retained excess under a uniform bound on concentric forcing averages -/

@[expose] public section

namespace PDE

open MeasureTheory

/-- A uniform forcing-average bound on the concentric balls gives retained
excess with no loss in the exact outer coefficient. The maximal function will
provide this bound in the harmonic comparison theorem. -/
theorem centeredVectorMeanL2_weakLaplacian_retained_of_forcing_bound
    {d : ℕ} (hd : 0 < d) {z : Vec d} {R : ℝ} (hR : 0 < R)
    (u : H1Function (euclideanBall z R)) {F : Vec d → Vec d}
    (hF : MemVectorL2On (euclideanBall z R) F)
    (hsol : IsWeakDivergenceFormSolutionOn (fun _ => (1 : Mat d))
      (euclideanBall z R) u 0 F)
    {M θ r : ℝ} (hM : 0 ≤ M) (hθ : 0 < θ) (hθone : θ < 1)
    (hbound : ∀ b : ℝ, 0 < b → b ≤ R →
      Real.sqrt (integralAverage (euclideanBall z b) (fun x => vecNormSq (F x))) ≤ M)
    (hr : 0 < r) (hrR : r ≤ R) :
    centeredVectorMeanL2 (euclideanBall z r) u.grad ≤
      (r / R) * centeredVectorMeanL2 (euclideanBall z R) u.grad +
        θ ^ (-(d : ℝ) / 2) * M / (1 - θ) := by
  apply retainedExcessIteration (fun b => centeredVectorMeanL2 (euclideanBall z b) u.grad)
    hR hr hrR hθ hθone (mul_nonneg (Real.rpow_nonneg hθ.le _) hM)
  intro a b ha hab hbR hθba
  have hb : 0 < b := ha.trans_le hab
  have hsub : euclideanBall z b ⊆ euclideanBall z R := euclideanBall_mono hb.le hbR
  let ub := u.restrict (isOpen_euclideanBall z b) hsub
  have hFb : MemVectorL2On (euclideanBall z b) F :=
    fun i => memLpOn_mono hsub (hF i)
  have hsolb := hsol.restrict (isOpen_euclideanBall z R) (isOpen_euclideanBall z b) hsub
  have hstep := centeredVectorMeanL2_weakLaplacian_grad_step hd hb ub hFb hsolb ha hab
  have hratio : b / a ≤ θ⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ hθ).2
    rw [div_mul_eq_mul_div]
    apply (div_le_one ha).2
    simpa only [mul_comm] using hθba
  have hfactor : (b / a) ^ ((d : ℝ) / 2) ≤ θ ^ (-(d : ℝ) / 2) := by
    calc
      (b / a) ^ ((d : ℝ) / 2) ≤ (θ⁻¹) ^ ((d : ℝ) / 2) :=
        Real.rpow_le_rpow (div_nonneg hb.le ha.le) hratio (by positivity)
      _ = θ ^ (-(d : ℝ) / 2) := by rw [← Real.rpow_neg_eq_inv_rpow, neg_div]
  have herror : (b / a) ^ ((d : ℝ) / 2) *
      Real.sqrt (integralAverage (euclideanBall z b) (fun x => vecNormSq (F x))) ≤
        θ ^ (-(d : ℝ) / 2) * M :=
    mul_le_mul hfactor (hbound b hb hbR) (Real.sqrt_nonneg _)
      (Real.rpow_nonneg hθ.le _)
  simpa only [ub, H1Function.restrict_grad] using
    hstep.trans (add_le_add le_rfl herror)

end PDE
