module

public import PDEFoundation.Measure.MatrixPerturbationLpConvergence
public import PDEFoundation.PDE.PerturbativeDirichletStability
public import PDEFoundation.Sobolev.H1.Algebra

/-! # Strong convergence of affine Dirichlet gradients -/

@[expose] public section

namespace PDE

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

/-- The quotient gradient norm is exactly the real Euclidean-magnitude seminorm. -/
theorem GradMemLpOn.norm_toHilbertVectorLp_eq_eLpNorm
    {d : ℕ} {U : Set (Vec d)} {p : ENNReal} {G : Vec d → Vec d}
    (hG : GradMemLpOn U p G) :
    ‖hG.toHilbertVectorLp‖ =
      (eLpNorm (fun x => vecEuclideanNorm (G x)) p (volumeOn U)).toReal := by
  unfold GradMemLpOn.toHilbertVectorLp
  rw [Lp.norm_toLp, eLpNorm_toHilbertVecField_eq (hF :=
    (aemeasurable_pi_iff.2 fun i => (hG i).aestronglyMeasurable.aemeasurable).aestronglyMeasurable)]

/-- Uniformly identity-close coefficients converging almost everywhere and
strongly convergent forcing give strong gradient convergence for actual weak
solutions with the same affine boundary datum. -/
theorem tendsto_eLpNorm_gradient_add_h10_sub_zero
    {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) (w : ℕ → H10Function U)
    (aSeq : ℕ → CoeffField d) (a : CoeffField d)
    (FSeq : ℕ → Vec d → Vec d) (F : Vec d → Vec d)
    {delta : ℝ} (hdelta : 0 ≤ delta) (hdeltaOne : delta < 1)
    (haSeq : ∀ n i j, AEMeasurable (fun x => aSeq n x i j) (volumeOn U))
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hcloseSeq : ∀ n, ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE delta (aSeq n x) (1 : Mat d))
    (hclose : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (hFSeq : ∀ n, MemVectorL2On U (FSeq n)) (hF : MemVectorL2On U F)
    (hsolSeq : ∀ n, IsWeakDivergenceFormSolutionOn (aSeq n) U
      (u + (w n).toH1Function) 0 (FSeq n))
    (hsol : IsWeakDivergenceFormSolutionOn a U u 0 F)
    (haConv : ∀ i j, ∀ᵐ x ∂volumeOn U,
      Tendsto (fun n => aSeq n x i j) atTop (𝓝 (a x i j)))
    (hFConv : Tendsto (fun n => eLpNorm
      (fun x => vecEuclideanNorm (FSeq n x - F x)) 2 (volumeOn U))
      atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm
      (fun x => vecEuclideanNorm
        ((u + (w n).toH1Function).grad x - u.grad x))
      2 (volumeOn U)) atTop (𝓝 0) := by
  have hCoeffConv := tendsto_eLpNorm_matrix_sub_mulVec_zero_of_ae
    u.gradMemL2 hdelta haSeq ha hcloseSeq hclose haConv
  have hFReal : Tendsto (fun n =>
      ‖(vectorDifferenceMemL2 (FSeq n) F (hFSeq n) hF).toHilbertVectorLp‖)
      atTop (𝓝 0) := by
    simpa only [GradMemLpOn.norm_toHilbertVectorLp_eq_eLpNorm,
      ENNReal.toReal_zero] using!
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hFConv
  have hCoeffReal : Tendsto (fun n =>
      ‖(coefficientDifferenceGradientMemL2OfNonneg (aSeq n) a delta delta
        hdelta hdelta (haSeq n) ha (hcloseSeq n) hclose u).toHilbertVectorLp‖)
      atTop (𝓝 0) := by
    simpa only [GradMemLpOn.norm_toHilbertVectorLp_eq_eLpNorm,
      ENNReal.toReal_zero] using!
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hCoeffConv
  have hbound (n : ℕ) := norm_gradient_sub_le_perturbative_data
    (aSeq n) a delta delta hdelta hdeltaOne hdelta
    (haSeq n) ha (hcloseSeq n) hclose (FSeq n) F (hFSeq n) hF
    (u + (w n).toH1Function) u (hsolSeq n) hsol (w n)
    (by simp only [add_sub_cancel_left])
  have hNormConv : Tendsto
      (fun n => ‖(w n).toH1Function.gradMemL2.toHilbertVectorLp‖)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun n => norm_nonneg _) hbound
    simpa only [add_zero, mul_zero] using
      (hFReal.add hCoeffReal).const_mul ((1 - delta)⁻¹)
  simp only [H1Function.add_grad, add_sub_cancel_left]
  have hfinite (n : ℕ) :
      eLpNorm (fun x => vecEuclideanNorm ((w n).toH1Function.grad x))
        2 (volumeOn U) ≠ ∞ :=
    (w n).toH1Function.gradMemL2.memLp_vecEuclideanNorm.eLpNorm_ne_top
  apply (ENNReal.tendsto_toReal_zero_iff hfinite).mp
  simpa only [GradMemLpOn.norm_toHilbertVectorLp_eq_eLpNorm] using hNormConv

end

end PDE
