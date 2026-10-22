module

public import EllipticRegularity.CalderonZygmund.HolderGradientBoundedInterior
public import PDEFoundation.Ambient.MatrixPerturbationEllipticity
public import PDEFoundation.PDE.CalderonZygmundBoundedGradient
public import PDEFoundation.PDE.CoefficientForcingScale
public import PDEFoundation.Regularity.SmoothFieldHolder

/-! # Smooth high-exponent Calderón--Zygmund estimate -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped _root_.ENNReal

/-- For smooth coefficients and forcing, interior Schauder regularity supplies
and then discharges the temporary bounded-gradient hypothesis in the
high-exponent Calderón--Zygmund estimate. -/
theorem exists_calderonZygmund_smooth_highExponent_constants
    (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 1 ≤ C ∧
    ∀ (p : ℝ), 4 ≤ p →
    ∀ (a : CoeffField d) (F : Vec d → Vec d),
    (∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x i j)) →
    (∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => F x i)) →
    (∀ x ∈ euclideanBall (0 : Vec d) 1,
      IsMatrixPerturbationLE (1 / (C * p)) (a x) (1 : Mat d)) →
    ∀ (u : H1Function (euclideanBall (0 : Vec d) 1)),
    ∀ (hF : MemLp (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p)
      (volumeOn (euclideanBall (0 : Vec d) 1))),
    IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u 0 F →
    MemW1p (euclideanBall (0 : Vec d) (1 / 2)) (ENNReal.ofReal p) u.toFun ∧
    ∃ hgrad : MemLp (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
      (volumeOn (euclideanBall (0 : Vec d) (1 / 2))),
    euclideanFieldLpMeanNormOn (euclideanBall (0 : Vec d) (1 / 2))
      (ENNReal.ofReal p) u.grad
      (memLp_normalizedVolumeOn_of_memLpOn hgrad
        (volume_euclideanBall_pos (0 : Vec d) (by norm_num))) ≤
    C * (Real.sqrt (integralAverage (euclideanBall (0 : Vec d) 1)
      (fun x => vecNormSq (u.grad x))) +
      p * euclideanFieldLpMeanNormOn (euclideanBall (0 : Vec d) 1)
        (ENNReal.ofReal p) F
        (memLp_normalizedVolumeOn_of_memLpOn hF
          (volume_euclideanBall_pos (0 : Vec d) (by norm_num)))) := by
  obtain ⟨C, hC, hhigh⟩ := exists_calderonZygmund_boundedGradient_highExponent d hd
  refine ⟨C, hC, ?_⟩
  intro p hp a F ha hFsmooth hclose u hF hsol
  let delta : ℝ := 1 / (C * p)
  let c : ℝ := (1 - delta)⁻¹
  let an : CoeffField d := fun x => c • a x
  let Fn : Vec d → Vec d := fun x => c • F x
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hp0 : 0 < p := by linarith
  have hdelta0 : 0 ≤ delta := by dsimp only [delta]; positivity
  have hdeltahalf : delta ≤ 1 / 2 := by
    dsimp only [delta]
    apply (div_le_iff₀ (mul_pos hCpos hp0)).2
    nlinarith [mul_le_mul_of_nonneg_right hC hp0.le]
  have hell : ∀ x ∈ euclideanBall (0 : Vec d) 1,
      IsEllipticMatrix 1 9 (an x) := by
    intro x hx
    exact isEllipticMatrix_inv_one_sub_smul_of_isMatrixPerturbationLE
      hdelta0 hdeltahalf (hclose x hx)
  have hanSmooth : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => an x i j) := by
    intro i j
    simpa only [an, Pi.smul_apply, smul_eq_mul] using! (ha i j).const_smul c
  have hFnSmooth : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => Fn x i) := by
    intro i
    simpa only [Fn, Pi.smul_apply, smul_eq_mul] using (hFsmooth i).const_smul c
  have hanHolder := exists_euclideanMatrixHolderSeminormLE_half_of_contDiff hanSmooth
  have hFnHolder := exists_euclideanFieldHolderSeminormLE_half_of_contDiff hFnSmooth
  have hsoln : IsWeakDivergenceFormSolutionOn an
      (euclideanBall (0 : Vec d) 1) u 0 Fn := by
    simpa only [an, Fn, Pi.zero_apply, mul_zero] using!
      hsol.smul_coefficient_source_forcing c
  obtain ⟨_, M, hM, hgradBound⟩ :=
    memLp_top_vecEuclideanNorm_grad_three_fourths_ball_of_holder hd
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
      an Fn hell hanHolder hFnHolder u hsoln
  have haMeas : ∀ i j, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec d) 1)) := fun i j =>
    (ha i j).continuous.aemeasurable
  have hFMeas : ∀ i, AEStronglyMeasurable (fun x => F x i)
      (volumeOn (euclideanBall (0 : Vec d) 1)) := fun i =>
    (hFsmooth i).continuous.aestronglyMeasurable
  have hcloseAE : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
      IsMatrixPerturbationLE (1 / (C * p)) (a x) (1 : Mat d) := by
    filter_upwards [ae_restrict_mem (isOpen_euclideanBall _ _).measurableSet] with x hx
    exact hclose x hx
  exact hhigh p hp a haMeas hcloseAE u F hFMeas hF hsol M hM hgradBound

end PDE
