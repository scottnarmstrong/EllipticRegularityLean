module

public import EllipticRegularity.CalderonZygmund.RoughHighExponent
public import PDEFoundation.Measure.MeanLpBoundTransport
public import PDEFoundation.PDE.BallDirichletInteriorGradient
public import EllipticRegularity.CalderonZygmund.DirichletEndpointBounds
public import PDEFoundation.Measure.FiniteVectorOperatorInterpolation

/-! # Interpolation for the actual zero-boundary Dirichlet solution -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped _root_.ENNReal

noncomputable section

/-- Actual endpoint estimates and vector interpolation produce a genuine
zero-boundary solution with a uniform raw norm bound for `2 ≤ p ≤ 4`. -/
theorem exists_dirichlet_lowExponent_raw_constants (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 1 ≤ C ∧
    ∀ {p delta : ℝ}, 2 ≤ p → p ≤ 4 → 0 ≤ delta → delta ≤ 1 / (4 * C) →
    ∀ (a : CoeffField d),
    (∀ i j, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
    (∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1), IsMatrixPerturbationLE delta (a x) 1) →
    ∀ (F : Vec d → Vec d),
    (∀ i, AEStronglyMeasurable (fun x => F x i) (volumeOn (euclideanBall (0 : Vec d) 1))) →
    MemLp (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p)
      (volumeOn (euclideanBall (0 : Vec d) 1)) →
    ∃ w : H10Function (euclideanBall (0 : Vec d) 1),
    IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) w.toH1Function 0 F ∧
    MemLp (fun x => vecEuclideanNorm (w.toH1Function.grad x)) (ENNReal.ofReal p)
      (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ∧
    eLpNorm (fun x => vecEuclideanNorm (w.toH1Function.grad x)) (ENNReal.ofReal p)
      (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
      ENNReal.ofReal ((d : ℝ)^2 * (6 * C)) *
        eLpNorm (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p)
          (volumeOn (euclideanBall (0 : Vec d) 1)) := by
  obtain ⟨C, hC, hFour⟩ := exists_ballDirichletInteriorGradient_four_constants d hd
  refine ⟨C, hC, ?_⟩
  intro p delta hp hpFour hdelta hsmall a ha hclose F hFcoord hFp
  let U := euclideanBall (0 : Vec d) 1
  let V := euclideanBall (0 : Vec d) (1 / 2)
  have hdeltaHalf : delta ≤ 1 / 2 := by
    apply hsmall.trans
    apply (div_le_iff₀ (by positivity : 0 < 4 * C)).2
    linarith only [hC]
  have hdeltaOne : delta < 1 := by linarith
  let T := ballDirichletInteriorGradientCLM hd 0 1 (by norm_num)
    a delta hdelta hdeltaOne ha hclose
  have hFL2 : MemVectorL2On U F :=
    memVectorL2On_euclideanBall_of_memLp_vecEuclideanNorm hp
      (0 : Vec d) (by norm_num) (V := U) (by rfl) hFp hFcoord
  have hFmeas : AEStronglyMeasurable F (volumeOn U) :=
    (aemeasurable_pi_iff.2 fun i => (hFcoord i).aemeasurable).aestronglyMeasurable
  let f := hFL2.toHilbertVectorLp
  have hInputP : MemLp f (ENNReal.ofReal p) (volumeOn U) := by
    rw [memLp_iff, eLpNorm_congr_ae hFL2.coeFn_toHilbertVectorLp,
      eLpNorm_toHilbertVecField_eq (hF := hFmeas)]
    exact hFp.eLpNorm_lt_top
  let : IsFiniteMeasure (volumeOn U) := isFiniteMeasure_volumeOn_euclideanBall 0 (by norm_num)
  let : IsFiniteMeasure (volumeOn V) := isFiniteMeasure_volumeOn_euclideanBall 0 (by norm_num)
  have hTwo : ∀ g : HilbertVectorLp U 2, MemLp g 2 (volumeOn U) →
      eLpNorm (T g) 2 (volumeOn V) ≤ ENNReal.ofReal (6 * C) * eLpNorm g 2 (volumeOn U) := by
    intro g _
    have he := eLpNorm_ballDirichletInteriorGradientCLM_two_le hd a hdelta hdeltaOne
      hdeltaHalf ha hclose g
    exact he.trans (mul_le_mul_left
      (by exact_mod_cast (ENNReal.ofReal_le_ofReal (by linarith : (2 : ℝ) ≤ 6 * C))) _)
  have hFourT : ∀ g : HilbertVectorLp U 2, MemLp g 4 (volumeOn U) →
      eLpNorm (T g) 4 (volumeOn V) ≤ ENNReal.ofReal (6 * C) * eLpNorm g 4 (volumeOn U) :=
    fun g hg => (hFour a delta hdelta hdeltaOne ha hclose hsmall g hg).2
  obtain ⟨hOutputP, hBound⟩ := memLp_and_eLpNorm_hilbertVector_operator_le_of_two_four
    hd (volumeOn U) (volumeOn V) T hp hpFour (by linarith : 1 ≤ 6 * C) hTwo hFourT f hInputP
  obtain ⟨w, _, hwAE, hwsol⟩ := exists_ballDirichletInteriorGradient_solution
    hd 0 1 (by norm_num) a delta hdelta hdeltaOne ha hclose F hFL2
  have hNormAE : (fun x => ‖T f x‖) =ᵐ[volumeOn V]
      fun x => vecEuclideanNorm (w.toH1Function.grad x) := by
    filter_upwards [hwAE] with x hx
    rw [hx]
    exact norm_toHilbertVecField_apply _ x
  have hGrad : MemLp (fun x => vecEuclideanNorm (w.toH1Function.grad x))
      (ENNReal.ofReal p) (volumeOn V) := hOutputP.norm.ae_eq hNormAE
  refine ⟨w, hwsol.toIsWeakDivergenceFormSolutionOn (isOpen_euclideanBall _ _), hGrad, ?_⟩
  rw [← eLpNorm_congr_ae hNormAE, eLpNorm_norm _ (Lp.aestronglyMeasurable _)]
  rw [eLpNorm_congr_ae hFL2.coeFn_toHilbertVectorLp,
    eLpNorm_toHilbertVecField_eq (hF := hFmeas)] at hBound
  exact hBound

end

end PDE
