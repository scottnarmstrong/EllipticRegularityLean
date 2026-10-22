module

public import EllipticRegularity.CalderonZygmund.RawForcing
public import CZStatements.NegativeSobolev
public import PDEFoundation.Analysis.NativeLpInjectedInfimum
public import PDEFoundation.Measure.BallVolume
public import PDEFoundation.PDE.WeakDivergenceFormFunctional
public import PDEFoundation.Measure.ForcingScale
public import PDEFoundation.Sobolev.H1.MeanEnergyOperator
public import PDEFoundation.Sobolev.W1p.ZeroBoundaryPoincare
public import CZStatements.General

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

noncomputable section


/-- Interior Calderón--Zygmund estimate with forcing supplied as a functional
on the gradient-normed zero-boundary Sobolev space.  The representing vector
field is constructed internally and does not occur in the theorem surface. -/
theorem exists_interior_negativeSobolev
    (d : ℕ) (hd : 0 < d) (Lambda : ℝ) (hLambda : 1 ≤ Lambda) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (p : ℝ), ∀ hp : 2 ≤ p,
      let q := ENNReal.ofReal (p / (p - 1))
      letI : Fact (1 ≤ q) :=
        ⟨ENNReal.one_le_ofReal.mpr
          (Real.HolderConjugate.conjExponent (lt_of_lt_of_le one_lt_two hp)).symm.lt.le⟩
      let U := euclideanBall (0 : Vec d) 1
      let S := W10pGraph (p := q) (isOpen_euclideanBall (0 : Vec d) 1)
      let A : S →ₗ[ℝ] HilbertVectorLp U q :=
        (w10pGradientCLM q (isOpen_euclideanBall (0 : Vec d) 1)).toLinearMap
      letI : NormedAddCommGroup S :=
        NormedAddCommGroup.induced S (HilbertVectorLp U q) A
          (w10pGradientCLM_injective hd
            (isOpenBoundedConvexDomain_euclideanBall
              (0 : Vec d) (by norm_num : (0 : ℝ) < 1))
            (hasEuclideanDiameterLE_euclideanBall
              (0 : Vec d) (by norm_num : (0 : ℝ) < 1))
            (by norm_num : (0 : ℝ) ≤ 2 * 1)
            (Real.HolderConjugate.conjExponent
              (lt_of_lt_of_le one_lt_two hp)).symm.lt)
      letI : SeminormedAddCommGroup S :=
        (inferInstance : NormedAddCommGroup S).toSeminormedAddCommGroup
      letI : TopologicalSpace S :=
        (inferInstance : NormedAddCommGroup S).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      letI : Norm S := (inferInstance : NormedAddCommGroup S).toNorm
      letI : NormedSpace ℝ S :=
        NormedSpace.induced ℝ S (HilbertVectorLp U q) A
      ∀ (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn U)) →
      (∀ᵐ x ∂volumeOn U, IsEllipticMatrix 1 Lambda (a x)) →
      (let A0 : Mat d := fun i j => integralAverage U (fun x => a x i j)
        ∀ᵐ x ∂volumeOn U,
          IsMatrixPerturbationLE (1 / (C * p)) (a x) A0) →
      ∀ (u : H1Function U) (L : S →L[ℝ] ℝ),
      (∀ φ : WeakTestFunction U,
        (∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (φ.grad x)) =
          L (smoothCompactlySupportedW1pGraphToW10pGraph
            (p := q) (isOpen_euclideanBall (0 : Vec d) 1) φ)) →
      MemW1p (euclideanBall (0 : Vec d) (1 / 2 : ℝ))
          (ENNReal.ofReal p) u.toFun ∧
        ∃ hgrad : MemLp (fun x => vecEuclideanNorm (u.grad x))
            (ENNReal.ofReal p)
            (volumeOn (euclideanBall (0 : Vec d) (1 / 2 : ℝ))),
          euclideanFieldLpMeanNormOn
              (euclideanBall (0 : Vec d) (1 / 2 : ℝ))
              (ENNReal.ofReal p) u.grad
              (memLp_normalizedVolumeOn_of_memLpOn hgrad
                (volume_euclideanBall_pos (0 : Vec d) (by norm_num))) ≤
            C *
              (Real.sqrt (integralAverage U (fun x => vecNormSq (u.grad x))) +
                p * (((volume U)⁻¹ ^
                  (1 / ENNReal.ofReal p).toReal).toReal * ‖L‖)) := by
  let hCZExists := exists_calderonZygmund_rawForcing d hd Lambda hLambda
  let C : ℝ := Classical.choose hCZExists
  have hCZSpec := Classical.choose_spec hCZExists
  have hC : 1 ≤ C := hCZSpec.1
  have hCZ := hCZSpec.2
  refine ⟨C, hC, ?_⟩
  intro p hp q U S A
  have hpOne : 1 < p := lt_of_lt_of_le one_lt_two hp
  let : Fact (1 ≤ q) :=
    ⟨ENNReal.one_le_ofReal.mpr (Real.HolderConjugate.conjExponent hpOne).symm.lt.le⟩
  have hA : Function.Injective A := by
    exact w10pGradientCLM_injective hd
      (isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) (by norm_num : (0 : ℝ) < 1))
      (hasEuclideanDiameterLE_euclideanBall (0 : Vec d) (by norm_num : (0 : ℝ) < 1))
      (by norm_num : (0 : ℝ) ≤ 2 * 1)
      (Real.HolderConjugate.conjExponent hpOne).symm.lt
  let inducedNormedAddCommGroup : NormedAddCommGroup S :=
    NormedAddCommGroup.induced S (HilbertVectorLp U q) A hA
  let inducedSeminormedAddCommGroup : SeminormedAddCommGroup S :=
    inducedNormedAddCommGroup.toSeminormedAddCommGroup
  let inducedTopologicalSpace : TopologicalSpace S :=
    inducedNormedAddCommGroup.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let inducedNorm : Norm S := inducedNormedAddCommGroup.toNorm
  let inducedNormedSpace : NormedSpace ℝ S :=
    NormedSpace.induced ℝ S (HilbertVectorLp U q) A
  have hrepresentation := exists_unitBall_divergence_representation d hd p hpOne
  intro a ha hell hsmall u L hfunctional
  obtain ⟨F, hFmeas, hF, hrep, hFnorm, _⟩ := hrepresentation L
  have hFL2 : MemVectorL2On U F := by
    apply memVectorL2On_euclideanBall_of_memLp_vecEuclideanNorm hp
      (0 : Vec d) (by norm_num) (V := U) (by
        intro x hx
        exact hx) hF hFmeas
  have hflux : MemVectorL2On U (fun x => matVecMul (a x) (u.grad x)) := by
    apply memVectorL2On_matVecMul_of_ae_operator_bound u.gradMemL2
      (fun i j => (ha i j).aestronglyMeasurable) (zero_le_one.trans hLambda)
    filter_upwards [hell] with x hx
    exact fun v => vecEuclideanNorm_matVecMul_le_of_isEllipticMatrix hx v
  have hdata : DivergenceFormL2DataOn a U u (fun _ => 0) F :=
    ⟨hflux, MemLp.zero, hFL2⟩
  have hrep' : ∀ v : S,
      L v = -∫ x in U,
        vecDot (F x)
          ((w10pGradientCLM q
            (isOpen_euclideanBall (0 : Vec d) 1) v x).toVec) := by
    simpa only [A] using! hrep
  have hsol : IsWeakDivergenceFormSolutionOn a U u (fun _ => 0) F :=
    isWeakDivergenceFormSolutionOn_of_functional_representation
      (q := q) (isOpen_euclideanBall (0 : Vec d) 1)
      hdata L hrep' hfunctional
  rw [← hFnorm]
  exact hCZ p hp a ha hell hsmall u F hFmeas hF hsol


end

end PDE
