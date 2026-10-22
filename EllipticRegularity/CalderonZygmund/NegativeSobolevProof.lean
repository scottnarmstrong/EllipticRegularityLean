module

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

namespace CZNegativeSobolevProof

/-- Representation of the dual of the zero-boundary Sobolev space by a
minimal native vector-valued density. -/
theorem result
    (d : ℕ) (hd : 0 < d) (p : ℝ) (hp : 1 < p) :
    let q := ENNReal.ofReal (p / (p - 1))
    letI : Fact (1 ≤ q) :=
      ⟨ENNReal.one_le_ofReal.mpr (Real.HolderConjugate.conjExponent hp).symm.lt.le⟩
    let U := euclideanBall (0 : Vec d) 1
    let S := W10pGraph (p := q) (isOpen_euclideanBall (0 : Vec d) 1)
    let A : S →ₗ[ℝ] HilbertVectorLp U q :=
      (w10pGradientCLM q (isOpen_euclideanBall (0 : Vec d) 1)).toLinearMap
    letI : NormedAddCommGroup S := NormedAddCommGroup.induced S (HilbertVectorLp U q) A
      (w10pGradientCLM_injective hd
        (isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) (by norm_num : (0 : ℝ) < 1))
        (hasEuclideanDiameterLE_euclideanBall (0 : Vec d) (by norm_num : (0 : ℝ) < 1))
        (by norm_num : (0 : ℝ) ≤ 2 * 1)
        (Real.HolderConjugate.conjExponent hp).symm.lt)
    letI : SeminormedAddCommGroup S :=
      (inferInstance : NormedAddCommGroup S).toSeminormedAddCommGroup
    letI : TopologicalSpace S :=
      (inferInstance : NormedAddCommGroup S).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI : Norm S := (inferInstance : NormedAddCommGroup S).toNorm
    letI : NormedSpace ℝ S := NormedSpace.induced ℝ S (HilbertVectorLp U q) A
    ∀ L : S →L[ℝ] ℝ,
      ∃ F : Vec d → Vec d,
        (∀ i : Fin d, AEStronglyMeasurable (fun x => F x i) (volumeOn U)) ∧
        MemLp (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p) (volumeOn U) ∧
        (∀ u : S, L u = -∫ x, vecDot (F x) ((A u x).toVec) ∂volumeOn U) ∧
        (eLpNorm (fun x => vecEuclideanNorm (F x))
          (ENNReal.ofReal p) (volumeOn U)).toReal = ‖L‖ ∧
        ‖L‖ = sInf {N : ℝ | ∃ G : Vec d → Vec d,
          (∀ i : Fin d, AEStronglyMeasurable (fun x => G x i) (volumeOn U)) ∧
          MemLp (fun x => vecEuclideanNorm (G x)) (ENNReal.ofReal p) (volumeOn U) ∧
          (∀ u : S, L u = -∫ x, vecDot (G x) ((A u x).toVec) ∂volumeOn U) ∧
          (eLpNorm (fun x => vecEuclideanNorm (G x))
            (ENNReal.ofReal p) (volumeOn U)).toReal = N} := by
  let q := ENNReal.ofReal (p / (p - 1))
  let : Fact (1 ≤ q) :=
    ⟨ENNReal.one_le_ofReal.mpr (Real.HolderConjugate.conjExponent hp).symm.lt.le⟩
  let U := euclideanBall (0 : Vec d) 1
  let S := W10pGraph (p := q) (isOpen_euclideanBall (0 : Vec d) 1)
  let A : S →ₗ[ℝ] HilbertVectorLp U q :=
    (w10pGradientCLM q (isOpen_euclideanBall (0 : Vec d) 1)).toLinearMap
  let graphNormedAddCommGroup : NormedAddCommGroup S := inferInstance
  let graphNormedSpace : NormedSpace ℝ S := inferInstance
  have hA : Function.Injective A := by
    simpa only [A, q, U] using!
      (w10pGradientCLM_injective hd
        (isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) (by norm_num : (0 : ℝ) < 1))
        (hasEuclideanDiameterLE_euclideanBall (0 : Vec d) (by norm_num : (0 : ℝ) < 1))
        (by norm_num : (0 : ℝ) ≤ 2 * 1)
        (Real.HolderConjugate.conjExponent hp).symm.lt)
  let : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  let : IsFiniteMeasure (volumeOn U) := by
    dsimp only [U]
    exact isFiniteMeasure_volumeOn_euclideanBall (0 : Vec d) (by norm_num)
  have hmain := exists_nativeLp_density_and_infimum_through_injective
    (μ := volumeOn U) (d := d) (p := p) (E := S) hp A hA
  let inducedNormedAddCommGroup : NormedAddCommGroup S :=
    NormedAddCommGroup.induced S (HilbertVectorLp U q) A hA
  let inducedSeminormedAddCommGroup : SeminormedAddCommGroup S :=
    inducedNormedAddCommGroup.toSeminormedAddCommGroup
  let inducedTopologicalSpace : TopologicalSpace S :=
    inducedNormedAddCommGroup.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let inducedNorm : Norm S := inducedNormedAddCommGroup.toNorm
  let inducedNormedSpace : NormedSpace ℝ S :=
    NormedSpace.induced ℝ S (HilbertVectorLp U q) A
  exact hmain

end CZNegativeSobolevProof

end

end PDE
