module

public import EllipticRegularity.CalderonZygmund.ForcingSharpnessProof
public import PDEFoundation.Analysis.RadialForcingDivergence
public import PDEFoundation.PDE.WeakDivergenceForm
public import PDEFoundation.Measure.EuclideanFieldMeanLp
public import PDEFoundation.Measure.BallVolume
public import PDEFoundation.Sobolev.Mean
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

@[expose] public section

namespace PDE
open MeasureTheory
open scoped ENNReal

theorem exists_planar_logarithmic_forcing_sharpness :
    let B := euclideanBall (0 : Vec 2) 1
    let V := euclideanBall (0 : Vec 2) (1 / 2 : ℝ)
    ∃ u : H1Function B,
      (∀ x, u.toFun x = x 0 * Real.log (vecEuclideanNorm x)) ∧
      (∀ x i, u.grad x i = basisVec 0 i * Real.log (vecEuclideanNorm x) +
        x 0 * x i / vecNormSq x) ∧
      (∀ i : Fin 2, AEStronglyMeasurable (fun x => radialForcing 0 x i) (volumeOn B)) ∧
      MemLp (fun x => vecEuclideanNorm (radialForcing 0 x)) ⊤ (volumeOn B) ∧
      eLpNorm (fun x => vecEuclideanNorm (radialForcing 0 x)) ⊤ (volumeOn B) ≤ 2 ∧
      IsWeakDivergenceFormSolutionOn (fun _ => (1 : Mat 2)) B u 0 (radialForcing 0) ∧
      Real.sqrt (integralAverage B (fun x => vecNormSq (u.grad x))) = Real.sqrt (1 / 2 : ℝ) ∧
      (∀ p : ℝ, 2 ≤ p →
        ∃ hgrad : MemLp (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p) (volumeOn V),
          (1 / 2 : ℝ) * Real.rpow (Real.Gamma (p + 1)) (1 / p) - 1 ≤
            euclideanFieldLpMeanNormOn V (ENNReal.ofReal p) u.grad
              (memLp_normalizedVolumeOn_of_memLpOn hgrad
                (volume_euclideanBall_pos (0 : Vec 2) (by norm_num)))) ∧
      ¬MemLp (fun x => vecEuclideanNorm (u.grad x)) ⊤ (volumeOn V) := by exact PDE.CZForcingSharpnessProof.result

end PDE
