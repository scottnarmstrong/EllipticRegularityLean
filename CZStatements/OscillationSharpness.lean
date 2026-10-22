module

public import EllipticRegularity.CalderonZygmund.OscillationSharpnessProof
public import PDEFoundation.Analysis.RadialCoefficientFlux
public import PDEFoundation.PDE.WeakDivergenceForm
public import PDEFoundation.Measure.PlanarRadialAverage
public import PDEFoundation.Ambient.RadialPerturbationSize
public import PDEFoundation.Measure.EuclideanFieldMeasurability

@[expose] public section

namespace PDE
open MeasureTheory
open scoped ENNReal

theorem exists_planar_radialMode_sharpness
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    let β := Real.sqrt ((1 - δ) / (1 + δ))
    let B := euclideanBall (0 : Vec 2) 1
    let a : CoeffField 2 := fun x => (1 : Mat 2) + δ • radialReflectionMatrix x
    ∃ u : H1Function B,
      (∀ x, u.toFun x = x 0 * Real.rpow (vecEuclideanNorm x) (β - 1)) ∧
      (∀ x, u.grad x = radialModePowerField 0 β x) ∧
      IsWeakDivergenceFormSolutionOn a B u 0 0 ∧
      (∀ x, IsEllipticMatrix (1 - δ) (1 + δ) (a x)) ∧
      (∀ x, IsEllipticMatrix 1 ((1 + δ) / (1 - δ)) ((1 - δ)⁻¹ • a x)) ∧
      ((fun i j => integralAverage B (fun x => a x i j)) = (1 : Mat 2)) ∧
      (∀ (x : Vec 2) (ε : ℝ), IsMatrixPerturbationLE ε (a x) (1 : Mat 2) ↔ δ ≤ ε) ∧
      ∀ (p R : ℝ), 0 < p → 0 < R →
        (MemLp (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
          (volumeOn (euclideanBall (0 : Vec 2) R)) ↔ p * (1 - β) < 2) := by exact PDE.CZOscillationSharpnessProof.result δ hδ0 hδ1

end PDE
