module

public import CZStatements.General
public import PDEFoundation.Measure.ForcingScale

@[expose] public section

open scoped ENNReal

namespace PDE
open MeasureTheory

/-- Calderon--Zygmund estimate with the exact unit-ball conversion from raw forcing norm. -/
theorem exists_calderonZygmund_rawForcing
    (d : ℕ) (hd : 0 < d) (Lambda : ℝ) (hLambda : 1 ≤ Lambda) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (p : ℝ), 2 ≤ p →
      ∀ (a : CoeffField d),
      (∀ i j : Fin d,
        AEMeasurable (fun x => a x i j)
          (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
        IsEllipticMatrix 1 Lambda (a x)) →
      (let A0 : Mat d := fun i j =>
          integralAverage (euclideanBall (0 : Vec d) 1)
            (fun x => a x i j)
        ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
          IsMatrixPerturbationLE (1 / (C * p)) (a x) A0) →
      ∀ (u : H1Function (euclideanBall (0 : Vec d) 1))
        (F : Vec d → Vec d),
      (∀ i : Fin d,
        AEStronglyMeasurable (fun x => F x i)
          (volumeOn (euclideanBall (0 : Vec d) 1))) →
      ∀ (_hF : MemLp (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p)
          (volumeOn (euclideanBall (0 : Vec d) 1))),
      IsWeakDivergenceFormSolutionOn a
          (euclideanBall (0 : Vec d) 1) u (0 : Vec d → ℝ) F →
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
              (Real.sqrt
                  (integralAverage (euclideanBall (0 : Vec d) 1)
                    (fun x => vecNormSq (u.grad x))) +
                p * ((((volume (euclideanBall (0 : Vec d) 1))⁻¹ ^
                    (1 / ENNReal.ofReal p).toReal).toReal) *
                  (eLpNorm (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p)
                    (volumeOn (euclideanBall (0 : Vec d) 1))).toReal)) := by
  obtain ⟨C, hC, hCZ⟩ := exists_calderonZygmund d hd Lambda hLambda
  refine ⟨C, hC, ?_⟩
  intro p hp a ha hell hsmall u F hFmeas hF hsol
  obtain ⟨hW, hgrad, hbound⟩ := hCZ p hp a ha hell hsmall u F hFmeas hF hsol
  refine ⟨hW, hgrad, ?_⟩
  let U := euclideanBall (0 : Vec d) 1
  have hFmean : MemLp (fun x => vecEuclideanNorm (F x))
      (ENNReal.ofReal p) (normalizedVolumeOn U) :=
    memLp_normalizedVolumeOn_of_memLpOn hF
      (volume_euclideanBall_pos (0 : Vec d) (by norm_num))
  have hmean : euclideanFieldLpMeanNormOn U (ENNReal.ofReal p) F hFmean =
      (((volume U)⁻¹ ^ (1 / ENNReal.ofReal p).toReal).toReal *
        (eLpNorm (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p)
          (volumeOn U)).toReal) := by
    rw [euclideanFieldLpMeanNormOn, lpMeanNormOn_eq_toReal]
    change (euclideanFieldELpMeanNormOn U (ENNReal.ofReal p) F).toReal = _
    rw [euclideanFieldELpMeanNormOn_eq_volume_inv_rpow_mul
        (lt_top_iff_ne_top.mpr
          (volume_euclideanBall_ne_top (0 : Vec d) (by norm_num)))]
    rw [ENNReal.toReal_mul]
    rfl
  simpa only [U, hmean] using hbound

end PDE
