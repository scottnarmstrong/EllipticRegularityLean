module

public import PDEFoundation.Measure.SparseCubePointwise
public import PDEFoundation.PDE.CubeGradientMeanBound
public import PDEFoundation.PDE.LaplacianDyadicCubeEssentialInf

/-! # Pointwise sparse bound on one Laplacian root cube -/

@[expose] public section

namespace PDE

open BoxIntegral MeasureTheory Set
open scoped _root_.ENNReal

noncomputable section

/-- The original weak Laplacian data on a doubled circumscribed ball imply the
source pointwise sparse bound on the root cube, with all mean and descendant
excess premises discharged internally. -/
theorem ae_vecEuclideanNorm_grad_le_laplacian_dyadicSparseSum
    {d : ℕ} (I : Box (Fin d)) (L : ℝ) (hd : 0 < d)
    (hwidth : ∀ i, I.upper i - I.lower i = L)
    (u : H1Function (euclideanBall (boxCenter I)
      (2 * (Real.sqrt d * L / 2))))
    (F : Vec d → Vec d)
    (hF : MemVectorL2On (euclideanBall (boxCenter I)
      (2 * (Real.sqrt d * L / 2))) F)
    (hsol : IsWeakDivergenceFormSolutionOn (fun _ => (1 : Mat d))
      (euclideanBall (boxCenter I) (2 * (Real.sqrt d * L / 2))) u 0 F)
    {p : ℝ} (hp : 2 < p)
    (hFp : MemLp (fun x => vecEuclideanNorm (F x))
      (ENNReal.ofReal p) volume) :
    ∀ᵐ x ∂volume.restrict (I : Set (Vec d)),
      ENNReal.ofReal (vecEuclideanNorm (u.grad x)) ≤
        ENNReal.ofReal
          (((1 + 2 * (2 : ℝ) ^ (1 + (d : ℝ) / 2)) *
              Real.sqrt ((volume (euclideanBall (0 : Vec d) 1)).toReal *
                (Real.sqrt d / 2) ^ d) * Real.sqrt ((2 : ℝ) ^ d)) *
            Real.sqrt (integralAverage
              (euclideanBall (boxCenter I) (2 * (Real.sqrt d * L / 2)))
              (fun y => vecNormSq (u.grad y)))) +
          ENNReal.ofReal
            (((2 : ℝ) ^ (1 + (d : ℝ) / 2) *
                Real.sqrt ((volume (euclideanBall (0 : Vec d) 1)).toReal *
                  (Real.sqrt d / 2) ^ d)) *
              (((d : ℝ) + 2) / 2 * (1 + 2 / (d : ℝ)) ^ ((d : ℝ) / 2))) *
            dyadicSparseSum I (dyadicSparseFamily I u.grad)
              (dyadicBoxEssentialInfReal I
                (fun y => (quadraticBallMaximal F y).toReal)) x := by
  let D := Real.sqrt ((volume (euclideanBall (0 : Vec d) 1)).toReal *
    (Real.sqrt d / 2) ^ d)
  let κ := ((d : ℝ) + 2) / 2 * (1 + 2 / (d : ℝ)) ^ ((d : ℝ) / 2)
  let C := (2 : ℝ) ^ (1 + (d : ℝ) / 2)
  let U0 := Real.sqrt (integralAverage
    (euclideanBall (boxCenter I) (2 * (Real.sqrt d * L / 2)))
    (fun y => vecNormSq (u.grad y)))
  let A := D * Real.sqrt ((2 : ℝ) ^ d) * U0
  let B := D * κ
  let b : Vec d → ℝ := fun y => (quadraticBallMaximal F y).toReal
  let i0 : Fin d := ⟨0, hd⟩
  have hL : 0 < L := by
    rw [← hwidth i0]
    exact sub_pos.mpr (I.lower_lt_upper i0)
  have hr0 : 0 < Real.sqrt d * L / 2 := by
    have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
    positivity
  have hrootOuter : (I : Set (Vec d)) ⊆
      euclideanBall (boxCenter I) (2 * (Real.sqrt d * L / 2)) :=
    (Box.coe_subset_euclideanClosedBall_boxCenter I L hd hwidth).trans
      (euclideanClosedBall_subset_euclideanBall hr0.le (by linarith))
  have hgrad : ∀ i, MemLp (fun x => u.grad x i) 2
      (volumeOn (I : Set (Vec d))) := fun i =>
    memLpOn_mono hrootOuter (u.gradMemL2 i)
  have hA : 0 ≤ A := by
    dsimp only [A, D, U0]
    positivity
  have hB : 0 ≤ B := by
    have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
    have hunit : 0 < (volume (euclideanBall (0 : Vec d) 1)).toReal :=
      volume_euclideanBall_toReal_pos (0 : Vec d) (by norm_num)
    dsimp only [B, D, κ]
    positivity
  have hmean : vecEuclideanNorm
      (coordinateVectorAverage (I : Set (Vec d)) u.grad) ≤ A := by
    rw [coordinateVectorAverage_eq_vectorIntegralAverage]
    simpa only [A, D, U0, mul_assoc] using
      vecEuclideanNorm_vectorIntegralAverage_grad_box_le I L hd hwidth u
  have hexcess (q : List (Set (Fin d))) : dyadicMeanOscillation I u.grad q ≤
      A * (1 / 2 : ℝ) ^ q.length +
        B * dyadicBoxEssentialInfReal I b q := by
    have hq := centeredVectorMeanL2_dyadicDescendant_le_essentialInf
      I L hd hwidth u F hF hsol hp hFp q
    rw [dyadicMeanOscillation, coordinateVectorAverage_eq_vectorIntegralAverage]
    change centeredVectorMeanL2 (dyadicDescendant I q : Set (Vec d)) u.grad ≤ _
    calc
      centeredVectorMeanL2 (dyadicDescendant I q : Set (Vec d)) u.grad ≤
          (Real.sqrt ((volume (euclideanBall (0 : Vec d) 1)).toReal *
              (Real.sqrt d / 2) ^ d) * Real.sqrt ((2 : ℝ) ^ d) /
              (2 : ℝ) ^ q.length) *
            Real.sqrt (integralAverage
              (euclideanBall (boxCenter I) (2 * (Real.sqrt d * L / 2)))
              (fun y => vecNormSq (u.grad y))) +
          (Real.sqrt ((volume (euclideanBall (0 : Vec d) 1)).toReal *
              (Real.sqrt d / 2) ^ d) *
            (((d : ℝ) + 2) / 2 *
              (1 + 2 / (d : ℝ)) ^ ((d : ℝ) / 2))) *
            dyadicBoxEssentialInfReal I b q := by simpa only [b] using hq
      _ = A * (1 / 2 : ℝ) ^ q.length +
          B * dyadicBoxEssentialInfReal I b q := by
        rw [one_div_pow]
        dsimp only [A, B, D, κ, U0]
        ring
  have hpoint := ae_vecEuclideanNorm_le_of_mean_and_dyadic_excess
    I hd u.grad hgrad b hA hB hmean hexcess
  have henergy : (1 + 2 * C) * A =
      ((1 + 2 * (2 : ℝ) ^ (1 + (d : ℝ) / 2)) *
          Real.sqrt ((volume (euclideanBall (0 : Vec d) 1)).toReal *
            (Real.sqrt d / 2) ^ d) * Real.sqrt ((2 : ℝ) ^ d)) *
        Real.sqrt (integralAverage
          (euclideanBall (boxCenter I) (2 * (Real.sqrt d * L / 2)))
          (fun y => vecNormSq (u.grad y))) := by
    dsimp only [C, A, D, U0]
    ring
  have hforcing : C * B =
      ((2 : ℝ) ^ (1 + (d : ℝ) / 2) *
          Real.sqrt ((volume (euclideanBall (0 : Vec d) 1)).toReal *
            (Real.sqrt d / 2) ^ d)) *
        (((d : ℝ) + 2) / 2 * (1 + 2 / (d : ℝ)) ^ ((d : ℝ) / 2)) := by
    dsimp only [C, B, D, κ]
    ring
  simpa only [C, A, B, b, henergy, hforcing] using hpoint

end

end PDE
