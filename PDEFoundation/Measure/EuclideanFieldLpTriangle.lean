module

public import PDEFoundation.Ambient.EuclideanNorm
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! # Triangle inequality for Euclidean magnitudes of native vector fields -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

/-- The scalar `Lᵖ` seminorm of the Euclidean magnitude satisfies the vector
field triangle inequality, without a finiteness assumption. -/
theorem eLpNorm_vecEuclideanNorm_add_le
    {d : ℕ} {μ : Measure (Vec d)} {p : ENNReal} (hp : 1 ≤ p)
    (F G : Vec d → Vec d)
    (_hF : AEStronglyMeasurable (fun x => vecEuclideanNorm (F x)) μ)
    (_hG : AEStronglyMeasurable (fun x => vecEuclideanNorm (G x)) μ)
    (hFG : AEStronglyMeasurable (fun x => vecEuclideanNorm (F x + G x)) μ) :
    eLpNorm (fun x => vecEuclideanNorm (F x + G x)) p μ ≤
      eLpNorm (fun x => vecEuclideanNorm (F x)) p μ +
        eLpNorm (fun x => vecEuclideanNorm (G x)) p μ := by
  calc
    eLpNorm (fun x => vecEuclideanNorm (F x + G x)) p μ ≤
        eLpNorm
          ((fun x => vecEuclideanNorm (F x)) +
            fun x => vecEuclideanNorm (G x)) p μ := by
      apply eLpNorm_mono_ae hFG
      filter_upwards with x
      simp only [Pi.add_apply]
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (vecEuclideanNorm_nonneg _),
        abs_of_nonneg (add_nonneg (vecEuclideanNorm_nonneg _)
          (vecEuclideanNorm_nonneg _))]
      exact vecEuclideanNorm_add_le (F x) (G x)
    _ ≤ eLpNorm (fun x => vecEuclideanNorm (F x)) p μ +
        eLpNorm (fun x => vecEuclideanNorm (G x)) p μ :=
      eLpNorm_add_le hp

end PDE
