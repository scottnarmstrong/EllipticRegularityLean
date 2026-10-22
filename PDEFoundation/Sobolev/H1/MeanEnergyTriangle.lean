module

public import PDEFoundation.Sobolev.H1.VectorMeanOscillation

/-! # Elementary normalized mean-energy identities -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The normalized Euclidean `L²` energy satisfies the triangle inequality. -/
theorem sqrt_integralAverage_vecNormSq_add_le
    {U : Set (Vec d)} {f g : Vec d → Vec d}
    (hf : MemVectorL2On U f) (hg : MemVectorL2On U g) :
    Real.sqrt (integralAverage U (fun x => vecNormSq (f x + g x))) ≤
      Real.sqrt (integralAverage U (fun x => vecNormSq (f x))) +
        Real.sqrt (integralAverage U (fun x => vecNormSq (g x))) := by
  rw [sqrt_integralAverage_vecNormSq_eq,
    sqrt_integralAverage_vecNormSq_eq,
    sqrt_integralAverage_vecNormSq_eq]
  have hraw := sqrt_setIntegral_vecNormSq_add_le hf hg
  calc
    Real.sqrt (∫ x in U, vecNormSq (f x + g x)) /
        Real.sqrt (volume U).toReal ≤
      (Real.sqrt (∫ x in U, vecNormSq (f x)) +
        Real.sqrt (∫ x in U, vecNormSq (g x))) /
          Real.sqrt (volume U).toReal :=
      div_le_div_of_nonneg_right hraw (Real.sqrt_nonneg _)
    _ = Real.sqrt (∫ x in U, vecNormSq (f x)) /
          Real.sqrt (volume U).toReal +
        Real.sqrt (∫ x in U, vecNormSq (g x)) /
          Real.sqrt (volume U).toReal := by ring

/-- The vector integral average of a constant field is that constant on a
positive finite-volume set. -/
theorem vectorIntegralAverage_const
    {U : Set (Vec d)} (hUpos : 0 < volume U) (hUtop : volume U < ∞)
    (c : Vec d) :
    vectorIntegralAverage U (fun _ => c) = c := by
  have hreal : (volume U).toReal ≠ 0 :=
    (ENNReal.toReal_pos hUpos.ne' hUtop.ne).ne'
  funext i
  rw [vectorIntegralAverage_apply, integralAverage, setIntegral_const,
    smul_eq_mul]
  change (volume U).toReal⁻¹ * ((volume U).toReal * c i) = c i
  rw [← mul_assoc, inv_mul_cancel₀ hreal, one_mul]

/-- The normalized Euclidean `L²` energy of a constant vector field is its
Euclidean magnitude. -/
theorem sqrt_integralAverage_vecNormSq_const
    {U : Set (Vec d)} (hUpos : 0 < volume U) (hUtop : volume U < ∞)
    (c : Vec d) :
    Real.sqrt (integralAverage U (fun _ => vecNormSq c)) =
      vecEuclideanNorm c := by
  have hreal : (volume U).toReal ≠ 0 :=
    (ENNReal.toReal_pos hUpos.ne' hUtop.ne).ne'
  unfold integralAverage
  rw [setIntegral_const, smul_eq_mul]
  change Real.sqrt ((volume U).toReal⁻¹ *
    ((volume U).toReal * vecNormSq c)) = vecEuclideanNorm c
  rw [← mul_assoc, inv_mul_cancel₀ hreal, one_mul]
  rfl

end

end PDE
