module

public import PDEFoundation.Sobolev.H1.VectorMeanOscillation

/-!
# Centered energy of orthogonal fields

Orthogonality and a zero-mean second field preserve the first field's mean.
The ordinary Euclidean Pythagorean identity therefore also holds for centered
energy. This algebra is independent of harmonicity and boundary geometry.
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

variable {d : ℕ} {U : Set (Vec d)}

/-- Adding an orthogonal field with zero vector mean increases centered energy. -/
theorem centeredVectorMeanL2_le_add_of_orthogonal_of_mean_eq_zero
    {h w : Vec d → Vec d}
    (hh : MemVectorL2On U h) (hw : MemVectorL2On U w)
    (hUpos : 0 < volume U) (hUtop : volume U < ∞)
    (hmean : vectorIntegralAverage U w = 0)
    (horth : ∫ x in U, vecDot (h x) (w x) = 0) :
    centeredVectorMeanL2 U h ≤ centeredVectorMeanL2 U (fun x => h x + w x) := by
  have hsum : MemVectorL2On U (fun x => h x + w x) := fun i => (hh i).add (hw i)
  have hsumMean : vectorIntegralAverage U (fun x => h x + w x) =
      vectorIntegralAverage U h := by
    rw [vectorIntegralAverage_add
      (integrableOn_of_memVectorL2On_of_volume_lt_top hh hUtop)
      (integrableOn_of_memVectorL2On_of_volume_lt_top hw hUtop), hmean, add_zero]
  have hhSq := integrableOn_vecNormSq_of_memVectorL2On hh
  have hwSq := integrableOn_vecNormSq_of_memVectorL2On hw
  have hcross := (integrableOn_vecDot_of_memVectorL2On hh hw).const_mul 2
  have henergy : (∫ x in U, vecNormSq (h x + w x)) =
      (∫ x in U, vecNormSq (h x)) + ∫ x in U, vecNormSq (w x) := by
    simp_rw [vecNormSq_add_expand]
    have hsplit := integral_add (hhSq.add hcross) hwSq
    have hinner := integral_add hhSq hcross
    simp only [Pi.add_apply] at hsplit hinner
    rw [hsplit, hinner, integral_const_mul, horth, mul_zero, add_zero]
  have hhVariance := setIntegral_vecNormSq_sub_eq_centered_add hh hUpos hUtop 0
  have hsumVariance := setIntegral_vecNormSq_sub_eq_centered_add hsum hUpos hUtop 0
  simp only [sub_zero, hsumMean] at hhVariance hsumVariance
  have hraw : (∫ x in U, vecNormSq (h x - vectorIntegralAverage U h)) ≤
      ∫ x in U, vecNormSq (h x + w x - vectorIntegralAverage U (fun x => h x + w x)) := by
    have hwNonneg : 0 ≤ ∫ x in U, vecNormSq (w x) :=
      integral_nonneg fun x => vecNormSq_nonneg (w x)
    rw [hsumMean]
    linarith only [hhVariance, hsumVariance, henergy, hwNonneg]
  unfold centeredVectorMeanL2
  simp only [sqrt_integralAverage_vecNormSq_eq]
  exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hraw) (Real.sqrt_nonneg _)

end PDE
