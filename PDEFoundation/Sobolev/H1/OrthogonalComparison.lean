module

public import PDEFoundation.Sobolev.H1.OrthogonalOscillation
public import PDEFoundation.Sobolev.H1.VectorMeanRestriction

/-! # Oscillation comparison for orthogonal replacements -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- A zero-mean orthogonal error preserves the exact contraction coefficient
on the outer centered energy. Only its restriction incurs a volume factor. -/
theorem centeredVectorMeanL2_comparison_of_orthogonal_contraction
    {V U : Set (Vec d)} (hVU : V ⊆ U) {h w : Vec d → Vec d}
    (hh : MemVectorL2On U h) (hw : MemVectorL2On U w)
    (hVpos : 0 < volume V) (hVtop : volume V < ∞)
    (hUpos : 0 < volume U) (hUtop : volume U < ∞)
    (hmean : vectorIntegralAverage U w = 0)
    (horth : ∫ x in U, vecDot (h x) (w x) = 0)
    {θ : ℝ} (hθ : 0 ≤ θ)
    (hdecay : centeredVectorMeanL2 V h ≤ θ * centeredVectorMeanL2 U h) :
    centeredVectorMeanL2 V (fun x => h x + w x) ≤
      θ * centeredVectorMeanL2 U (fun x => h x + w x) +
        Real.sqrt ((volume U).toReal / (volume V).toReal) *
          Real.sqrt (integralAverage U (fun x => vecNormSq (w x))) := by
  have hhV : MemVectorL2On V h := fun i => memLpOn_mono hVU (hh i)
  have hwV : MemVectorL2On V w := fun i => memLpOn_mono hVU (hw i)
  have hcenter := centeredVectorMeanL2_le_add_of_orthogonal_of_mean_eq_zero
    hh hw hUpos hUtop hmean horth
  have hwbound := (centeredVectorMeanL2_mono_set hVU hw hVpos hVtop hUpos hUtop).trans
    (mul_le_mul_of_nonneg_left
      (centeredVectorMeanL2_le_sqrt_integralAverage_vecNormSq hw hUpos hUtop)
      (Real.sqrt_nonneg _))
  exact (centeredVectorMeanL2_add_le hhV hwV hVtop).trans
    (add_le_add (hdecay.trans (mul_le_mul_of_nonneg_left hcenter hθ)) hwbound)

end PDE
