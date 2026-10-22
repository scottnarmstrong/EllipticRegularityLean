module

public import PDEFoundation.Sobolev.H1.MeanEnergyOperator
public import PDEFoundation.Sobolev.H1.VectorMeanRestriction

/-!
# Linear operator bounds for centered vector mean oscillation
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

/-- Centering at the vector integral average has no more normalized Euclidean
`L²` energy than centering at an arbitrary constant vector. -/
theorem centeredVectorMeanL2_le_sqrt_integralAverage_sub_const
    {g : Vec d → Vec d} (hg : MemVectorL2On U g)
    (hUpos : 0 < volume U) (hUtop : volume U < ∞) (c : Vec d) :
    centeredVectorMeanL2 U g ≤
      Real.sqrt (integralAverage U (fun x => vecNormSq (g x - c))) := by
  have hraw := setIntegral_vecNormSq_sub_vectorIntegralAverage_le
    hg hUpos hUtop c
  unfold centeredVectorMeanL2
  simp only [sqrt_integralAverage_vecNormSq_eq]
  exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hraw)
    (Real.sqrt_nonneg _)

/-- A constant matrix satisfying a Euclidean operator bound sends native
vector `L²` fields to native vector `L²` fields. -/
theorem memVectorL2On_const_matVecMul
    (A : Mat d) {g : Vec d → Vec d} (hg : MemVectorL2On U g)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hA : ∀ v : Vec d,
      vecEuclideanNorm (matVecMul A v) ≤ delta * vecEuclideanNorm v) :
    MemVectorL2On U (fun x => matVecMul A (g x)) := by
  apply memVectorL2On_matVecMul_of_ae_operator_bound
    (a := fun _ => A) hg
  · intro i j
    exact aestronglyMeasurable_const
  · exact hdelta
  · exact Filter.Eventually.of_forall fun _ v => hA v

/-- A constant Euclidean operator contracts centered native-vector mean
`L²` oscillation by its displayed operator bound. -/
theorem centeredVectorMeanL2_const_matVecMul_le
    (A : Mat d) {g : Vec d → Vec d} (hg : MemVectorL2On U g)
    (hUpos : 0 < volume U) (hUtop : volume U < ∞)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hA : ∀ v : Vec d,
      vecEuclideanNorm (matVecMul A v) ≤ delta * vecEuclideanNorm v) :
    centeredVectorMeanL2 U (fun x => matVecMul A (g x)) ≤
      delta * centeredVectorMeanL2 U g := by
  let m := vectorIntegralAverage U g
  have hgCenter : MemVectorL2On U (fun x => g x - m) :=
    memVectorL2On_sub_const hg hUtop m
  have hAg : MemVectorL2On U (fun x => matVecMul A (g x)) :=
    memVectorL2On_const_matVecMul A hg hdelta hA
  have hACenter : MemVectorL2On U
      (fun x => matVecMul A (g x - m)) :=
    memVectorL2On_const_matVecMul A hgCenter hdelta hA
  have hmin := centeredVectorMeanL2_le_sqrt_integralAverage_sub_const
    hAg hUpos hUtop (matVecMul A m)
  have hsub (x : Vec d) :
      matVecMul A (g x) - matVecMul A m = matVecMul A (g x - m) :=
    (map_sub (Matrix.toLin' A) (g x) m).symm
  simp_rw [hsub] at hmin
  have hop := sqrt_integralAverage_vecNormSq_le_mul_of_ae_vecEuclideanNorm_le
    hACenter hgCenter hdelta
    (Filter.Eventually.of_forall fun x => hA (g x - m))
  exact hmin.trans (by simpa only [centeredVectorMeanL2] using hop)

end

end PDE
