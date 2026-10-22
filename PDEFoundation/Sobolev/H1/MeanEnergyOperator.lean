module

public import PDEFoundation.Sobolev.H1.MeanEnergy
public import PDEFoundation.Sobolev.H1.VectorL2Bounds
public import PDEFoundation.Ambient.MatrixPerturbation

/-!
# Operator bounds for normalized vector mean energy
-/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

/-- Almost-everywhere Euclidean operator domination gives the corresponding
sharp domination of normalized root mean-square vector energy. The statement
is total in the volume of `U`. -/
theorem sqrt_integralAverage_vecNormSq_le_mul_of_ae_vecEuclideanNorm_le
    {F G : Vec d → Vec d} {delta : ℝ}
    (hF : MemVectorL2On U F) (hG : MemVectorL2On U G)
    (hdelta : 0 ≤ delta)
    (hbound : ∀ᵐ x ∂volumeOn U,
      vecEuclideanNorm (F x) ≤ delta * vecEuclideanNorm (G x)) :
    Real.sqrt (integralAverage U (fun x => vecNormSq (F x))) ≤
      delta * Real.sqrt (integralAverage U (fun x => vecNormSq (G x))) := by
  have hraw := sqrt_setIntegral_vecNormSq_le_mul_of_ae_vecEuclideanNorm_le
    hF hG hdelta hbound
  rw [sqrt_integralAverage_vecNormSq_eq,
    sqrt_integralAverage_vecNormSq_eq]
  calc
    Real.sqrt (∫ x in U, vecNormSq (F x)) /
        Real.sqrt (volume U).toReal ≤
      (delta * Real.sqrt (∫ x in U, vecNormSq (G x))) /
        Real.sqrt (volume U).toReal :=
      div_le_div_of_nonneg_right hraw (Real.sqrt_nonneg _)
    _ = delta *
        (Real.sqrt (∫ x in U, vecNormSq (G x)) /
          Real.sqrt (volume U).toReal) := by ring

/-- A matrix field with measurable entries and an almost-everywhere
Euclidean operator bound sends native vector `L²` fields to native vector
`L²` fields. -/
theorem memVectorL2On_matVecMul_of_ae_operator_bound
    {a : Vec d → Mat d} {G : Vec d → Vec d} {delta : ℝ}
    (hG : MemVectorL2On U G)
    (hmeas : ∀ i j, AEStronglyMeasurable (fun x => a x i j) (volumeOn U))
    (_hdelta : 0 ≤ delta)
    (hbound : ∀ᵐ x ∂volumeOn U, ∀ v : Vec d,
      vecEuclideanNorm (matVecMul (a x) v) ≤ delta * vecEuclideanNorm v) :
    MemVectorL2On U (fun x => matVecMul (a x) (G x)) := by
  classical
  intro i
  have hmeasCoord : AEStronglyMeasurable
      (fun x => matVecMul (a x) (G x) i) (volumeOn U) := by
    simp only [matVecMul]
    convert (Finset.aestronglyMeasurable_sum Finset.univ fun j _ =>
      (hmeas i j).mul (hG j).aestronglyMeasurable) using 1
    funext x
    simp
  have hcoordBound : ∀ᵐ x ∂volumeOn U,
      ‖matVecMul (a x) (G x) i‖ ≤
        delta * vecEuclideanNorm (G x) := by
    filter_upwards [hbound] with x hx
    simpa only [Real.norm_eq_abs] using
      (abs_apply_le_vecEuclideanNorm (matVecMul (a x) (G x)) i).trans (hx (G x))
  apply MemLp.of_le_mul hG.memLp_vecEuclideanNorm hmeasCoord
  simpa only [Real.norm_eq_abs, abs_of_nonneg (vecEuclideanNorm_nonneg _)] using
    hcoordBound

end

end PDE
