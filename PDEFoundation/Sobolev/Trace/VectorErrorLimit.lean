module

public import PDEFoundation.Sobolev.OneDimensional.SmoothApproximationLimit
public import PDEFoundation.Sobolev.Trace.CoordinateControl

/-!
# One-dimensional limits from vector error control

This module is the native-`Vec` bridge between an explicit Euclidean-magnitude
control of a vector-valued approximation error and the scalar one-dimensional
smooth-approximation limit theorem.  The coordinate estimate has constant one;
the measurability of the coordinate is derived from the smooth scalar
derivative and the supplied scalar derivative datum, rather than inferred from
the magnitude alone.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open Filter MeasureTheory Set

noncomputable section

/-- Smooth scalar approximants whose value errors converge in interval `L²`
and whose derivative errors are a specified coordinate of a vector error with
vanishing explicit Euclidean-magnitude energy have a canonical continuous
limit.  The coordinate passage has constant one, and its measurability comes
from the displayed pointwise derivative-error identity. -/
theorem uniformCauchySeqLimit_hasWeakDerivOnIoo_of_tendsto_setIntegral_sq_vector_error
    {d : ℕ} {i : Fin d} {a b : ℝ} (hab : a < b)
    {F : ℕ → ℝ → ℝ} {u g : ℝ → ℝ} {E : ℕ → ℝ → Vec d}
    (hF : ∀ n, ContDiff ℝ 1 (F n))
    (hu : MemLp u 2 (volume.restrict (Icc a b)))
    (hg : MemLp g 2 (volume.restrict (Icc a b)))
    (hValueError : ∀ n, MemLp (fun t => F n t - u t) 2
      (volume.restrict (Icc a b)))
    (hVectorError : ∀ n, MemLp (fun t => vecEuclideanNorm (E n t)) 2
      (volume.restrict (Icc a b)))
    (hValue : Tendsto
      (fun n => ∫ t in Icc a b, |F n t - u t| ^ 2) atTop (𝓝 0))
    (hVector : Tendsto
      (fun n => ∫ t in Icc a b, vecEuclideanNorm (E n t) ^ 2)
        atTop (𝓝 0))
    (hDerivativeError : ∀ n t, deriv (F n) t - g t = E n t i) :
    TendstoUniformlyOn F (uniformCauchySeqLimit F) atTop (Icc a b) ∧
      ContinuousOn (uniformCauchySeqLimit F) (Icc a b) ∧
      uniformCauchySeqLimit F =ᵐ[volume.restrict (Icc a b)] u ∧
      HasWeakDerivOnIoo a b (uniformCauchySeqLimit F) g := by
  have hCoordinateMeas : ∀ n, AEStronglyMeasurable (fun t => E n t i)
      (volume.restrict (Icc a b)) := by
    intro n
    have hScalarMeas : AEStronglyMeasurable
        (fun t => deriv (F n) t - g t) (volume.restrict (Icc a b)) :=
      ((hF n).continuous_deriv_one.continuousOn
        |>.aestronglyMeasurable measurableSet_Icc).sub hg.aestronglyMeasurable
    refine hScalarMeas.congr ?_
    filter_upwards with t
    exact hDerivativeError n t
  have hCoordinateError : ∀ n, MemLp (fun t => E n t i) 2
      (volume.restrict (Icc a b)) := by
    intro n
    exact memLp_coordinate_of_memLp_vecEuclideanNorm_Icc
      (hVectorError n) (hCoordinateMeas n)
  have hScalarDerivativeError : ∀ n, MemLp
      (fun t => deriv (F n) t - g t) 2 (volume.restrict (Icc a b)) := by
    intro n
    apply (memLp_congr_ae ?_).mpr (hCoordinateError n)
    filter_upwards with t
    exact hDerivativeError n t
  have hVectorIntegrable : ∀ n,
      IntegrableOn (fun t => vecEuclideanNorm (E n t) ^ 2) (Icc a b) := by
    intro n
    simpa only [IntegrableOn] using (hVectorError n).integrable_sq
  have hCoordinateTendstoRaw : Tendsto
      (fun n => ∫ t in Icc a b, (E n t i) ^ 2) atTop (𝓝 0) := by
    have hNonneg : ∀ n, 0 ≤ ∫ t in Icc a b, (E n t i) ^ 2 := by
      intro n
      exact integral_nonneg fun _ => sq_nonneg _
    have hLe : ∀ n,
        (∫ t in Icc a b, (E n t i) ^ 2) ≤
          ∫ t in Icc a b, vecEuclideanNorm (E n t) ^ 2 := by
      intro n
      exact integral_coordinate_sq_le_integral_vecEuclideanNorm_sq_Icc
        (hVectorIntegrable n) (hCoordinateMeas n)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hVector (Eventually.of_forall hNonneg) ?_
    exact Eventually.of_forall hLe
  have hCoordinateTendsto : Tendsto
      (fun n => ∫ t in Icc a b,
        |deriv (F n) t - g t| ^ (2 : ℝ)) atTop (𝓝 0) := by
    simpa only [hDerivativeError, Real.rpow_two, sq_abs] using
      hCoordinateTendstoRaw
  exact uniformCauchySeqLimit_hasWeakDerivOnIoo_of_tendsto_setIntegral_sq_error
    hab hF hu hg hValueError hScalarDerivativeError hValue hCoordinateTendsto

end

end PDE
