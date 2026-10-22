module

public import PDEFoundation.Measure.ForcingScale

@[expose] public section

namespace PDE
open MeasureTheory Set
open scoped ENNReal

/-- Euclidean magnitude commutes exactly with the literal vector indicator. -/
theorem vecEuclideanNorm_indicator {d : ℕ} (U : Set (Vec d))
    (F : Vec d → Vec d) :
    (fun x => vecEuclideanNorm (U.indicator F x)) =
      U.indicator (fun x => vecEuclideanNorm (F x)) := by
  classical
  funext x
  by_cases hx : x ∈ U
  · simp only [Set.indicator_of_mem hx]
  · simp only [Set.indicator_of_notMem hx, vecEuclideanNorm, vecNormSq, vecDot, Pi.zero_apply,
      zero_mul, Finset.sum_const_zero, Real.sqrt_zero]

/-- Coordinate measurability on the source domain yields global coordinate
measurability of its literal zero extension. -/
theorem aestronglyMeasurable_indicator_coordinate {d : ℕ}
    {U : Set (Vec d)} (hU : MeasurableSet U) (F : Vec d → Vec d)
    (i : Fin d) (hF : AEStronglyMeasurable (fun x => F x i) (volumeOn U)) :
    AEStronglyMeasurable (fun x => U.indicator F x i) volume := by
  have hcoord : (fun x => U.indicator F x i) = U.indicator (fun x => F x i) := by
    classical
    funext x
    by_cases hx : x ∈ U
    · simp only [Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_notMem hx, Pi.zero_apply]
  rw [hcoord]
  exact (aestronglyMeasurable_indicator_iff hU).mpr hF

/-- The zero-extension norm is exactly the original restricted forcing norm. -/
theorem eLpNorm_vecEuclideanNorm_indicator {d : ℕ}
    {U : Set (Vec d)} (hU : MeasurableSet U) (F : Vec d → Vec d) (p : ENNReal) :
    eLpNorm (fun x => vecEuclideanNorm (U.indicator F x)) p volume =
      eLpNorm (fun x => vecEuclideanNorm (F x)) p (volumeOn U) := by
  rw [vecEuclideanNorm_indicator]
  exact eLpNorm_indicator_eq_eLpNorm_restrict hU

/-- Actual domain Lp forcing gives global Lp magnitude of the zero extension. -/
theorem memLp_vecEuclideanNorm_indicator {d : ℕ}
    {U : Set (Vec d)} (hU : MeasurableSet U) (F : Vec d → Vec d) {p : ENNReal}
    (hF : MemLp (fun x => vecEuclideanNorm (F x)) p (volumeOn U)) :
    MemLp (fun x => vecEuclideanNorm (U.indicator F x)) p volume := by
  rw [vecEuclideanNorm_indicator]
  exact (memLp_indicator_iff_restrict hU).mpr hF

end PDE
