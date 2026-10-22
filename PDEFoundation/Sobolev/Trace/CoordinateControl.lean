module

public import PDEFoundation.Ambient.EuclideanNorm
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Coordinate control for vector-valued traces

The explicit Euclidean magnitude of a native `Vec d` controls each coordinate
with constant one.  Coordinate measurability is kept as an explicit
hypothesis: measurability of a magnitude alone cannot recover the
measurability of a coordinate.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open Filter MeasureTheory Set

noncomputable section

/-- On a restricted interval, each coordinate has `L²` seminorm at most the
explicit Euclidean-magnitude seminorm, with constant one, once that coordinate
is known to be a.e. strongly measurable. -/
theorem eLpNorm_coordinate_le_eLpNorm_vecEuclideanNorm_Icc
    {d : ℕ} (G : ℝ → Vec d) (i : Fin d) (a b : ℝ)
    (hGi : AEStronglyMeasurable (fun t => G t i)
      (volume.restrict (Icc a b))) :
    eLpNorm (fun t => G t i) 2 (volume.restrict (Icc a b)) ≤
      eLpNorm (fun t => vecEuclideanNorm (G t)) 2
        (volume.restrict (Icc a b)) := by
  apply eLpNorm_mono hGi
  intro t
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (vecEuclideanNorm_nonneg _)] using
    abs_apply_le_vecEuclideanNorm (G t) i

/-- `L²` control of an explicit Euclidean magnitude gives `L²` control of a
coordinate on the same restricted interval, once that coordinate is known to
be a.e. strongly measurable. -/
theorem memLp_coordinate_of_memLp_vecEuclideanNorm_Icc
    {d : ℕ} {G : ℝ → Vec d} {i : Fin d} {a b : ℝ}
    (hG : MemLp (fun t => vecEuclideanNorm (G t)) 2
      (volume.restrict (Icc a b)))
    (hGi : AEStronglyMeasurable (fun t => G t i)
      (volume.restrict (Icc a b))) :
    MemLp (fun t => G t i) 2 (volume.restrict (Icc a b)) := by
  apply hG.of_le hGi
  filter_upwards with t
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (vecEuclideanNorm_nonneg _)] using
    abs_apply_le_vecEuclideanNorm (G t) i

/-- The square of each coordinate is integrable on a closed interval under
`L²` control of the explicit Euclidean magnitude. -/
theorem integrableOn_coordinate_sq_of_memLp_vecEuclideanNorm_Icc
    {d : ℕ} {G : ℝ → Vec d} {i : Fin d} {a b : ℝ}
    (hG : MemLp (fun t => vecEuclideanNorm (G t)) 2
      (volume.restrict (Icc a b)))
    (hGi : AEStronglyMeasurable (fun t => G t i)
      (volume.restrict (Icc a b))) :
    IntegrableOn (fun t => G t i ^ 2) (Icc a b) := by
  simpa only [IntegrableOn] using
    (memLp_coordinate_of_memLp_vecEuclideanNorm_Icc hG hGi).integrable_sq

/-- The integral of a squared coordinate is bounded by the integral of the
squared explicit Euclidean magnitude, with constant one.  The coordinate
measurability hypothesis ensures that the left integral is genuinely
integrable, rather than relying on the default value of a nonintegrable
Bochner integral. -/
theorem integral_coordinate_sq_le_integral_vecEuclideanNorm_sq_Icc
    {d : ℕ} {G : ℝ → Vec d} {i : Fin d} {a b : ℝ}
    (hG : IntegrableOn (fun t => vecEuclideanNorm (G t) ^ 2) (Icc a b))
    (hGi : AEStronglyMeasurable (fun t => G t i)
      (volume.restrict (Icc a b))) :
    (∫ t in Icc a b, G t i ^ 2) ≤
      ∫ t in Icc a b, vecEuclideanNorm (G t) ^ 2 := by
  have hGiSq : AEStronglyMeasurable (fun t => G t i ^ 2)
      (volume.restrict (Icc a b)) :=
    hGi.pow 2
  have hCoordinate : IntegrableOn (fun t => G t i ^ 2) (Icc a b) := by
    apply hG.mono' hGiSq
    filter_upwards with t
    calc
      ‖G t i ^ 2‖ = G t i ^ 2 := Real.norm_of_nonneg (sq_nonneg _)
      _ ≤ vecNormSq (G t) := sq_apply_le_vecNormSq (G t) i
      _ = vecEuclideanNorm (G t) ^ 2 := (vecEuclideanNorm_sq _).symm
  apply integral_mono hCoordinate hG
  intro t
  simpa only [vecEuclideanNorm_sq] using sq_apply_le_vecNormSq (G t) i

/-- Vanishing squared explicit-Euclidean trace error on a closed interval
forces vanishing squared error in each coordinate. -/
theorem tendsto_integral_coordinate_sq_sub_zero_of_tendsto_integral_vecEuclideanNorm_sq_sub_zero_Icc
    {d : ℕ} {F : ℕ → ℝ → Vec d} {G : ℝ → Vec d}
    {i : Fin d} {a b : ℝ}
    (hMeas : ∀ n, AEStronglyMeasurable (fun t => F n t i - G t i)
      (volume.restrict (Icc a b)))
    (hIntegrable : ∀ n,
      IntegrableOn (fun t => vecEuclideanNorm (F n t - G t) ^ 2) (Icc a b))
    (hTendsto : Tendsto (fun n =>
      ∫ t in Icc a b, vecEuclideanNorm (F n t - G t) ^ 2)
      atTop (nhds 0)) :
    Tendsto (fun n => ∫ t in Icc a b, (F n t i - G t i) ^ 2)
      atTop (nhds 0) := by
  have hCoordinateNonneg : ∀ n, 0 ≤
      ∫ t in Icc a b, (F n t i - G t i) ^ 2 := by
    intro n
    exact integral_nonneg fun _ => sq_nonneg _
  have hCoordinateLe : ∀ n,
      (∫ t in Icc a b, (F n t i - G t i) ^ 2) ≤
        ∫ t in Icc a b, vecEuclideanNorm (F n t - G t) ^ 2 := by
    intro n
    have hMeas' : AEStronglyMeasurable (fun t => (F n t - G t) i)
        (volume.restrict (Icc a b)) := by
      simpa only [Pi.sub_apply] using hMeas n
    simpa only [Pi.sub_apply] using
      integral_coordinate_sq_le_integral_vecEuclideanNorm_sq_Icc
        (hIntegrable n) hMeas'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hTendsto
    (Eventually.of_forall hCoordinateNonneg) ?_
  filter_upwards with n
  exact hCoordinateLe n

end

end PDE
