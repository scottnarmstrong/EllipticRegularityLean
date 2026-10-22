module

public import EllipticRegularity.Parabolic.NashLower.Extend

/-!
# One local Harnack step for a solution on a long cylinder

The local Harnack inequality (as an internal predicate whose body is the inner statement of
`parabLocalHarnack`, for a fixed constant `H`) is applied to the restriction of a
nonnegative solution on `ℝ^d × [s,T]` to the cylinder
`(τ - 3θ/2, τ + 5θ/4] × B_{√(2θ)}((z+z')/2)`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE.Parabolic.NashLower

/-- The inner statement of `PDE.parabLocalHarnack` for a fixed `H`. -/
def LocalHarnackAt (d : ℕ) (Lam H : ℝ) : Prop :=
  ∀ (a : ParCoeffField d) (τ θ : ℝ), 0 < θ → ∀ z z' : Vec d,
      euclideanSqDist z z' ≤ θ / 4 →
      IsParabolicCoeff 1 Lam a
        (euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (2 * θ)))
        (Ioc (τ - 3 * θ / 2) (τ + 5 * θ / 4)) →
      ∀ u : ParH1Function (euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (2 * θ)))
        (Ioc (τ - 3 * θ / 2) (τ + 5 * θ / 4)),
      IsParabolicWeakSolution a (euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (2 * θ)))
        (Ioc (τ - 3 * θ / 2) (τ + 5 * θ / 4)) u →
      (∀ᵐ w ∂(volume.restrict (euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (2 * θ)) ×ˢ
        Ioc (τ - 3 * θ / 2) (τ + 5 * θ / 4))), 0 ≤ u.toFun w) →
        essSup (fun x : Vec d => ENNReal.ofReal (u.toFun (x, τ)))
            (volume.restrict (euclideanBall z (Real.sqrt θ / 4))) ≤
          ENNReal.ofReal H *
            essInf (fun x : Vec d => ENNReal.ofReal (u.toFun (x, τ + θ)))
              (volume.restrict (euclideanBall z' (Real.sqrt θ / 4)))

/-- One Harnack step for a nonnegative solution on `ℝ^d × [s,T]`. -/
theorem harnack_step {d : ℕ} {Lam H : ℝ} (hH : LocalHarnackAt d Lam H) {a : ParCoeffField d}
    {s T : ℝ} (hcoef : IsParabolicCoeff 1 Lam a univ (Icc s T))
    (w : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hw : IsParabolicWeakSolution a univ (Icc s T) w)
    (hpos : ∀ τ ∈ Icc s T, ∀ᵐ x : Vec d, 0 ≤ w.toFun (x, τ)) {τ θ : ℝ} (hθ : 0 < θ)
    (z z' : Vec d) (hzz : euclideanSqDist z z' ≤ θ / 4) (h1 : s ≤ τ - 3 * θ / 2)
    (h2 : τ + 5 * θ / 4 ≤ T) :
    essSup (fun x : Vec d => ENNReal.ofReal (w.toFun (x, τ)))
        (volume.restrict (euclideanBall z (Real.sqrt θ / 4))) ≤
      ENNReal.ofReal H *
        essInf (fun x : Vec d => ENNReal.ofReal (w.toFun (x, τ + θ)))
          (volume.restrict (euclideanBall z' (Real.sqrt θ / 4))) := by
  have hJ : Ioc (τ - 3 * θ / 2) (τ + 5 * θ / 4) ⊆ Icc s T :=
    Ioc_subset_Icc_self.trans (Icc_subset_Icc h1 h2)
  have hB := subset_univ (euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (2 * θ)))
  refine hH a τ θ hθ z z' hzz (isParabolicCoeff_mono hcoef hB hJ)
    (restrictParH1 hB hJ w) (isParabolicWeakSolution_restrict hB hJ hw) ?_
  refine ae_nonneg_of_ae_slices (F := w.toFun) measurableSet_Ioc ?_ (fun τ' hτ' => hpos τ' (hJ hτ'))
  exact w.memL2.aestronglyMeasurable.mono_measure
    (Measure.restrict_mono (prod_mono hB hJ) le_rfl)

end PDE.Parabolic.NashLower
