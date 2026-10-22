module

public import EllipticRegularity.Parabolic.NashKernel.OperatorBounds
public import EllipticRegularity.Parabolic.NashKernel.GeometryLebesgue

/-!
# Cube averages of a representing kernel

Here `Metric.closedBall` on `Vec d` is used on purpose: it is a cube for the supremum norm, and
cubes are the sets of the Lebesgue differentiation theorem.  For a jointly measurable bounded `P`
representing `cauchyOp` on indicators, the integral of `P` over the product cube
`closedBall (x, y) δ` equals `∫ 1_{B_x} · cauchyOp (1_{B_y})`.
-/

@[expose] public section

namespace PDE.Parabolic.NashKernel

open MeasureTheory Metric Set

variable {d : ℕ}

/-- A jointly measurable bounded function on `Vec d × Vec d` is locally integrable. -/
theorem locallyIntegrable_of_bounded {F : Vec d × Vec d → ℝ} {M : ℝ} (hF : Measurable F)
    (hM : ∀ q, |F q| ≤ M) : LocallyIntegrable F volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  refine Measure.integrableOn_of_bounded (M := M) hK.measure_lt_top.ne
    hF.aestronglyMeasurable (Filter.Eventually.of_forall fun q => ?_)
  simpa [Real.norm_eq_abs] using hM q

/-- Indicator of a sup-cube is in `L¹`. -/
theorem integrable_indicator_closedBall (x : Vec d) (δ : ℝ) :
    Integrable ((closedBall x δ).indicator (1 : Vec d → ℝ)) volume :=
  (integrable_indicator_iff measurableSet_closedBall).2
    (integrableOn_const (isCompact_closedBall x δ).measure_lt_top.ne)

/-- Indicator of a sup-cube is in `L²`. -/
theorem memLp_indicator_closedBall (x : Vec d) (δ : ℝ) :
    MemLp ((closedBall x δ).indicator (1 : Vec d → ℝ)) 2 volume :=
  memLp_indicator_const 2 measurableSet_closedBall 1
    (Or.inr (isCompact_closedBall x δ).measure_lt_top.ne)

/-- `∫ |1_{B}| = vol B` for a sup-cube. -/
theorem integral_abs_indicator_closedBall (x : Vec d) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∫ z, |(closedBall x δ).indicator (1 : Vec d → ℝ) z| = (2 * δ) ^ d := by
  have h : (fun z => |(closedBall x δ).indicator (1 : Vec d → ℝ) z|) =
      (closedBall x δ).indicator (1 : Vec d → ℝ) := by
    funext z
    by_cases hz : z ∈ closedBall x δ <;> simp [hz]
  rw [h, integral_indicator_one measurableSet_closedBall, measureReal_def,
    PDE.NashKernelGeometry.volume_closedBall_vec x hδ,
    ENNReal.toReal_ofReal (pow_nonneg (by linarith) _)]

/-- `∫ 1_B = vol B`. -/
theorem integral_indicator_closedBall (x : Vec d) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∫ z, (closedBall x δ).indicator (1 : Vec d → ℝ) z = (2 * δ) ^ d := by
  rw [integral_indicator_one measurableSet_closedBall, measureReal_def,
    PDE.NashKernelGeometry.volume_closedBall_vec x hδ,
    ENNReal.toReal_ofReal (pow_nonneg (by linarith) _)]

/-- Fubini plus the representation hypothesis on a product cube. -/
theorem setIntegral_closedBall_prod_eq {a : ParCoeffField d} {s t : ℝ} {P : Vec d → Vec d → ℝ}
    {M : ℝ} (hP : Measurable (Function.uncurry P)) (hM : ∀ x y, |P x y| ≤ M)
    (hrep : ∀ B : Set (Vec d), MeasurableSet B → Bornology.IsBounded B →
      cauchyOp a s t (B.indicator 1) =ᵐ[volume] fun x => ∫ y in B, P x y)
    (x y : Vec d) (δ : ℝ) :
    ∫ q in closedBall (x, y) δ, Function.uncurry P q =
      ∫ z, (closedBall x δ).indicator (1 : Vec d → ℝ) z *
        cauchyOp a s t ((closedBall y δ).indicator 1) z := by
  have hloc := locallyIntegrable_of_bounded hP (M := M) (fun q => hM q.1 q.2)
  have hint : IntegrableOn (Function.uncurry P) (closedBall x δ ×ˢ closedBall y δ)
      ((volume : Measure (Vec d)).prod volume) := by
    have := hloc.integrableOn_isCompact (isCompact_closedBall (x, y) δ)
    rwa [PDE.NashKernelGeometry.closedBall_prod] at this
  rw [PDE.NashKernelGeometry.closedBall_prod, PDE.NashKernelGeometry.volume_prod_eq,
    setIntegral_prod _ hint]
  have hae := hrep (closedBall y δ) measurableSet_closedBall (isBounded_closedBall)
  have step : ∫ x' in closedBall x δ, ∫ y' in closedBall y δ, Function.uncurry P (x', y') =
      ∫ x' in closedBall x δ, cauchyOp a s t ((closedBall y δ).indicator 1) x' := by
    refine setIntegral_congr_ae measurableSet_closedBall ?_
    filter_upwards [hae] with x' hx' _ using hx'.symm
  rw [step, ← integral_indicator measurableSet_closedBall]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ closedBall x δ <;> simp [hz]

end PDE.Parabolic.NashKernel
