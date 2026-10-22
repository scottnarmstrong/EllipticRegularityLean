module

public import EllipticRegularity.Ch4.Meyers.Bounds
public import EllipticRegularity.Ch4.Meyers.AxisWeakGradient

/-!
# The profiles as `H¹` functions on the unit ball
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4Meyers

open MeasureTheory Set

variable {d : ℕ} {w : Fin d → ℝ}

theorem isFiniteMeasure_restrict_unitBall :
    IsFiniteMeasure (volume.restrict (euclideanBall (0 : Vec d) 1)) :=
  isFiniteMeasure_restrict.mpr (volume_euclideanBall_ne_top (0 : Vec d) zero_le_one)

theorem memLp_prof (hw : ∀ i, w i = 0 ∨ w i = 1) {k : Fin d} (hk : w k = 1) {γ : ℝ}
    (hγ0 : -1 / 2 < γ) (p : ℝ≥0∞) :
    MemLp (prof w γ k) p (volume.restrict (euclideanBall (0 : Vec d) 1)) := by
  have := isFiniteMeasure_restrict_unitBall (d := d)
  refine MemLp.of_bound (measurable_prof w γ k).aestronglyMeasurable 1 ?_
  refine (ae_restrict_iff' (measurableSet_euclideanBall _ _)).mpr (ae_of_all _ fun x hx => ?_)
  simpa [Real.norm_eq_abs] using abs_prof_le_one hw hk hγ0 hx

theorem memLp_profGrad (hw : ∀ i, w i = 0 ∨ w i = 1) {i0 i1 : Fin d} (hi : i0 ≠ i1)
    (h0 : w i0 = 1) (h1 : w i1 = 1) {k : Fin d} (hk : w k = 1) {γ : ℝ}
    (hγ0 : -1 / 2 < γ) (hγ1 : γ ≤ 0) (i : Fin d) :
    MemLp (fun x => profGrad w γ k x i) 2 (volume.restrict (euclideanBall (0 : Vec d) 1)) :=
  memLp_two_of_abs_le_rpow hw hi h0 h1 hγ0 hγ1 (measurable_profGrad_apply w γ k i)
    (C := 1 + |2 * γ|) (ae_of_all _ fun x => abs_rpow_term_le hw hk (2 * γ) γ x i)

theorem memLp_profFlux (hw : ∀ i, w i = 0 ∨ w i = 1) {i0 i1 : Fin d} (hi : i0 ≠ i1)
    (h0 : w i0 = 1) (h1 : w i1 = 1) {k : Fin d} (hk : w k = 1) {γ : ℝ}
    (hγ0 : -1 / 2 < γ) (hγ1 : γ ≤ 0) (Λ : ℝ) (i : Fin d) :
    MemLp (fun x => profFlux w Λ γ k x i) 2 (volume.restrict (euclideanBall (0 : Vec d) 1)) :=
  memLp_two_of_abs_le_rpow hw hi h0 h1 hγ0 hγ1 (measurable_profFlux_apply w Λ γ k i)
    (C := 1 + |Λ - 1 + 2 * γ * Λ|) (ae_of_all _ fun x => abs_rpow_term_le hw hk _ γ x i)

theorem hasWeakGradientOn_prof (hw : ∀ i, w i = 0 ∨ w i = 1) {i0 i1 : Fin d} (hi : i0 ≠ i1)
    (h0 : w i0 = 1) (h1 : w i1 = 1) {k : Fin d} (hk : w k = 1) {γ : ℝ}
    (hγ0 : -1 / 2 < γ) (hγ1 : γ ≤ 0) :
    HasWeakGradientOn (euclideanBall (0 : Vec d) 1) (prof w γ k) (profGrad w γ k) := by
  refine hasWeakGradientOn_of_axis hw hi h0 h1 (isOpen_euclideanBall _ _)
    (memLp_prof hw hk hγ0 2) (memLp_profGrad hw hi h0 h1 hk hγ0 hγ1) ?_ ?_
  · intro x hx
    have hpos : 0 < axisSq w x :=
      lt_of_le_of_ne (axisSq_nonneg hw x) (fun h => hx.2 h.symm)
    exact (contDiffAt_prof hpos γ k 1).contDiffWithinAt
  · intro x hx
    have hpos : 0 < axisSq w x :=
      lt_of_le_of_ne (axisSq_nonneg hw x) (fun h => hx.2 h.symm)
    exact classicalGradient_prof hw hpos γ k

/-- The profile `s^γ x_k` as an `H¹` function on the unit ball, with the explicit gradient. -/
noncomputable def profH1 (hw : ∀ i, w i = 0 ∨ w i = 1) {i0 i1 : Fin d} (hi : i0 ≠ i1)
    (h0 : w i0 = 1) (h1 : w i1 = 1) {k : Fin d} (hk : w k = 1) {γ : ℝ}
    (hγ0 : -1 / 2 < γ) (hγ1 : γ ≤ 0) : H1Function (euclideanBall (0 : Vec d) 1) where
  toFun := prof w γ k
  grad := profGrad w γ k
  memL2 := memLp_prof hw hk hγ0 2
  gradMemL2 := memLp_profGrad hw hi h0 h1 hk hγ0 hγ1
  hasWeakGradient := hasWeakGradientOn_prof hw hi h0 h1 hk hγ0 hγ1

end PDE.Ch4Meyers
