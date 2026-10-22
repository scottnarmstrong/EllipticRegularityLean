module

public import PDEFoundation.Measure.GoodSquareRadius
public import PDEFoundation.Sobolev.Trace.SquareBoundaryOscillation
public import PDEFoundation.Sobolev.Trace.SquareIncrement

/-!
# Boundary oscillation from actual square-side energy

This module connects the one-dimensional increment estimates of a continuous
square trace to the actual four-side tangential energy.  The selected radius
is fixed throughout: the enlarged energy used for radius selection is not
substituted here.
-/

@[expose] public section

namespace PDE

open Filter MeasureTheory Set

noncomputable section

private theorem sq_abs_increment_le_two_mul_radius_mul_full_energy
    {a b r : ℝ} {v q : ℝ → ℝ}
    (hba : b - a = 2 * r)
    (hq : MemLp q 2 (volume.restrict (Icc a b)))
    (hordered : ∀ ⦃s t : ℝ⦄, s ∈ Icc a b → t ∈ Icc a b → s ≤ t →
      |v t - v s| ^ 2 ≤ (t - s) * ∫ z in Icc s t, |q z| ^ (2 : ℝ))
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    |v t - v s| ^ 2 ≤ 2 * r * ∫ z in Icc a b, |q z| ^ (2 : ℝ) := by
  have hqIntegrable : IntegrableOn (fun z => |q z| ^ (2 : ℝ)) (Icc a b) volume := by
    simpa only [Real.norm_eq_abs] using!
      hq.integrable_norm_rpow (by norm_num) (by norm_num)
  have hfullNonneg : 0 ≤ ∫ z in Icc a b, |q z| ^ (2 : ℝ) := by
    exact integral_nonneg fun z => Real.rpow_nonneg (abs_nonneg (q z)) _
  rcases le_total s t with hst | hts
  · have hsmall :
        ∫ z in Icc s t, |q z| ^ (2 : ℝ) ≤ ∫ z in Icc a b, |q z| ^ (2 : ℝ) := by
      refine setIntegral_mono_set hqIntegrable ?_ ?_
      · exact Eventually.of_forall fun z => Real.rpow_nonneg (abs_nonneg (q z)) _
      · exact Eventually.of_forall fun z hz => Icc_subset_Icc hs.1 ht.2 hz
    calc
      |v t - v s| ^ 2 ≤ (t - s) * ∫ z in Icc s t, |q z| ^ (2 : ℝ) :=
        hordered hs ht hst
      _ ≤ (t - s) * ∫ z in Icc a b, |q z| ^ (2 : ℝ) :=
        mul_le_mul_of_nonneg_left hsmall (sub_nonneg.mpr hst)
      _ ≤ (b - a) * ∫ z in Icc a b, |q z| ^ (2 : ℝ) := by
        exact mul_le_mul_of_nonneg_right (sub_le_sub ht.2 hs.1) hfullNonneg
      _ = 2 * r * ∫ z in Icc a b, |q z| ^ (2 : ℝ) := by rw [hba]
  · have hreverse := hordered ht hs hts
    simpa only [abs_sub_comm] using
      (show |v s - v t| ^ 2 ≤ 2 * r * ∫ z in Icc a b, |q z| ^ (2 : ℝ) from by
        have hsmall :
            ∫ z in Icc t s, |q z| ^ (2 : ℝ) ≤ ∫ z in Icc a b, |q z| ^ (2 : ℝ) := by
          refine setIntegral_mono_set hqIntegrable ?_ ?_
          · exact Eventually.of_forall fun z => Real.rpow_nonneg (abs_nonneg (q z)) _
          · exact Eventually.of_forall fun z hz => Icc_subset_Icc ht.1 hs.2 hz
        calc
          |v s - v t| ^ 2 ≤ (s - t) * ∫ z in Icc t s, |q z| ^ (2 : ℝ) := hreverse
          _ ≤ (s - t) * ∫ z in Icc a b, |q z| ^ (2 : ℝ) :=
            mul_le_mul_of_nonneg_left hsmall (sub_nonneg.mpr hts)
          _ ≤ (b - a) * ∫ z in Icc a b, |q z| ^ (2 : ℝ) := by
            exact mul_le_mul_of_nonneg_right (sub_le_sub hs.2 ht.1) hfullNonneg
          _ = 2 * r * ∫ z in Icc a b, |q z| ^ (2 : ℝ) := by rw [hba])

/-- The continuous four-side trace at a positive radius has squared boundary
oscillation at most eight times the radius times its actual tangential
energy.  All four energy terms are the closed-side integrals appearing in
`squareSideTangentialEnergy`; no enlarged-radius quantity enters this bound. -/
theorem SquareSideTrace.hasBoundarySqOscillationLE_actual_tangential_energy
    {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2} {x₀ : Vec 2} {ρ : ℝ}
    (T : SquareSideTrace u g x₀ ρ) (hρ : 0 < ρ) :
    T.HasBoundarySqOscillationLE
      (8 * ρ * squareSideTangentialEnergy g x₀ ρ) := by
  let Eright : ℝ := ∫ z in Icc (x₀ 1 - ρ) (x₀ 1 + ρ),
    |squareLoopRightTangentialRestriction g x₀ ρ z| ^ (2 : ℝ)
  let Etop : ℝ := ∫ z in Icc (x₀ 0 - ρ) (x₀ 0 + ρ),
    |squareLoopTopTangentialRestriction g x₀ ρ z| ^ (2 : ℝ)
  let Eleft : ℝ := ∫ z in Icc (x₀ 1 - ρ) (x₀ 1 + ρ),
    |squareLoopLeftTangentialRestriction g x₀ ρ z| ^ (2 : ℝ)
  let Ebottom : ℝ := ∫ z in Icc (x₀ 0 - ρ) (x₀ 0 + ρ),
    |squareLoopBottomTangentialRestriction g x₀ ρ z| ^ (2 : ℝ)
  have hEright : 0 ≤ Eright := by
    dsimp only [Eright]
    exact integral_nonneg fun z => Real.rpow_nonneg (abs_nonneg _) _
  have hEtop : 0 ≤ Etop := by
    dsimp only [Etop]
    exact integral_nonneg fun z => Real.rpow_nonneg (abs_nonneg _) _
  have hEleft : 0 ≤ Eleft := by
    dsimp only [Eleft]
    exact integral_nonneg fun z => Real.rpow_nonneg (abs_nonneg _) _
  have hEbottom : 0 ≤ Ebottom := by
    dsimp only [Ebottom]
    exact integral_nonneg fun z => Real.rpow_nonneg (abs_nonneg _) _
  have hright : T.HasSideSqIncrementLE .right Eright := by
    intro s t hs ht
    change |T.right t - T.right s| ^ 2 ≤ 2 * ρ * Eright
    exact sq_abs_increment_le_two_mul_radius_mul_full_energy
      (by ring) T.rightTangentialMemL2
      (fun {s t} hs ht hst => T.right_sq_abs_increment_le hρ hs ht hst) hs ht
  have htop : T.HasSideSqIncrementLE .top Etop := by
    intro s t hs ht
    change |T.top t - T.top s| ^ 2 ≤ 2 * ρ * Etop
    exact sq_abs_increment_le_two_mul_radius_mul_full_energy
      (by ring) T.topTangentialMemL2
      (fun {s t} hs ht hst => T.top_sq_abs_increment_le hρ hs ht hst) hs ht
  have hleft : T.HasSideSqIncrementLE .left Eleft := by
    intro s t hs ht
    change |T.left t - T.left s| ^ 2 ≤ 2 * ρ * Eleft
    exact sq_abs_increment_le_two_mul_radius_mul_full_energy
      (by ring) T.leftTangentialMemL2
      (fun {s t} hs ht hst => T.left_sq_abs_increment_le hρ hs ht hst) hs ht
  have hbottom : T.HasSideSqIncrementLE .bottom Ebottom := by
    intro s t hs ht
    change |T.bottom t - T.bottom s| ^ 2 ≤ 2 * ρ * Ebottom
    exact sq_abs_increment_le_two_mul_radius_mul_full_energy
      (by ring) T.bottomTangentialMemL2
      (fun {s t} hs ht hst => T.bottom_sq_abs_increment_le hρ hs ht hst) hs ht
  have hboundary := T.hasBoundarySqOscillationLE_of_sideSqIncrementLE hρ.le
    hEright hEtop hEleft hEbottom hright htop hleft hbottom
  have henergy : Eright + Etop + Eleft + Ebottom = squareSideTangentialEnergy g x₀ ρ := by
    dsimp only [Eright, Etop, Eleft, Ebottom, squareSideTangentialEnergy,
      squareLoopRightTangentialRestriction, squareLoopTopTangentialRestriction,
      squareLoopLeftTangentialRestriction, squareLoopBottomTangentialRestriction,
      squareLoopRightSide, squareLoopTopSide, squareLoopLeftSide, squareLoopBottomSide]
    simp only [Real.rpow_two, sq_abs]
    ring
  rw [henergy] at hboundary
  exact hboundary

end

end PDE
