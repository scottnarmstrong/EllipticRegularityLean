module

public import EllipticRegularity.Meyers.Cutoff
public import PDEFoundation.Geometry.AxisBox

/-!
# The cutoff hypothesis of the boundary reverse Hölder inequality

The smooth cube cutoff of `PDEFoundation.Sobolev.Cutoff.Cube` vanishes outside the closed cube of
half-side `3 r / 2`, a fact the public structure does not record; it is recovered here from the
explicit product formula.
-/

@[expose] public section

namespace PDE.MeyersRH

variable {d : ℕ}

theorem cubeCutoff_eq_zero_of_notMem {z : Vec d} {r : ℝ} (hr : 0 < r) {x : Vec d}
    (hx : x ∉ closedCenteredAxisCube z (3 * r / 2)) : (cubeCutoff z hr).toFun x = 0 := by
  have h : (cubeCutoff z hr).toFun x = ∏ i : Fin d,
      (axisBoxLowerTransition (z i - 2 * r) r (x i) *
        axisBoxUpperTransition (z i + 2 * r) r (x i)) := rfl
  rw [h]
  simp only [closedCenteredAxisCube, Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies,
    not_forall, not_and_or, not_le] at hx
  obtain ⟨i, hi⟩ := hx
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  rcases hi with hi | hi
  · rw [axisBoxLowerTransition_eq_zero_of_le_add_half_delta hr (by linarith), zero_mul]
  · rw [axisBoxUpperTransition_eq_zero_of_sub_half_delta_le hr (by linarith), mul_zero]

/-- The cutoff hypothesis `hcut` of `boundary_reverse_holder`, with `Kη = 32 d`. -/
theorem exists_boundary_cutoff (d : ℕ) : ∀ (z : Vec d) (r : ℝ), 0 < r → ∃ η : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧ (∀ x, 0 ≤ η x) ∧ (∀ x, η x ≤ 1) ∧
      (∀ x ∈ centeredAxisCube z r, η x = 1) ∧
      tsupport η ⊆ closedCenteredAxisCube z (3 * r / 2) ∧
      ∀ x, vecEuclideanNorm (classicalGradient η x) ≤ (32 * (d : ℝ)) / r := by
  intro z r hr
  let c := cubeCutoff z hr
  refine ⟨c.toFun, c.smooth, c.hasCompactSupport, c.nonneg, c.le_one, c.eq_one_on_inner, ?_,
    c.gradient_bound⟩
  refine closure_minimal ?_ (isClosed_closedCenteredAxisCube z _)
  intro x hx
  by_contra hxn
  exact hx (cubeCutoff_eq_zero_of_notMem hr hxn)

end PDE.MeyersRH
