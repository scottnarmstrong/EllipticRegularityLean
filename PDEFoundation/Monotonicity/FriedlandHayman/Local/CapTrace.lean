module

public import PDEFoundation.Monotonicity.FriedlandHayman.Local.Moment

/-!
# Friedland--Hayman: integrability on caps and the cap trace identity

Integrability of functions restricted to the cap about an arbitrary point `x`, and the trace
identity `∫_{cos ε < ⟪x, y⟫} |y - x|² dσ(y) = (D - 1) m_ε + m'_ε`, obtained by summing the second
moment identity over the coordinate vectors.
-/

@[expose] public section

open MeasureTheory

namespace PDE.FHLane

noncomputable section

namespace Local

variable {D : ℕ}

theorem measurableSet_cap_at (x : Sph D) (ε : ℝ) :
    MeasurableSet {y : Sph D | Real.cos ε < inner ℝ (x : HilbertVec D) (y : HilbertVec D)} :=
  (isOpen_lt continuous_const (continuous_const.inner continuous_subtype_val)).measurableSet

theorem integrable_cap_at (x : Sph D) {Ψ : Sph D → ℝ} (hΨ : Continuous Ψ) (ε : ℝ) :
    Integrable (fun y : Sph D => if Real.cos ε < inner ℝ (x : HilbertVec D) (y : HilbertVec D)
      then Ψ y else 0) (sphMeasure D) := by
  have h := (Symm.integrable_of_continuous hΨ).indicator (measurableSet_cap_at x ε)
  refine h.congr (ae_of_all _ fun y => ?_)
  by_cases hy : Real.cos ε < inner ℝ (x : HilbertVec D) (y : HilbertVec D)
  · simp [hy]
  · simp [hy]

end Local

open Local

/-- Trace identity on a cap. -/
theorem cap_trace {D : ℕ} (hD : 2 ≤ D) [NeZero D] (x : Sph D) {ε : ℝ} (hε : 0 < ε)
    (hε' : ε < Real.pi) :
    ∫ y : Sph D, (if Real.cos ε < inner ℝ (x : HilbertVec D) (y : HilbertVec D) then
        ‖(y : HilbertVec D) - x‖ ^ 2 else 0) ∂(sphMeasure D) =
      ((D : ℝ) - 1) * capMom D ε + capMom' D ε := by
  have hc : ∀ i : Fin D, Continuous fun y : Sph D =>
      inner ℝ (bas D i) ((y : HilbertVec D) - x) ^ 2 := fun i =>
    (continuous_const.inner (continuous_subtype_val.sub continuous_const)).pow 2
  have e : ∀ y : Sph D, (if Real.cos ε < inner ℝ (x : HilbertVec D) (y : HilbertVec D) then
      ‖(y : HilbertVec D) - x‖ ^ 2 else 0) =
      ∑ i : Fin D, (if Real.cos ε < inner ℝ (x : HilbertVec D) (y : HilbertVec D) then
        inner ℝ (bas D i) ((y : HilbertVec D) - x) ^ 2 else 0) := by
    intro y
    split_ifs
    · rw [PiLp.norm_sq_eq_of_L2]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_comm, inner_bas, Real.norm_eq_abs, sq_abs]
    · simp
  simp_rw [e]
  rw [integral_finsetSum _ fun i _ => integrable_cap_at x (hc i) ε]
  have h2 : ∀ i : Fin D, ∫ y : Sph D, (if Real.cos ε < inner ℝ (x : HilbertVec D) (y : HilbertVec D)
      then inner ℝ (bas D i) ((y : HilbertVec D) - x) ^ 2 else 0) ∂(sphMeasure D) =
      capMom D ε * (1 - ((x : HilbertVec D) i) ^ 2) + capMom' D ε * ((x : HilbertVec D) i) ^ 2 := by
    intro i
    rw [cap_second_moment hD x (bas D i) hε hε', norm_bas, real_inner_comm, inner_bas]
    ring
  simp_rw [h2]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib,
    sum_sq_sphere, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end

end PDE.FHLane
