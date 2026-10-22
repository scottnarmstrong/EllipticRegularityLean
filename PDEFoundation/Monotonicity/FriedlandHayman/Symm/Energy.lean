module

public import PDEFoundation.Monotonicity.FriedlandHayman.Symm.Polarization
public import PDEFoundation.Monotonicity.FriedlandHayman.Symm.Split

/-!
# Friedland--Hayman: nonlocal cap energies and polarization

The nonlocal energy `nlEnergy ε g` with the cap kernel of angular radius `ε`, the two-point
inequality, the monotonicity `nlEnergy ε (polarize u g) ≤ nlEnergy ε g`, and the sup-norm
continuity of `nlEnergy ε`.
-/

@[expose] public section

open MeasureTheory Metric Set

namespace PDE.FHLane

noncomputable section

variable {D : ℕ}

/-- Nonlocal energy with the cap kernel of angular radius `ε`. -/
noncomputable def nlEnergy (ε : ℝ) (g : C(Sph D, ℝ)) : ℝ :=
  ∫ x, ∫ y, (if Real.cos ε < inner ℝ (x : HilbertVec D) (y : HilbertVec D) then (g x - g y) ^ 2 else 0)
    ∂(sphMeasure D) ∂(sphMeasure D)

namespace Symm

/-- The integrand of `nlEnergy`. -/
def kern (ε : ℝ) (g : C(Sph D, ℝ)) (x y : Sph D) : ℝ :=
  if Real.cos ε < inner ℝ (x : HilbertVec D) (y : HilbertVec D) then (g x - g y) ^ 2 else 0

theorem nlEnergy_eq (ε : ℝ) (g : C(Sph D, ℝ)) :
    nlEnergy ε g = ∫ x, ∫ y, kern ε g x y ∂(sphMeasure D) ∂(sphMeasure D) := rfl

theorem measurable_kern (ε : ℝ) (g : C(Sph D, ℝ)) :
    Measurable (fun p : Sph D × Sph D => kern ε g p.1 p.2) := by
  unfold kern
  refine Measurable.ite ?_ (((g.continuous.measurable.comp measurable_fst).sub
    (g.continuous.measurable.comp measurable_snd)).pow_const 2) measurable_const
  exact (isOpen_lt continuous_const
    (continuous_subtype_val.comp continuous_fst |>.inner
      (continuous_subtype_val.comp continuous_snd))).measurableSet

theorem abs_sub_le_two_norm (g : C(Sph D, ℝ)) (x y : Sph D) : |g x - g y| ≤ 2 * ‖g‖ := by
  have h1 := g.norm_coe_le_norm x
  have h2 := g.norm_coe_le_norm y
  rw [Real.norm_eq_abs, abs_le] at h1 h2
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem abs_kern_le (ε : ℝ) (g : C(Sph D, ℝ)) (x y : Sph D) : |kern ε g x y| ≤ (2 * ‖g‖) ^ 2 := by
  unfold kern
  have h := abs_sub_le_two_norm g x y
  split_ifs
  · rw [abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq' (by linarith [(abs_le.1 h).1]) (abs_le.1 h).2
  · simp only [abs_zero]; positivity

theorem two_point_le (a b c d : ℝ) :
    (max a b - max c d) ^ 2 + (min a b - min c d) ^ 2 ≤ (a - c) ^ 2 + (b - d) ^ 2 := by
  rcases le_total a b with h1 | h1 <;> rcases le_total c d with h2 | h2 <;>
    simp only [h1, h2, max_eq_right, max_eq_left, min_eq_left, min_eq_right] <;>
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]

theorem two_point_eq (a b c d : ℝ) :
    (max a b - max c d) ^ 2 + (min a b - min c d) ^ 2 +
      ((max a b - min c d) ^ 2 + (min a b - max c d) ^ 2) =
    (a - c) ^ 2 + (b - d) ^ 2 + ((a - d) ^ 2 + (b - c) ^ 2) := by
  rcases le_total a b with h1 | h1 <;> rcases le_total c d with h2 | h2 <;>
    simp only [h1, h2, max_eq_right, max_eq_left, min_eq_left, min_eq_right] <;> ring

variable (u : HilbertVec D) (hu : ‖u‖ = 1)

theorem quad_kern_polarize_le (ε : ℝ) (g : C(Sph D, ℝ)) {x y : Sph D} (hx : x ∈ halfPos u)
    (hy : y ∈ halfPos u) :
    quad u hu (kern ε (polarize u hu g)) x y ≤ quad u hu (kern ε g) x y := by
  have hx' : 0 < inner ℝ (x : HilbertVec D) u := hx
  have hy' : 0 < inner ℝ (y : HilbertVec D) u := hy
  have hst := inner_sub_inner_rho u hu x y
  have hord : inner ℝ (x : HilbertVec D) (rho u hu y : HilbertVec D) ≤
      inner ℝ (x : HilbertVec D) (y : HilbertVec D) := by
    nlinarith [mul_pos hx' hy']
  have h1 := two_point_le (g x) (g (rho u hu x)) (g y) (g (rho u hu y))
  have h2 := two_point_eq (g x) (g (rho u hu x)) (g y) (g (rho u hu y))
  unfold quad kern
  rw [polarize_of_pos u hu g hx', polarize_of_pos u hu g hy', polarize_rho_of_pos u hu g hx',
    polarize_rho_of_pos u hu g hy', inner_rho_rho, inner_rho_left]
  split_ifs <;> linarith

theorem nlEnergy_polarize_le' (ε : ℝ) (g : C(Sph D, ℝ)) :
    nlEnergy ε (polarize u hu g) ≤ nlEnergy ε g := by
  rw [nlEnergy_eq, nlEnergy_eq,
    iterated_split (u := u) (hu := hu) (measurable_kern ε _) (abs_kern_le ε (polarize u hu g)),
    iterated_split (u := u) (hu := hu) (measurable_kern ε _) (abs_kern_le ε g)]
  have hm : ∀ h : C(Sph D, ℝ), Measurable
      ((halfPos u ×ˢ halfPos u).indicator fun p : Sph D × Sph D => quad u hu (kern ε h) p.1 p.2) :=
    fun h => (measurable_quad (measurable_kern ε h)).indicator
      ((measurableSet_halfPos u).prod (measurableSet_halfPos u))
  have hb : ∀ h : C(Sph D, ℝ), ∀ p : Sph D × Sph D,
      |(halfPos u ×ˢ halfPos u).indicator (fun p : Sph D × Sph D => quad u hu (kern ε h) p.1 p.2) p|
        ≤ 4 * (2 * ‖h‖) ^ 2 := fun h p => by
    by_cases hp : p ∈ halfPos u ×ˢ halfPos u
    · rw [indicator_of_mem hp]; exact abs_quad_le (abs_kern_le ε h) _ _
    · rw [indicator_of_notMem hp, abs_zero]; positivity
  refine integral_mono (integrable_of_bdd (hm _) (hb _)) (integrable_of_bdd (hm _) (hb _)) ?_
  intro p
  by_cases hp : p ∈ halfPos u ×ˢ halfPos u
  · simp only [indicator_of_mem hp]
    exact quad_kern_polarize_le u hu ε g hp.1 hp.2
  · simp [indicator_of_notMem hp]

end Symm

/-- Polarization decreases the nonlocal cap energy. -/
theorem nlEnergy_polarize_le (u : HilbertVec D) (hu : ‖u‖ = 1) (g : C(Sph D, ℝ)) (ε : ℝ) :
    nlEnergy ε (polarize u hu g) ≤ nlEnergy ε g :=
  Symm.nlEnergy_polarize_le' u hu ε g

end

end PDE.FHLane
