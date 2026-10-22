module

public import PDEFoundation.Monotonicity.FriedlandHayman.Symm.Invariance

/-!
# Friedland--Hayman: polarization on the sphere

The hyperplane reflection `reflection' u`, the polarization `polarize u g` of a continuous function
on the sphere toward the side `⟪x, u⟫ ≥ 0`, the splitting of sphere integrals over the two open
half-spheres, and equimeasurability of polarization.
-/

@[expose] public section

open MeasureTheory Metric Set

namespace PDE.FHLane

noncomputable section

variable {D : ℕ}

/-- Reflection in the hyperplane `u^⊥` (`‖u‖ = 1`), as a linear isometry equivalence. -/
def reflection' (u : HilbertVec D) (_hu : ‖u‖ = 1) : HilbertVec D ≃ₗᵢ[ℝ] HilbertVec D :=
  Submodule.reflection (ℝ ∙ u)ᗮ

theorem reflection'_apply (u : HilbertVec D) (hu : ‖u‖ = 1) (x : HilbertVec D) :
    reflection' u hu x = x - (2 * inner ℝ x u) • u := by
  rw [reflection', Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
  simp [hu, real_inner_comm]
  module

namespace Symm

/-- The reflection acting on the sphere. -/
abbrev rho (u : HilbertVec D) (hu : ‖u‖ = 1) : Sph D → Sph D := sphMap (reflection' u hu)

variable (u : HilbertVec D) (hu : ‖u‖ = 1)

theorem coe_rho (x : Sph D) :
    ((rho u hu x : Sph D) : HilbertVec D) = (x : HilbertVec D) - (2 * inner ℝ (x : HilbertVec D) u) • u :=
  reflection'_apply u hu x

theorem rho_rho (x : Sph D) : rho u hu (rho u hu x) = x := by
  apply Subtype.ext
  simp [rho, reflection', Submodule.reflection_reflection]

theorem inner_rho_rho (x y : Sph D) :
    inner ℝ (rho u hu x : HilbertVec D) (rho u hu y : HilbertVec D) =
      inner ℝ (x : HilbertVec D) (y : HilbertVec D) :=
  LinearIsometryEquiv.inner_map_map _ _ _

theorem inner_rho_u (x : Sph D) :
    inner ℝ (rho u hu x : HilbertVec D) u = - inner ℝ (x : HilbertVec D) u := by
  rw [coe_rho, inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq, hu]
  simp; ring

theorem rho_eq_of_inner_eq_zero {x : Sph D} (h : inner ℝ (x : HilbertVec D) u = 0) :
    rho u hu x = x := by
  apply Subtype.ext
  rw [coe_rho, h]; simp

theorem inner_sub_inner_rho (x y : Sph D) :
    inner ℝ (x : HilbertVec D) y - inner ℝ (x : HilbertVec D) (rho u hu y : HilbertVec D) =
      2 * (inner ℝ (x : HilbertVec D) u * inner ℝ (y : HilbertVec D) u) := by
  rw [coe_rho, inner_sub_right, inner_smul_right]
  ring

theorem inner_rho_left (x y : Sph D) :
    inner ℝ (rho u hu x : HilbertVec D) (y : HilbertVec D) =
      inner ℝ (x : HilbertVec D) (rho u hu y : HilbertVec D) := by
  rw [← inner_rho_rho u hu x (rho u hu y), rho_rho]

theorem continuous_rho : Continuous (rho u hu) := continuous_sphMap _

theorem dist_rho_le {x y : Sph D} (hx : 0 ≤ inner ℝ (x : HilbertVec D) u)
    (hy : inner ℝ (y : HilbertVec D) u ≤ 0) : dist x (rho u hu y) ≤ dist x y := by
  have h := inner_sub_inner_rho u hu x y
  have h2 : inner ℝ (x : HilbertVec D) y ≤ inner ℝ (x : HilbertVec D) (rho u hu y : HilbertVec D) := by
    nlinarith [mul_nonneg hx (neg_nonneg.2 hy)]
  have key : ∀ z : Sph D, dist x z ^ 2 = 2 - 2 * inner ℝ (x : HilbertVec D) (z : HilbertVec D) := by
    intro z
    have hx1 : ‖(x : HilbertVec D)‖ = 1 := by simp
    have hz1 : ‖(z : HilbertVec D)‖ = 1 := by simp
    rw [Subtype.dist_eq, dist_eq_norm, ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
      inner_sub_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hx1, hz1,
      real_inner_comm (z : HilbertVec D) x]
    ring
  apply le_of_sq_le_sq _ dist_nonneg
  rw [key, key]
  linarith

/-- The open half-sphere `⟪x, u⟫ > 0`. -/
def halfPos (u : HilbertVec D) : Set (Sph D) := {x | 0 < inner ℝ (x : HilbertVec D) u}

theorem measurableSet_halfPos : MeasurableSet (halfPos u) :=
  (isOpen_lt continuous_const (continuous_subtype_val.inner continuous_const)).measurableSet

theorem isOpen_halfPos : IsOpen (halfPos u) :=
  isOpen_lt continuous_const (continuous_subtype_val.inner continuous_const)

theorem ae_inner_ne_zero (hu0 : u ≠ 0) :
    ∀ᵐ x : Sph D ∂(sphMeasure D), inner ℝ (x : HilbertVec D) u ≠ 0 := measure_eq_zero_iff_ae_notMem.1 (sphMeasure_inner_eq_zero hu0)

/-- Splitting a sphere integral over the open half-sphere `⟪x, u⟫ > 0`. -/
theorem integral_split {F : Sph D → ℝ} (hF : Integrable F (sphMeasure D)) :
    ∫ x, F x ∂(sphMeasure D) =
      ∫ x, (halfPos u).indicator (fun x => F x + F (rho u hu x)) x ∂(sphMeasure D) := by
  have hFρ : Integrable (fun x => F (rho u hu x)) (sphMeasure D) := integrable_comp_sphMap _ hF
  have hA := measurableSet_halfPos u
  have hB : MeasurableSet {x : Sph D | inner ℝ (x : HilbertVec D) u < 0} :=
    (isOpen_lt (continuous_subtype_val.inner continuous_const) continuous_const).measurableSet
  have h1 : ∫ x, F x ∂(sphMeasure D) =
      ∫ x, ((halfPos u).indicator F x + {x : Sph D | inner ℝ (x : HilbertVec D) u < 0}.indicator F x)
        ∂(sphMeasure D) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_inner_ne_zero u (ne_zero_of_norm_ne_zero (by rw [hu]; norm_num))] with x hx
    rcases lt_or_gt_of_ne hx with h | h
    · have : x ∉ halfPos u := by simp [halfPos, h.le]
      simp [this, h]
    · have : x ∈ halfPos u := h
      simp [this, not_lt.2 h.le]
  have h2 : ∫ x, {x : Sph D | inner ℝ (x : HilbertVec D) u < 0}.indicator F x ∂(sphMeasure D) =
      ∫ x, (halfPos u).indicator (fun x => F (rho u hu x)) x ∂(sphMeasure D) := by
    rw [← integral_comp_sphMap (reflection' u hu)
      ((hFρ.indicator hA).aestronglyMeasurable)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    by_cases h : inner ℝ (x : HilbertVec D) u < 0
    · have h' : rho u hu x ∈ halfPos u := by
        show 0 < inner ℝ (rho u hu x : HilbertVec D) u
        rw [inner_rho_u]; linarith
      simp [h, h', rho_rho]
    · have h' : rho u hu x ∉ halfPos u := by
        show ¬ 0 < inner ℝ (rho u hu x : HilbertVec D) u
        rw [inner_rho_u]; linarith [not_lt.1 h]
      simp [h, h']
  rw [h1, integral_add (hF.indicator hA) (hF.indicator hB), h2, ← integral_add (hF.indicator hA)
    (hFρ.indicator hA)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  by_cases h : x ∈ halfPos u <;> simp [h]

end Symm

end

end PDE.FHLane
