module

public import PDEFoundation.Monotonicity.FriedlandHayman.Symm.Polarize

/-!
# Friedland--Hayman: polarization of continuous functions on the sphere

The definition of `polarize u hu g` (two-point rearrangement toward `⟪x, u⟫ ≥ 0`), equimeasurability,
the sup-norm contraction property, preservation of Lipschitz constants and of nonnegativity.
-/

@[expose] public section

open MeasureTheory Metric Set

namespace PDE.FHLane

noncomputable section

variable {D : ℕ}

namespace Symm

theorem integrable_of_continuous {F : Sph D → ℝ} (hF : Continuous F) :
    Integrable F (sphMeasure D) :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)

theorem phi_max_add_phi_min (Φ : ℝ → ℝ) (a b : ℝ) : Φ (max a b) + Φ (min a b) = Φ a + Φ b := by
  rcases le_total a b with h | h
  · simp [h, add_comm]
  · simp [h]

theorem abs_max_sub_min_le {a b c d M : ℝ} (h1 : |a - c| ≤ M) (h2 : |a - d| ≤ M) (h3 : |b - c| ≤ M)
    (h4 : |b - d| ≤ M) : |max a b - min c d| ≤ M := by
  rw [abs_le] at *
  obtain ⟨h1, h1'⟩ := h1
  obtain ⟨h2, h2'⟩ := h2
  obtain ⟨h3, h3'⟩ := h3
  obtain ⟨h4, h4'⟩ := h4
  rcases max_cases a b with ⟨e, _⟩ | ⟨e, _⟩ <;> rcases min_cases c d with ⟨f, _⟩ | ⟨f, _⟩ <;>
    rw [e, f] <;> constructor <;> linarith

end Symm

open Symm

/-- Polarization (two-point rearrangement) toward the side `⟪x, u⟫ ≥ 0`. -/
def polarize (u : HilbertVec D) (hu : ‖u‖ = 1) (g : C(Sph D, ℝ)) : C(Sph D, ℝ) where
  toFun x :=
    if 0 ≤ inner ℝ (x : HilbertVec D) u then max (g x) (g (rho u hu x))
    else min (g x) (g (rho u hu x))
  continuous_toFun := by
    refine Continuous.if_le
      (g.continuous.max (g.continuous.comp (continuous_rho u hu)))
      (g.continuous.min (g.continuous.comp (continuous_rho u hu)))
      continuous_const (continuous_subtype_val.inner continuous_const) fun x hx => ?_
    rw [rho_eq_of_inner_eq_zero u hu hx.symm]
    simp

variable (u : HilbertVec D) (hu : ‖u‖ = 1)

theorem polarize_apply_of_nonneg (g : C(Sph D, ℝ)) {x : Sph D}
    (hx : 0 ≤ inner ℝ (x : HilbertVec D) u) :
    polarize u hu g x = max (g x) (g (rho u hu x)) := by
  simp [polarize, hx]

theorem polarize_apply_of_neg (g : C(Sph D, ℝ)) {x : Sph D}
    (hx : inner ℝ (x : HilbertVec D) u < 0) :
    polarize u hu g x = min (g x) (g (rho u hu x)) := by
  simp [polarize, not_le.2 hx]

theorem polarize_rho_of_pos (g : C(Sph D, ℝ)) {x : Sph D}
    (hx : 0 < inner ℝ (x : HilbertVec D) u) :
    polarize u hu g (rho u hu x) = min (g x) (g (rho u hu x)) := by
  rw [polarize_apply_of_neg u hu g (by rw [inner_rho_u]; linarith), rho_rho, min_comm]

theorem polarize_of_pos (g : C(Sph D, ℝ)) {x : Sph D}
    (hx : 0 < inner ℝ (x : HilbertVec D) u) :
    polarize u hu g x = max (g x) (g (rho u hu x)) :=
  polarize_apply_of_nonneg u hu g hx.le

/-- Equimeasurability. -/
theorem integral_comp_polarize (g : C(Sph D, ℝ)) {Φ : ℝ → ℝ} (hΦ : Continuous Φ) :
    ∫ x, Φ (polarize u hu g x) ∂(sphMeasure D) = ∫ x, Φ (g x) ∂(sphMeasure D) := by
  rw [integral_split u hu (F := fun x => Φ (polarize u hu g x))
      (integrable_of_continuous (hΦ.comp (polarize u hu g).continuous)),
    integral_split u hu (F := fun x => Φ (g x)) (integrable_of_continuous (hΦ.comp g.continuous))]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  by_cases h : x ∈ halfPos u
  · have h' : 0 < inner ℝ (x : HilbertVec D) u := h
    simp only [indicator_of_mem h, polarize_of_pos u hu g h', polarize_rho_of_pos u hu g h']
    rw [phi_max_add_phi_min]
  · simp [indicator_of_notMem h]

theorem dist_polarize_le (g₁ g₂ : C(Sph D, ℝ)) :
    dist (polarize u hu g₁) (polarize u hu g₂) ≤ dist g₁ g₂ := by
  refine (ContinuousMap.dist_le dist_nonneg).2 fun x => ?_
  have h1 := ContinuousMap.dist_apply_le_dist (f := g₁) (g := g₂) x
  have h2 := ContinuousMap.dist_apply_le_dist (f := g₁) (g := g₂) (rho u hu x)
  rw [Real.dist_eq] at h1 h2 ⊢
  by_cases h : 0 ≤ inner ℝ (x : HilbertVec D) u
  · rw [polarize_apply_of_nonneg u hu _ h, polarize_apply_of_nonneg u hu _ h]
    exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le h1 h2)
  · rw [polarize_apply_of_neg u hu _ (not_le.1 h), polarize_apply_of_neg u hu _ (not_le.1 h)]
    exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le h1 h2)

theorem polarize_nonneg {g : C(Sph D, ℝ)} (hg : ∀ x, 0 ≤ g x) : ∀ x, 0 ≤ polarize u hu g x := by
  intro x
  by_cases h : 0 ≤ inner ℝ (x : HilbertVec D) u
  · rw [polarize_apply_of_nonneg u hu _ h]; exact (hg x).trans (le_max_left _ _)
  · rw [polarize_apply_of_neg u hu _ (not_le.1 h)]; exact le_min (hg _) (hg _)

theorem dist_rho_rho (x y : Sph D) : dist (rho u hu x) (rho u hu y) = dist x y := by
  rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
  have := (reflection' u hu).norm_map ((x : HilbertVec D) - y)
  rw [map_sub] at this
  exact this

theorem dist_rho_left (x y : Sph D) : dist (rho u hu x) y = dist x (rho u hu y) := by
  rw [← dist_rho_rho u hu (rho u hu x) y, rho_rho]

theorem polarize_lipschitz {g : C(Sph D, ℝ)} {L : NNReal} (hg : LipschitzWith L g) :
    LipschitzWith L (polarize u hu g) := by
  have hL : ∀ p q : Sph D, |g p - g q| ≤ L * dist p q := fun p q => by
    simpa [Real.dist_eq] using hg.dist_le_mul p q
  have mixed : ∀ x y : Sph D, 0 ≤ inner ℝ (x : HilbertVec D) u →
      inner ℝ (y : HilbertVec D) u < 0 → dist (polarize u hu g x) (polarize u hu g y) ≤ L * dist x y := by
    intro x y hx hy
    rw [polarize_apply_of_nonneg u hu _ hx, polarize_apply_of_neg u hu _ hy, Real.dist_eq]
    have e1 := dist_rho_le u hu hx hy.le
    have e2 : dist (rho u hu x) y ≤ dist x y := by rw [dist_rho_left]; exact e1
    have hLn : (0 : ℝ) ≤ L := L.2
    refine abs_max_sub_min_le (hL _ _) ((hL _ _).trans ?_) ((hL _ _).trans ?_) ((hL _ _).trans ?_)
    · exact mul_le_mul_of_nonneg_left e1 hLn
    · exact mul_le_mul_of_nonneg_left e2 hLn
    · rw [dist_rho_rho]
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hLn : (0 : ℝ) ≤ L := L.2
  by_cases hx : 0 ≤ inner ℝ (x : HilbertVec D) u <;> by_cases hy : 0 ≤ inner ℝ (y : HilbertVec D) u
  · rw [polarize_apply_of_nonneg u hu _ hx, polarize_apply_of_nonneg u hu _ hy, Real.dist_eq]
    refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le (hL _ _) ((hL _ _).trans ?_))
    rw [dist_rho_rho]
  · exact mixed x y hx (not_le.1 hy)
  · rw [dist_comm, dist_comm x y]; exact mixed y x hy (not_le.1 hx)
  · rw [polarize_apply_of_neg u hu _ (not_le.1 hx), polarize_apply_of_neg u hu _ (not_le.1 hy),
      Real.dist_eq]
    refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le (hL _ _) ((hL _ _).trans ?_))
    rw [dist_rho_rho]

end

end PDE.FHLane
