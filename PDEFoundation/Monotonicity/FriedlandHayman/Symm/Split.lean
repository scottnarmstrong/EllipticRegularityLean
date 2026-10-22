module

public import PDEFoundation.Monotonicity.FriedlandHayman.Symm.Polarize

/-!
# Friedland--Hayman: splitting a double sphere integral over `H₊ × H₊`

For a bounded jointly measurable kernel `k` on the sphere, the iterated integral of `k` equals the
integral over the product measure of the four-term sum
`k x y + k x (ρ y) + k (ρ x) y + k (ρ x) (ρ y)` restricted to `H₊ × H₊`.
-/

@[expose] public section

open MeasureTheory Metric Set

namespace PDE.FHLane

noncomputable section

variable {D : ℕ}

namespace Symm

theorem integrable_of_bdd {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hC x)

variable (u : HilbertVec D) (hu : ‖u‖ = 1)

theorem measurable_rho : Measurable (rho u hu) := (continuous_rho u hu).measurable

/-- The four-term symmetrization of a kernel. -/
def quad (k : Sph D → Sph D → ℝ) (x y : Sph D) : ℝ :=
  k x y + k x (rho u hu y) + k (rho u hu x) y + k (rho u hu x) (rho u hu y)

variable {u hu}

theorem measurable_quad {k : Sph D → Sph D → ℝ}
    (hk : Measurable (fun p : Sph D × Sph D => k p.1 p.2)) :
    Measurable (fun p : Sph D × Sph D => quad u hu k p.1 p.2) := by
  have hρ := measurable_rho u hu
  have h1 : Measurable fun p : Sph D × Sph D => k p.1 (rho u hu p.2) :=
    hk.comp (measurable_fst.prodMk (hρ.comp measurable_snd))
  have h2 : Measurable fun p : Sph D × Sph D => k (rho u hu p.1) p.2 :=
    hk.comp ((hρ.comp measurable_fst).prodMk measurable_snd)
  have h3 : Measurable fun p : Sph D × Sph D => k (rho u hu p.1) (rho u hu p.2) :=
    hk.comp ((hρ.comp measurable_fst).prodMk (hρ.comp measurable_snd))
  exact ((hk.add h1).add h2).add h3

theorem abs_quad_le {k : Sph D → Sph D → ℝ} {C : ℝ} (hC : ∀ x y, |k x y| ≤ C) (x y : Sph D) :
    |quad u hu k x y| ≤ 4 * C := by
  have := hC x y
  have := hC x (rho u hu y)
  have := hC (rho u hu x) y
  have := hC (rho u hu x) (rho u hu y)
  unfold quad
  rw [abs_le] at *
  constructor <;> linarith

theorem measurable_prodMk_left' {k : Sph D → Sph D → ℝ}
    (hk : Measurable (fun p : Sph D × Sph D => k p.1 p.2)) (x : Sph D) :
    Measurable (fun y : Sph D => k x y) :=
  hk.comp measurable_prodMk_left

theorem measurable_halfPos_pair {k : Sph D → Sph D → ℝ}
    (hk : Measurable (fun p : Sph D × Sph D => k p.1 p.2)) :
    Measurable fun p : Sph D × Sph D =>
      (halfPos u).indicator (fun y => k p.1 y + k p.1 (rho u hu y)) p.2 := by
  have hρ := measurable_rho u hu
  have : Measurable fun p : Sph D × Sph D => k p.1 p.2 + k p.1 (rho u hu p.2) :=
    hk.add (hk.comp (measurable_fst.prodMk (hρ.comp measurable_snd)))
  exact this.indicator ((measurableSet_halfPos u).preimage measurable_snd)

theorem abs_halfPos_pair_le {k : Sph D → Sph D → ℝ} {C : ℝ} (hC : ∀ x y, |k x y| ≤ C)
    (x y : Sph D) :
    |(halfPos u).indicator (fun y => k x y + k x (rho u hu y)) y| ≤ 2 * C := by
  have := hC x y
  have h0 := (abs_nonneg _).trans this
  by_cases h : y ∈ halfPos u
  · rw [indicator_of_mem h]
    have := hC x (rho u hu y)
    rw [abs_le] at *
    constructor <;> linarith
  · rw [indicator_of_notMem h, abs_zero]
    linarith

theorem integrable_halfPos_pair {k : Sph D → Sph D → ℝ}
    (hk : Measurable (fun p : Sph D × Sph D => k p.1 p.2)) {C : ℝ} (hC : ∀ x y, |k x y| ≤ C)
    (x : Sph D) :
    Integrable (fun y => (halfPos u).indicator (fun y => k x y + k x (rho u hu y)) y)
      (sphMeasure D) := by
  have hρ := measurable_rho u hu
  refine integrable_of_bdd (C := 2 * C) ?_ (abs_halfPos_pair_le hC x)
  refine Measurable.indicator ?_ (measurableSet_halfPos u)
  exact (measurable_prodMk_left' hk x).add ((measurable_prodMk_left' hk x).comp hρ)

theorem iterated_split {k : Sph D → Sph D → ℝ}
    (hk : Measurable (fun p : Sph D × Sph D => k p.1 p.2)) {C : ℝ} (hC : ∀ x y, |k x y| ≤ C) :
    ∫ x, ∫ y, k x y ∂(sphMeasure D) ∂(sphMeasure D) =
      ∫ p, (halfPos u ×ˢ halfPos u).indicator (fun p => quad u hu k p.1 p.2) p
        ∂((sphMeasure D).prod (sphMeasure D)) := by
  set G : Sph D × Sph D → ℝ :=
    (halfPos u ×ˢ halfPos u).indicator (fun p => quad u hu k p.1 p.2) with hG
  have hGm : Measurable G :=
    (measurable_quad hk).indicator ((measurableSet_halfPos u).prod (measurableSet_halfPos u))
  have hGb : ∀ p, |G p| ≤ 4 * C := fun p => by
    by_cases h : p ∈ halfPos u ×ˢ halfPos u
    · rw [hG, indicator_of_mem h]; exact abs_quad_le hC _ _
    · rw [hG, indicator_of_notMem h, abs_zero]
      have := (abs_nonneg _).trans (hC p.1 p.2)
      linarith
  have hGi : Integrable G ((sphMeasure D).prod (sphMeasure D)) := integrable_of_bdd hGm hGb
  rw [integral_prod _ hGi]
  set H : Sph D → ℝ := fun x =>
    ∫ y, (halfPos u).indicator (fun y => k x y + k x (rho u hu y)) y ∂(sphMeasure D) with hH
  have step1 : ∀ x, ∫ y, k x y ∂(sphMeasure D) = H x := fun x =>
    integral_split u hu (integrable_of_bdd (measurable_prodMk_left' hk x) (hC x))
  have hHi : Integrable H (sphMeasure D) :=
    (integrable_of_bdd (μ := (sphMeasure D).prod (sphMeasure D)) (measurable_halfPos_pair hk)
      (fun p => abs_halfPos_pair_le hC p.1 p.2)).integral_prod_left
  have e1 : ∫ x, ∫ y, k x y ∂(sphMeasure D) ∂(sphMeasure D) = ∫ x, H x ∂(sphMeasure D) :=
    integral_congr_ae (ae_of_all _ step1)
  rw [e1, integral_split u hu hHi]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  by_cases hx : x ∈ halfPos u
  · rw [indicator_of_mem hx]
    have : H x + H (rho u hu x) = ∫ y, G (x, y) ∂(sphMeasure D) := by
      rw [hH]
      simp only
      rw [← integral_add (integrable_halfPos_pair hk hC x) (integrable_halfPos_pair hk hC _)]
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      by_cases hy : y ∈ halfPos u
      · simp only [hG, indicator_of_mem hy, indicator_of_mem (Set.mk_mem_prod hx hy), quad]
        ring
      · simp [hG, hy]
    exact this
  · rw [indicator_of_notMem hx]
    symm
    simp [hG, hx]

end Symm

end

end PDE.FHLane
