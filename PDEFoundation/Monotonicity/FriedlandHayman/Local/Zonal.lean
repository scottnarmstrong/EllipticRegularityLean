module

public import PDEFoundation.Monotonicity.FriedlandHayman.Sphere.Proj
public import PDEFoundation.Monotonicity.FriedlandHayman.Sphere.SphereOne
public import PDEFoundation.Monotonicity.FriedlandHayman.Symm.Invariance

/-!
# Friedland--Hayman: the zonal integration formula

For a bounded measurable `G : ℝ → ℝ` and the pole `e₀ = (1, 0, …, 0)`,
`∫_{S^{D-1}} G(⟪x, e₀⟫) dσ = σ_{D-2} ∫_0^π G(cos φ) sin^{D-2} φ dφ`.
It is the case `n = 1` of the projection formula, combined with the two-point evaluation
`sphereIntegral_vec_one` and the substitution `φ ↦ π - φ`.
-/

@[expose] public section

open MeasureTheory

namespace PDE.FHLane

noncomputable section

/-- The pole `e₀ = (1, 0, …, 0)` of `HilbertVec D`. -/
noncomputable def pole (D : ℕ) [NeZero D] : HilbertVec D := Vec.toHilbertVec (Pi.single 0 1 : Vec D)

namespace Local

theorem pole_apply (D : ℕ) [NeZero D] (i : Fin D) : pole D i = (Pi.single 0 1 : Vec D) i := rfl

theorem inner_pole {D : ℕ} [NeZero D] (x : HilbertVec D) : inner ℝ x (pole D) = x 0 := by
  rw [PiLp.inner_apply, Finset.sum_eq_single (0 : Fin D)]
  · simp [pole_apply]
  · intro b _ hb
    simp [pole_apply, hb]
  · simp

theorem intervalIntegrable_of_bdd {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C)
    (a b : ℝ) : IntervalIntegrable f volume a b := by
  have h : ∀ a b : ℝ, IntegrableOn f (Set.Ioc a b) volume := fun a b =>
    Measure.integrableOn_of_bounded (M := C) (by simp) hf.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hC x)
  exact ⟨h a b, h b a⟩

theorem integral_zonal_aux {N : ℕ} [NeZero N] (G : ℝ → ℝ) (hG : Measurable G)
    (hb : ∃ C, ∀ t, |G t| ≤ C) :
    ∫ x, G ((x : HilbertVec (1 + N)) 0) ∂(sphMeasure (1 + N)) =
      sphereArea N * ∫ φ in (0 : ℝ)..Real.pi, G (Real.cos φ) * Real.sin φ ^ (N - 1) := by
  obtain ⟨C, hC⟩ := hb
  set G' : Vec 1 → ℝ := fun z => G (z 0) with hG'
  have hG'm : Measurable G' := hG.comp (measurable_pi_apply 0)
  have h := sphereIntegral_comp_projFst (n := 1) (N := N) G' hG'm ⟨C, fun y => hC _⟩
  have hL : sphereIntegral (0 : Vec (1 + N)) 1 (fun x => G' (projFst x)) =
      ∫ x, G ((x : HilbertVec (1 + N)) 0) ∂(sphMeasure (1 + N)) := by
    simp [sphereIntegral, projFst, hG', sphMeasure]
    rfl
  rw [← hL, h]
  congr 1
  have hf : Measurable fun φ : ℝ => G (Real.cos φ) * Real.sin φ ^ (N - 1) :=
    (hG.comp Real.measurable_cos).mul (Real.measurable_sin.pow_const _)
  have hfb : ∀ φ : ℝ, |G (Real.cos φ) * Real.sin φ ^ (N - 1)| ≤ C := fun φ => by
    rw [abs_mul, abs_pow]
    calc |G (Real.cos φ)| * |Real.sin φ| ^ (N - 1) ≤ C * 1 := by
          refine mul_le_mul (hC _) (pow_le_one₀ (abs_nonneg _) (Real.abs_sin_le_one _))
            (by positivity) ((abs_nonneg _).trans (hC 0))
      _ = C := mul_one C
  have h1 : ∀ θ : ℝ, Real.sin θ ^ (N - 1) * sphereIntegral (0 : Vec 1) (Real.cos θ) G' =
      G (Real.cos θ) * Real.sin θ ^ (N - 1) + G (-Real.cos θ) * Real.sin θ ^ (N - 1) := by
    intro θ
    rw [sphereIntegral_vec_one]
    simp only [hG']
    ring
  simp_rw [h1]
  have hint := intervalIntegrable_of_bdd hf hfb
  have hsub : ∫ θ in (0 : ℝ)..(Real.pi / 2), G (-Real.cos θ) * Real.sin θ ^ (N - 1) =
      ∫ φ in (Real.pi / 2)..Real.pi, G (Real.cos φ) * Real.sin φ ^ (N - 1) := by
    have := intervalIntegral.integral_comp_sub_left
      (fun φ : ℝ => G (Real.cos φ) * Real.sin φ ^ (N - 1)) (a := 0) (b := Real.pi / 2) Real.pi
    simp only [Real.cos_pi_sub, Real.sin_pi_sub] at this
    rw [this]
    congr 1 <;> ring
  rw [intervalIntegral.integral_add (hint _ _) ?_, hsub,
    intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)]
  have := intervalIntegrable_of_bdd (f := fun θ : ℝ => G (-Real.cos θ) * Real.sin θ ^ (N - 1))
    ((hG.comp Real.measurable_cos.neg).mul (Real.measurable_sin.pow_const _)) (C := C) (fun φ => by
      rw [abs_mul, abs_pow]
      calc |G (-Real.cos φ)| * |Real.sin φ| ^ (N - 1) ≤ C * 1 := by
            refine mul_le_mul (hC _) (pow_le_one₀ (abs_nonneg _) (Real.abs_sin_le_one _))
              (by positivity) ((abs_nonneg _).trans (hC 0))
        _ = C := mul_one C) 0 (Real.pi / 2)
  exact this

end Local

open Local

/-- Zonal integration formula. -/
theorem integral_zonal {D : ℕ} (hD : 2 ≤ D) [NeZero D] (G : ℝ → ℝ) (hG : Measurable G)
    (hb : ∃ C, ∀ t, |G t| ≤ C) :
    ∫ x, G (inner ℝ (x : HilbertVec D) (pole D)) ∂(sphMeasure D) =
      sphereArea (D - 1) * ∫ φ in (0 : ℝ)..Real.pi, G (Real.cos φ) * Real.sin φ ^ (D - 2) := by
  obtain ⟨N, rfl⟩ : ∃ N, D = 1 + N := ⟨D - 1, by omega⟩
  have : NeZero N := ⟨by omega⟩
  have h := Local.integral_zonal_aux (N := N) G hG hb
  simp_rw [Local.inner_pole]
  have e1 : 1 + N - 1 = N := by omega
  have e2 : 1 + N - 2 = N - 1 := by omega
  rw [e1, e2]
  exact h

end

end PDE.FHLane
