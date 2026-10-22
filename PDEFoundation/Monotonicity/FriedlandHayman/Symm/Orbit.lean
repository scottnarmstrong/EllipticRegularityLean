module

public import PDEFoundation.Monotonicity.FriedlandHayman.Symm.EnergyContinuity
public import PDEFoundation.Monotonicity.FriedlandHayman.Symm.Moment

/-!
# Friedland--Hayman: the polarization orbit and its invariants

The orbit of `g` under polarizations toward `u` with `0 ≤ ⟪u, e⟫`, the closed, polarization-invariant
set `Inv g L M` of nonnegative `L`-Lipschitz functions bounded by `M` that are equimeasurable with
`g` and have no larger nonlocal energies, and continuity of the integral functionals used for the
compactness argument.
-/

@[expose] public section

open MeasureTheory Metric Set

namespace PDE.FHLane.Rearr

noncomputable section

variable {D : ℕ}

/-- The polarization orbit of `g`, using only poles `u` with `0 ≤ ⟪u, e⟫`. -/
inductive Orbit (g : C(Sph D, ℝ)) (e : HilbertVec D) : C(Sph D, ℝ) → Prop
  | base : Orbit g e g
  | step {k : C(Sph D, ℝ)} (u : HilbertVec D) (hu : ‖u‖ = 1) (hue : 0 ≤ inner ℝ u e) :
      Orbit g e k → Orbit g e (polarize u hu k)

/-- Continuity of the integral on `C(Sph D, ℝ)` for the sup norm. -/
theorem continuous_integral : Continuous (fun k : C(Sph D, ℝ) => ∫ x, k x ∂(sphMeasure D)) := by
  refine Metric.continuous_iff.2 fun k₀ ε hε => ?_
  set M : ℝ := (sphMeasure D).real univ
  refine ⟨ε / (M + 1), by positivity, fun k hk => ?_⟩
  have hM : 0 ≤ M := measureReal_nonneg
  have h := norm_integral_le_of_norm_le_const (μ := sphMeasure D) (f := fun x => k x - k₀ x)
    (C := dist k k₀) (ae_of_all _ fun x => by
      simpa [Real.dist_eq] using ContinuousMap.dist_apply_le_dist (f := k) (g := k₀) x)
  rw [integral_sub (Symm.integrable_of_continuous k.continuous)
    (Symm.integrable_of_continuous k₀.continuous), Real.norm_eq_abs] at h
  rw [Real.dist_eq]
  refine lt_of_le_of_lt h ?_
  have h2 : dist k k₀ * (M + 1) < ε := by rwa [lt_div_iff₀ (by positivity)] at hk
  nlinarith [dist_nonneg (x := k) (y := k₀)]

theorem continuous_integral_comp (Φ : C(ℝ, ℝ)) :
    Continuous (fun k : C(Sph D, ℝ) => ∫ x, Φ (k x) ∂(sphMeasure D)) :=
  continuous_integral.comp Φ.continuous_postcomp

theorem continuous_moment (e : HilbertVec D) :
    Continuous (fun k : C(Sph D, ℝ) => ∫ x, k x * inner ℝ (x : HilbertVec D) e ∂(sphMeasure D)) := by
  refine Metric.continuous_iff.2 fun k₀ ε hε => ?_
  set M : ℝ := (sphMeasure D).real univ
  refine ⟨ε / ((M + 1) * (‖e‖ + 1)), by positivity, fun k hk => ?_⟩
  have hM : 0 ≤ M := measureReal_nonneg
  have hc : ∀ F : C(Sph D, ℝ), Integrable (fun x => F x * inner ℝ (x : HilbertVec D) e)
      (sphMeasure D) := fun F =>
    Symm.integrable_of_continuous (F.continuous.mul (continuous_subtype_val.inner continuous_const))
  have h := norm_integral_le_of_norm_le_const (μ := sphMeasure D)
    (f := fun x => k x * inner ℝ (x : HilbertVec D) e - k₀ x * inner ℝ (x : HilbertVec D) e)
    (C := dist k k₀ * ‖e‖) (ae_of_all _ fun x => by
      have h1 := ContinuousMap.dist_apply_le_dist (f := k) (g := k₀) x
      rw [Real.dist_eq] at h1
      rw [← sub_mul, Real.norm_eq_abs, abs_mul]
      have h2 : |inner ℝ (x : HilbertVec D) e| ≤ ‖e‖ := by
        have := abs_real_inner_le_norm (x : HilbertVec D) e
        simpa using this
      exact mul_le_mul h1 h2 (abs_nonneg _) dist_nonneg)
  rw [integral_sub (hc k) (hc k₀), Real.norm_eq_abs] at h
  rw [Real.dist_eq]
  refine lt_of_le_of_lt h ?_
  have h2 : dist k k₀ * ((M + 1) * (‖e‖ + 1)) < ε := by
    rwa [lt_div_iff₀ (by positivity)] at hk
  have := dist_nonneg (x := k) (y := k₀)
  nlinarith [mul_nonneg this hM, mul_nonneg this (norm_nonneg e),
    mul_nonneg (mul_nonneg this hM) (norm_nonneg e)]

/-- The invariant set: nonnegative, bounded by `M`, `L`-Lipschitz, equimeasurable with `g`, and with
nonlocal energies at most those of `g`. -/
def Inv (g : C(Sph D, ℝ)) (L : NNReal) (M : ℝ) (k : C(Sph D, ℝ)) : Prop :=
  (∀ x, 0 ≤ k x) ∧ (∀ x, k x ≤ M) ∧ LipschitzWith L k ∧
    (∀ Φ : C(ℝ, ℝ), ∫ x, Φ (k x) ∂(sphMeasure D) = ∫ x, Φ (g x) ∂(sphMeasure D)) ∧
    ∀ ε, nlEnergy ε k ≤ nlEnergy ε g

theorem isClosed_inv (g : C(Sph D, ℝ)) (L : NNReal) (M : ℝ) : IsClosed {k | Inv g L M k} := by
  have hev : ∀ x : Sph D, Continuous (fun k : C(Sph D, ℝ) => k x) := fun x =>
    continuous_eval_const x
  have h1 : IsClosed {k : C(Sph D, ℝ) | ∀ x, 0 ≤ k x} := by
    rw [ofPred_forall]; exact isClosed_iInter fun x => isClosed_le continuous_const (hev x)
  have h2 : IsClosed {k : C(Sph D, ℝ) | ∀ x, k x ≤ M} := by
    rw [ofPred_forall]; exact isClosed_iInter fun x => isClosed_le (hev x) continuous_const
  have h3 : IsClosed {k : C(Sph D, ℝ) | LipschitzWith L k} := by
    have : {k : C(Sph D, ℝ) | LipschitzWith L k} =
        ⋂ p : Sph D × Sph D, {k | dist (k p.1) (k p.2) ≤ L * dist p.1 p.2} := by
      ext k
      simp only [mem_ofPred_eq, mem_iInter]
      constructor
      · intro h p; exact h.dist_le_mul p.1 p.2
      · intro h; exact LipschitzWith.of_dist_le_mul fun x y => h (x, y)
    rw [this]
    exact isClosed_iInter fun p =>
      isClosed_le (((hev p.1).dist (hev p.2))) continuous_const
  have h4 : IsClosed {k : C(Sph D, ℝ) | ∀ Φ : C(ℝ, ℝ),
      ∫ x, Φ (k x) ∂(sphMeasure D) = ∫ x, Φ (g x) ∂(sphMeasure D)} := by
    rw [ofPred_forall]; exact isClosed_iInter fun Φ => isClosed_eq (continuous_integral_comp Φ) continuous_const
  have h5 : IsClosed {k : C(Sph D, ℝ) | ∀ ε, nlEnergy ε k ≤ nlEnergy ε g} := by
    rw [ofPred_forall]; exact isClosed_iInter fun ε => isClosed_le (continuous_nlEnergy ε) continuous_const
  exact h1.inter (h2.inter (h3.inter (h4.inter h5)))

theorem inv_polarize {g : C(Sph D, ℝ)} {L : NNReal} {M : ℝ} {k : C(Sph D, ℝ)} (hk : Inv g L M k)
    (u : HilbertVec D) (hu : ‖u‖ = 1) : Inv g L M (polarize u hu k) := by
  obtain ⟨h0, hM, hL, hΦ, hE⟩ := hk
  refine ⟨polarize_nonneg u hu h0, fun x => ?_, polarize_lipschitz u hu hL,
    fun Φ => (integral_comp_polarize u hu k Φ.continuous).trans (hΦ Φ),
    fun ε => (nlEnergy_polarize_le u hu k ε).trans (hE ε)⟩
  by_cases h : 0 ≤ inner ℝ (x : HilbertVec D) u
  · rw [polarize_apply_of_nonneg u hu _ h]; exact max_le (hM _) (hM _)
  · rw [polarize_apply_of_neg u hu _ (not_le.1 h)]; exact (min_le_left _ _).trans (hM _)

theorem orbit_inv {g : C(Sph D, ℝ)} {L : NNReal} {M : ℝ} (hg : Inv g L M g) {e : HilbertVec D}
    {k : C(Sph D, ℝ)} (hk : Orbit g e k) : Inv g L M k := by
  induction hk with
  | base => exact hg
  | step u hu _ _ ih => exact inv_polarize ih u hu

/-- The closure of the orbit. -/
def Hull (g : C(Sph D, ℝ)) (e : HilbertVec D) : Set (C(Sph D, ℝ)) := closure {k | Orbit g e k}

theorem hull_inv {g : C(Sph D, ℝ)} {L : NNReal} {M : ℝ} (hg : Inv g L M g) {e : HilbertVec D}
    {k : C(Sph D, ℝ)} (hk : k ∈ Hull g e) : Inv g L M k :=
  closure_minimal (fun _ h => orbit_inv hg h) (isClosed_inv g L M) hk

theorem self_mem_hull (g : C(Sph D, ℝ)) (e : HilbertVec D) : g ∈ Hull g e :=
  subset_closure Orbit.base

theorem polarize_mem_hull {g : C(Sph D, ℝ)} {e : HilbertVec D} {k : C(Sph D, ℝ)}
    (hk : k ∈ Hull g e) (u : HilbertVec D) (hu : ‖u‖ = 1) (hue : 0 ≤ inner ℝ u e) :
    polarize u hu k ∈ Hull g e := by
  have hcont : Continuous (polarize u hu : C(Sph D, ℝ) → C(Sph D, ℝ)) :=
    LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun a b => by
      simpa using dist_polarize_le u hu a b)
  have := map_mem_closure hcont hk (fun a (ha : Orbit g e a) => Orbit.step u hu hue ha)
  exact this

end

end PDE.FHLane.Rearr
