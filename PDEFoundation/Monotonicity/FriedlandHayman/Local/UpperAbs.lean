module

public import PDEFoundation.Monotonicity.FriedlandHayman.Local.CapTrace
public import PDEFoundation.Monotonicity.FriedlandHayman.Symm.Energy

/-!
# Friedland--Hayman: nonlocal energy bound from a pointwise first-order bound

If `(g x - g y)² ≤ ⟪G x, y - x⟫² + κ |y - x|²` whenever `y` lies in the cap about `x`, with
`G` a continuous vector field bounded by `M`, then the nonlocal energy is bounded by
`m_ε ∫ (|G|² - ⟪G, x⟫²) + (m'_ε M² + κ ((D - 1) m_ε + m'_ε)) σ(S)`.
-/

@[expose] public section

open MeasureTheory

namespace PDE.FHLane

noncomputable section

namespace Local

variable {D : ℕ}

/-- The inner (in `y`) energy at a fixed point is bounded by the cap moments. -/
theorem inner_energy_le (hD : 2 ≤ D) [NeZero D] (g : C(Sph D, ℝ)) (G : Sph D → HilbertVec D)
    {κ ε : ℝ} (hε : 0 < ε) (hε' : ε < Real.pi)
    (hpt : ∀ x y : Sph D, Real.cos ε < inner ℝ (x : HilbertVec D) (y : HilbertVec D) →
      (g x - g y) ^ 2 ≤ inner ℝ (G x) ((y : HilbertVec D) - x) ^ 2 +
        κ * ‖(y : HilbertVec D) - x‖ ^ 2) (x : Sph D) :
    ∫ y : Sph D, (if Real.cos ε < inner ℝ (x : HilbertVec D) (y : HilbertVec D) then
        (g x - g y) ^ 2 else 0) ∂(sphMeasure D) ≤
      capMom D ε * (‖G x‖ ^ 2 - inner ℝ (G x) (x : HilbertVec D) ^ 2) +
        capMom' D ε * inner ℝ (G x) (x : HilbertVec D) ^ 2 +
        κ * (((D : ℝ) - 1) * capMom D ε + capMom' D ε) := by
  have c1 : Continuous fun y : Sph D => (g x - g y) ^ 2 :=
    (continuous_const.sub g.continuous).pow 2
  have c2 : Continuous fun y : Sph D => inner ℝ (G x) ((y : HilbertVec D) - x) ^ 2 :=
    (continuous_const.inner (continuous_subtype_val.sub continuous_const)).pow 2
  have c3 : Continuous fun y : Sph D => ‖(y : HilbertVec D) - x‖ ^ 2 :=
    (continuous_subtype_val.sub continuous_const).norm.pow 2
  have h1 := integrable_cap_at x c2 ε
  have h2 := (integrable_cap_at x c3 ε).const_mul κ
  have key : ∫ y : Sph D, (if Real.cos ε < inner ℝ (x : HilbertVec D) (y : HilbertVec D) then
        (g x - g y) ^ 2 else 0) ∂(sphMeasure D) ≤
      ∫ y : Sph D, ((if Real.cos ε < inner ℝ (x : HilbertVec D) (y : HilbertVec D) then
        inner ℝ (G x) ((y : HilbertVec D) - x) ^ 2 else 0) +
        κ * (if Real.cos ε < inner ℝ (x : HilbertVec D) (y : HilbertVec D) then
        ‖(y : HilbertVec D) - x‖ ^ 2 else 0)) ∂(sphMeasure D) := by
    refine integral_mono (integrable_cap_at x c1 ε) (h1.add h2) fun y => ?_
    by_cases hy : Real.cos ε < inner ℝ (x : HilbertVec D) (y : HilbertVec D)
    · simp only [hy, ↓reduceIte]
      exact hpt x y hy
    · simp [hy]
  refine key.trans (le_of_eq ?_)
  rw [integral_add h1 h2, integral_const_mul, cap_second_moment hD x (G x) hε hε',
    cap_trace hD x hε hε']

end Local

open Local

/-- The nonlocal energy is bounded by the cap moments of a pointwise first-order bound. -/
theorem nlEnergy_le_of_pointwise {D : ℕ} (hD : 2 ≤ D) [NeZero D] (g : C(Sph D, ℝ))
    (G : Sph D → HilbertVec D) (hG : Continuous G) {κ M ε : ℝ}
    (hε : 0 < ε) (hε' : ε < Real.pi) (hM : ∀ x, ‖G x‖ ≤ M)
    (hpt : ∀ x y : Sph D, Real.cos ε < inner ℝ (x : HilbertVec D) (y : HilbertVec D) →
      (g x - g y) ^ 2 ≤ inner ℝ (G x) ((y : HilbertVec D) - x) ^ 2 +
        κ * ‖(y : HilbertVec D) - x‖ ^ 2) :
    nlEnergy ε g ≤
      capMom D ε * ∫ x, (‖G x‖ ^ 2 - inner ℝ (G x) (x : HilbertVec D) ^ 2) ∂(sphMeasure D) +
        (capMom' D ε * M ^ 2 + κ * (((D : ℝ) - 1) * capMom D ε + capMom' D ε)) *
          (sphMeasure D).real Set.univ := by
  have hm' : 0 ≤ capMom' D ε := capMom'_nonneg hD hε hε'.le
  set T : Sph D → ℝ := fun x => ‖G x‖ ^ 2 - inner ℝ (G x) (x : HilbertVec D) ^ 2 with hT
  have hTc : Continuous T :=
    (hG.norm.pow 2).sub ((hG.inner continuous_subtype_val).pow 2)
  set c : ℝ := capMom' D ε * M ^ 2 + κ * (((D : ℝ) - 1) * capMom D ε + capMom' D ε) with hc
  have hBi : Integrable (fun x : Sph D => capMom D ε * T x + c) (sphMeasure D) :=
    (Symm.integrable_of_continuous (hTc.const_mul _ |>.add continuous_const))
  have hle : ∀ x : Sph D, ∫ y : Sph D, (if Real.cos ε < inner ℝ (x : HilbertVec D)
      (y : HilbertVec D) then (g x - g y) ^ 2 else 0) ∂(sphMeasure D) ≤
      capMom D ε * T x + c := by
    intro x
    refine (inner_energy_le hD g G hε hε' hpt x).trans ?_
    have h1 : inner ℝ (G x) (x : HilbertVec D) ^ 2 ≤ M ^ 2 := by
      have h := abs_real_inner_le_norm (G x) (x : HilbertVec D)
      have hx : ‖(x : HilbertVec D)‖ = 1 := by simp
      rw [hx, mul_one] at h
      have : |inner ℝ (G x) (x : HilbertVec D)| ≤ M := h.trans (hM x)
      calc inner ℝ (G x) (x : HilbertVec D) ^ 2 = |inner ℝ (G x) (x : HilbertVec D)| ^ 2 :=
            (sq_abs _).symm
        _ ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
    have := mul_le_mul_of_nonneg_left h1 hm'
    simp only [hT, hc]
    linarith
  unfold nlEnergy
  calc _ ≤ ∫ x : Sph D, (capMom D ε * T x + c) ∂(sphMeasure D) := by
        refine integral_mono_of_nonneg (ae_of_all _ fun x => ?_) hBi (ae_of_all _ hle)
        exact integral_nonneg fun y => by split_ifs <;> positivity
    _ = _ := by
        rw [integral_add ((Symm.integrable_of_continuous hTc).const_mul _) (integrable_const c),
          integral_const_mul, integral_const, smul_eq_mul]
        ring

end

end PDE.FHLane
