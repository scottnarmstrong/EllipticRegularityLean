module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Friedland--Hayman: two-dimensional polar coordinates on the quarter plane

For `a b : ℕ` and an arbitrary profile `g : ℝ → ℝ`, the integral over the open quarter plane
of `s^a t^b exp(-(s² + t²)/2) g(s / √(s² + t²))` factors, in polar coordinates, as the radial
Gaussian moment times the angular integral of `sin^b cos^a g(cos)` over `(0, π/2)`.
-/

@[expose] public section

open MeasureTheory

namespace PDE.FHLane

noncomputable section

/-- The dilation factor `s / √(s² + t²)`. -/
def wfac (s t : ℝ) : ℝ := (Real.sqrt (s ^ 2 + t ^ 2))⁻¹ * s

/-- The quarter-plane integrand. -/
def quadIntegrand (a b : ℕ) (g : ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  z.1 ^ a * (z.2 ^ b * (Real.exp (-((z.1 ^ 2 + z.2 ^ 2) / 2)) * g (wfac z.1 z.2)))

/-- The angular profile. -/
def angProfile (a b : ℕ) (g : ℝ → ℝ) (θ : ℝ) : ℝ :=
  Real.sin θ ^ b * (Real.cos θ ^ a * g (Real.cos θ))

theorem cos_sin_pos_iff {θ : ℝ} (h : θ ∈ Set.Ioo (-Real.pi) Real.pi) :
    (0 < Real.cos θ ∧ 0 < Real.sin θ) ↔ θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  constructor
  · rintro ⟨hc, hs⟩
    have h0 : 0 < θ := by
      by_contra hneg
      push Not at hneg
      have := Real.sin_nonpos_of_nonpos_of_neg_pi_le hneg h.1.le
      linarith
    refine ⟨h0, ?_⟩
    by_contra hge
    push Not at hge
    have := Real.cos_nonpos_of_pi_div_two_le_of_le hge (by linarith [h.2])
    linarith
  · intro hθ
    refine ⟨Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩,
      Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])⟩

theorem quadIntegrand_polar (a b : ℕ) (g : ℝ → ℝ) {p : ℝ × ℝ} (hp : p ∈ polarCoord.target) :
    p.1 • (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)).indicator (quadIntegrand a b g)
        (polarCoord.symm p) =
      (p.1 ^ (a + b + 1) * Real.exp (-(p.1 ^ 2 / 2))) *
        (Set.Ioo 0 (Real.pi / 2)).indicator (angProfile a b g) p.2 := by
  obtain ⟨hR, hθ⟩ : 0 < p.1 ∧ p.2 ∈ Set.Ioo (-Real.pi) Real.pi := hp
  rw [polarCoord_symm_apply]
  by_cases hq : p.2 ∈ Set.Ioo 0 (Real.pi / 2)
  · obtain ⟨hc, hs⟩ := (cos_sin_pos_iff hθ).2 hq
    have hmem : (p.1 * Real.cos p.2, p.1 * Real.sin p.2) ∈
        Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) := ⟨mul_pos hR hc, mul_pos hR hs⟩
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hq]
    have hsq : (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2 := by
      have := Real.sin_sq_add_cos_sq p.2
      calc _ = p.1 ^ 2 * (Real.sin p.2 ^ 2 + Real.cos p.2 ^ 2) := by ring
        _ = _ := by rw [this, mul_one]
    have hw : wfac (p.1 * Real.cos p.2) (p.1 * Real.sin p.2) = Real.cos p.2 := by
      unfold wfac
      rw [hsq, Real.sqrt_sq hR.le]
      field_simp
    unfold quadIntegrand angProfile
    simp only [hsq, hw, smul_eq_mul]
    rw [mul_pow, mul_pow, pow_succ, pow_add]
    ring
  · have hmem : (p.1 * Real.cos p.2, p.1 * Real.sin p.2) ∉
        Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) := by
      intro h
      exact hq ((cos_sin_pos_iff hθ).1 ⟨(mul_pos_iff_of_pos_left hR).1 h.1,
        (mul_pos_iff_of_pos_left hR).1 h.2⟩)
    rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hq]
    simp

theorem integral_quadrant (a b : ℕ) (g : ℝ → ℝ) :
    ∫ z in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), quadIntegrand a b g z =
      (∫ r in Set.Ioi (0 : ℝ), r ^ (a + b + 1) * Real.exp (-(r ^ 2 / 2))) *
        ∫ θ in Set.Ioo 0 (Real.pi / 2), angProfile a b g θ := by
  rw [← integral_indicator (measurableSet_Ioi.prod measurableSet_Ioi),
    ← integral_comp_polarCoord_symm]
  rw [setIntegral_congr_fun polarCoord.open_target.measurableSet
    (fun p hp => quadIntegrand_polar a b g hp)]
  have htarget : polarCoord.target = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi := rfl
  rw [htarget, Measure.volume_eq_prod,
    setIntegral_prod_mul (fun r : ℝ => r ^ (a + b + 1) * Real.exp (-(r ^ 2 / 2)))
      ((Set.Ioo 0 (Real.pi / 2)).indicator (angProfile a b g)), setIntegral_indicator measurableSet_Ioo,
    Set.inter_eq_right.2]
  intro θ hθ
  exact ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩

end

end PDE.FHLane
