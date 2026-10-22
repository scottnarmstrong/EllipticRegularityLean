module

public import PDEFoundation.Monotonicity.Defs
public import PDEFoundation.Sobolev.ClassicalLaplacian
public import PDEFoundation.Sobolev.Mean
import PDEFoundation.Monotonicity.MonoSqBalls.Growth
import PDEFoundation.Monotonicity.MonoSqBalls.Lower
import PDEFoundation.Monotonicity.MonoSqBalls.Avg
import PDEFoundation.Monotonicity.GrowthFromFrequency.LogMean
import PDEFoundation.Monotonicity.Core.FrequencyMonoMonotone
import PDEFoundation.Monotonicity.Core.BallDivergence

/-!
# Proof of `PDE.mono_sq_balls` (Lemma 2.8)

With `m(t) = ⨍_{∂B_t} u²` and `a(t) = ⨍_{B_t} u²`: `a'(t) = (d/t)(m(t) - a(t))`; the second growth
inequality with `N ≥ 1` gives `m(s) ≤ (s/t)² m(t)`, hence `a(t) ≤ d/(d+2) m(t)` and
`a'(t) ≥ (2/t) a(t)`.  The ball is localized to a globally smooth function to differentiate.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE.MonoSqBallsProof

theorem result (d : ℕ) (hd : 0 < d) (r₀ : ℝ) (hr₀ : 0 < r₀)
    (u : Vec d → ℝ)
    (hu : ContDiffOn ℝ 2 u (euclideanBall (0 : Vec d) r₀))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) r₀, euclideanCoordLaplacian u x = 0)
    (hnc : ¬ ∃ c : ℝ, ∀ x ∈ euclideanBall (0 : Vec d) r₀, u x = c)
    (hu0 : u 0 = 0) :
    ∀ r ∈ Set.Ioo 0 r₀,
      2 / r * integralAverage (euclideanBall (0 : Vec d) r) (fun x => u x ^ 2) ≤
        deriv (fun s : ℝ => integralAverage (euclideanBall (0 : Vec d) s) (fun x => u x ^ 2)) r := by
  have _ := hr₀
  have : NeZero d := ⟨hd.ne'⟩
  intro r ⟨hr, hrR⟩
  have hpos := MonoSqBalls.sphereIntegral_pos_of_nonconstant hd hu hharm hnc
  obtain ⟨ρ', v, hρ1, hρ2, hv, hvu⟩ := exists_contDiff_localization hu hr hrR
  have hρ'0 : 0 < ρ' := hr.trans hρ1
  have hsub : ∀ t : ℝ, 0 ≤ t → t < ρ' → euclideanBall (0 : Vec d) t ⊆ euclideanBall 0 ρ' := by
    intro t ht0 htρ x hx
    rw [mem_euclideanBall_zero_iff] at hx ⊢
    exact hx.trans (pow_lt_pow_left₀ htρ ht0 two_ne_zero)
  have hcongr : ∀ t : ℝ, 0 ≤ t → t < ρ' →
      integralAverage (euclideanBall (0 : Vec d) t) (fun x => u x ^ 2) =
        integralAverage (euclideanBall (0 : Vec d) t) (fun x => v x ^ 2) := by
    intro t ht0 htρ
    unfold integralAverage
    congr 1
    refine setIntegral_congr_fun (isOpen_euclideanBall _ _).measurableSet fun x hx => ?_
    simp only [hvu (hsub t ht0 htρ hx)]
  have hmcongr : ∀ t : ℝ, 0 ≤ t → t < ρ' →
      sphereMean (0 : Vec d) t (fun x => u x ^ 2) = sphereMean 0 t (fun x => v x ^ 2) := by
    intro t ht0 htρ
    refine sphereMean_congr_of_eqOn hρ'0 (by rwa [abs_of_nonneg ht0]) fun x hx => ?_
    simp only [hvu hx]
  have hcv : Continuous fun x => v x ^ 2 := hv.continuous.pow 2
  have hA := MonoSqBalls.hasDerivAt_integralAverage (d := d) hcv hr
  have hA' : HasDerivAt (fun s : ℝ => integralAverage (euclideanBall (0 : Vec d) s) (fun x => u x ^ 2))
      (d / r * (sphereMean (0 : Vec d) r (fun x => u x ^ 2) -
        integralAverage (euclideanBall 0 r) (fun x => u x ^ 2))) r := by
    rw [hcongr r hr.le hρ1, hmcongr r hr.le hρ1]
    refine hA.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hr hρ1] with t ht
    exact hcongr t ht.1.le ht.2
  have hmean : ∀ s ∈ Ioo 0 r, sphereMean (0 : Vec d) s (fun x => v x ^ 2) ≤
      (s / r) ^ 2 * sphereMean 0 r (fun x => v x ^ 2) := by
    intro s hs
    have hsρ : s < ρ' := hs.2.trans hρ1
    rw [← hmcongr s hs.1.le hsρ, ← hmcongr r hr.le hρ1]
    have h1 := MonoSqBalls.growth_second hd hu hharm hpos hs.1 hs.2 hrR
    have hN := MonoSqBalls.one_le_almgrenFrequency hd hu hharm hnc hu0 hs.1 (hs.2.trans hrR)
    have hmr := LogMean.mean_pos hd hr (hpos r ⟨hr, hrR⟩)
    have hsr : s / r ≤ 1 := (div_le_one hr).mpr hs.2.le
    have h2 : (s / r) ^ (2 * almgrenFrequency u s) ≤ (s / r) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge (div_pos hs.1 hr) hsr (by linarith)
    rw [Real.rpow_two] at h2
    exact h1.trans (mul_le_mul_of_nonneg_right h2 hmr.le)
  have hle := MonoSqBalls.integralAverage_le (d := d) hcv hr hmean
  rw [← hcongr r hr.le hρ1, ← hmcongr r hr.le hρ1] at hle
  rw [hA'.deriv]
  set a := integralAverage (euclideanBall (0 : Vec d) r) (fun x => u x ^ 2)
  set m := sphereMean (0 : Vec d) r (fun x => u x ^ 2)
  have hd2 : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  have h3 : ((d : ℝ) + 2) * a ≤ d * m := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hd2] at hle
    linarith
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hr]
  linarith

end PDE.MonoSqBallsProof
