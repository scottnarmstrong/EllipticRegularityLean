module

public import PDEFoundation.Monotonicity.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import PDEFoundation.Sobolev.ClassicalLaplacian
import PDEFoundation.Monotonicity.MonoSqBalls.Growth
import PDEFoundation.Monotonicity.Core.HarmonicLiouvilleSphere
import PDEFoundation.Monotonicity.Core.Dichotomy
import PDEFoundation.Monotonicity.GrowthFromFrequency.LogMean

/-!
# Proof of `PDE.entire_harmonic_polynomial_of_frequency_bound` (Corollary 2.9)

An entire harmonic function of bounded Almgren frequency has sphere means of `u²` growing at most
like `r^(2N)` (first growth inequality with `s = 1`), hence is a polynomial by the Liouville
theorem in sphere-mean form.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE.EntireHarmonicPolynomialProof

theorem result (d : ℕ) (hd : 0 < d) (u : Vec d → ℝ)
    (hu : ContDiff ℝ 2 u) (hharm : ∀ x, euclideanCoordLaplacian u x = 0) (hu0 : u 0 = 0)
    (N : ℝ) (hN : ∀ r : ℝ, 0 < r → almgrenFrequency u r ≤ N) :
    ∃ p : MvPolynomial (Fin d) ℝ, p.totalDegree ≤ ⌊N⌋₊ ∧ ∀ x, u x = MvPolynomial.eval x p := by
  have _ := hu0
  by_cases hz : ∀ x, u x = 0
  · exact ⟨0, by simp, fun x => by simp [hz x]⟩
  push Not at hz
  obtain ⟨x0, hx0⟩ := hz
  refine exists_mvPolynomial_of_harmonic_sphereMean_growth hd hu hharm
    (C := sphereMean (0 : Vec d) 1 (fun x => u x ^ 2)) (N := N) ?_
  intro r hr
  rcases hr.eq_or_lt with rfl | hr1
  · simp
  · set R : ℝ := vecNormSq x0 + r + 1 with hR
    have hq : 0 ≤ vecNormSq x0 := by unfold vecNormSq; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have hR1 : 1 ≤ R := by linarith
    have hrR : r < R := by linarith
    have hx0R : x0 ∈ euclideanBall (0 : Vec d) R := by
      rw [mem_euclideanBall_zero_iff]; nlinarith
    have huR : ContDiffOn ℝ 2 u (euclideanBall (0 : Vec d) R) := hu.contDiffOn
    have hhR : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0 :=
      fun x _ => hharm x
    have hpos : ∀ t ∈ Ioo (0 : ℝ) R, 0 < sphereIntegral 0 t (fun x => u x ^ 2) := by
      rcases dichotomy_zero_or_sphereIntegral_sq_pos hd huR hhR with h0 | h
      · exact absurd (h0 x0 hx0R) hx0
      · exact h
    have h1 := MonoSqBalls.growth_first hd huR hhR hpos one_pos hr1 hrR
    have hr0 : 0 < r := one_pos.trans hr1
    have hm1 := LogMean.mean_pos hd one_pos (hpos 1 ⟨one_pos, hr1.trans hrR⟩)
    have hrp : 0 < r ^ (2 * almgrenFrequency u r) := Real.rpow_pos_of_pos hr0 _
    have h2 : sphereMean (0 : Vec d) r (fun x => u x ^ 2) ≤
        sphereMean (0 : Vec d) 1 (fun x => u x ^ 2) * r ^ (2 * almgrenFrequency u r) := by
      rw [one_div, Real.inv_rpow hr0.le, ← div_eq_inv_mul, div_le_iff₀ hrp] at h1
      exact h1
    have h3 : r ^ (2 * almgrenFrequency u r) ≤ r ^ (2 * N) :=
      Real.rpow_le_rpow_of_exponent_le hr (by linarith [hN r hr0])
    exact h2.trans (mul_le_mul_of_nonneg_left h3 hm1.le)

end PDE.EntireHarmonicPolynomialProof
