module

public import PDEFoundation.Monotonicity.Core.HarmonicLiouville
public import PDEFoundation.Monotonicity.Core.Bridge
import PDEFoundation.Monotonicity.Core.Dichotomy
import PDEFoundation.Measure.BallVolume

/-!
# Liouville theorem, sphere-mean form

The growth hypothesis is phrased with spherical means `sphereMean 0 r (u²) ≤ C r^(2N)`
(`r ≥ 1`), converted to ball averages through the polar formula.
-/

@[expose] public section

open MeasureTheory

namespace PDE

noncomputable section

variable {d : ℕ}

/-- A pointwise-in-radius bound on spherical means bounds the ball average. -/
theorem integralAverage_euclideanBall_le_of_sphereMean_le [NeZero d] {f : Vec d → ℝ}
    (hf : Continuous f) {r K : ℝ} (hr : 0 < r)
    (hmean : ∀ t ∈ Set.Icc (0 : ℝ) r, sphereMean 0 t f ≤ K) :
    integralAverage (euclideanBall (0 : Vec d) r) f ≤ K := by
  have hV := volume_euclideanBall_toReal_pos (0 : Vec d) hr
  have h1 : ∫ y in euclideanBall (0 : Vec d) r, f y =
      ∫ t in (0 : ℝ)..r, sphereIntegral (0 : Vec d) t f :=
    integral_euclideanBall_eq_intervalIntegral_sphereIntegral hf hr
  have h2 : ∫ y in euclideanBall (0 : Vec d) r, (fun _ => K) y =
      ∫ t in (0 : ℝ)..r, sphereIntegral (0 : Vec d) t (fun _ => K) :=
    integral_euclideanBall_eq_intervalIntegral_sphereIntegral continuous_const hr
  have h3 : ∫ t in (0 : ℝ)..r, sphereIntegral (0 : Vec d) t f ≤
      ∫ t in (0 : ℝ)..r, sphereIntegral (0 : Vec d) t (fun _ => K) := by
    refine intervalIntegral.integral_mono_on hr.le
      ((continuous_sphereIntegral hf (0 : Vec d)).intervalIntegrable _ _)
      ((continuous_sphereIntegral continuous_const (0 : Vec d)).intervalIntegrable _ _) fun t ht => ?_
    rw [sphereIntegral_eq_mul_sphereMean, sphereIntegral_const]
    refine mul_le_mul_of_nonneg_left (hmean t ht) ?_
    exact mul_nonneg sphereArea_pos.le (pow_nonneg ht.1 _)
  have h4 : ∫ y in euclideanBall (0 : Vec d) r, f y ≤
      K * (volume (euclideanBall (0 : Vec d) r)).toReal := by
    rw [h1]
    refine h3.trans ?_
    rw [← h2, setIntegral_const, smul_eq_mul, mul_comm]
    simp [Measure.real]
  unfold integralAverage
  rw [inv_mul_le_iff₀ hV]
  linarith

/-- **Liouville theorem, sphere-mean form.** -/
theorem exists_mvPolynomial_of_harmonic_sphereMean_growth (hd : 0 < d) {u : Vec d → ℝ}
    (hu : ContDiff ℝ 2 u) (hharm : ∀ x, euclideanCoordLaplacian u x = 0) {N C : ℝ}
    (hgrow : ∀ r : ℝ, 1 ≤ r → sphereMean (0 : Vec d) r (fun x => u x ^ 2) ≤ C * r ^ (2 * N)) :
    ∃ p : MvPolynomial (Fin d) ℝ, p.totalDegree ≤ ⌊N⌋₊ ∧
      ∀ x, u x = MvPolynomial.eval x p := by
  have : NeZero d := ⟨hd.ne'⟩
  have hc : Continuous fun x => u x ^ 2 := hu.continuous.pow 2
  -- bound on the unit interval of radii
  obtain ⟨E, hE⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_sphereMean hc (0 : Vec d)).continuousOn
  set M : ℝ := max N 0 with hM
  set K : ℝ := max E 0 + max C 0 with hK
  refine (exists_mvPolynomial_of_harmonic_growth (N := M) (C := K) hd hu hharm ?_).imp
    fun p hp => ⟨?_, hp.2⟩
  · intro r hr
    have hr0 : 0 < r := by linarith
    have hrM : 1 ≤ r ^ (2 * M) := Real.one_le_rpow hr (by positivity)
    refine integralAverage_euclideanBall_le_of_sphereMean_le hc hr0 fun t ht => ?_
    have hKn : 0 ≤ K := by rw [hK]; positivity
    rcases le_total t 1 with ht1 | ht1
    · calc sphereMean 0 t (fun x => u x ^ 2) ≤ max E 0 :=
          (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using (hE t ⟨ht.1, ht1⟩).trans (le_max_left E 0))
        _ ≤ K * 1 := by rw [hK, mul_one]; linarith [le_max_right C 0, le_max_left E 0]
        _ ≤ K * r ^ (2 * M) := mul_le_mul_of_nonneg_left hrM hKn
    · calc sphereMean 0 t (fun x => u x ^ 2) ≤ C * t ^ (2 * N) := hgrow t ht1
        _ ≤ max C 0 * t ^ (2 * M) := by
          refine mul_le_mul (le_max_left _ _) ?_ (Real.rpow_nonneg (by linarith) _) (le_max_right _ _)
          exact Real.rpow_le_rpow_of_exponent_le ht1 (by linarith [le_max_left N 0])
        _ ≤ max C 0 * r ^ (2 * M) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) ht.2 (by positivity))
            (le_max_right _ _)
        _ ≤ K * r ^ (2 * M) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [hK]; linarith [le_max_right E 0]
  · refine hp.1.trans (le_of_eq ?_)
    rcases le_total 0 N with h | h
    · rw [hM, max_eq_left h]
    · rw [hM, max_eq_right h, Nat.floor_of_nonpos h]; simp

end

end PDE
