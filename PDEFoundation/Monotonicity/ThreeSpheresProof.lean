module

public import PDEFoundation.Monotonicity.Defs
public import PDEFoundation.Sobolev.ClassicalLaplacian
import PDEFoundation.Monotonicity.GrowthFromFrequency.LogMean

/-!
# Proof of `PDE.three_spheres`

With `m(r) = ⨍_{∂B_r} u²` and `g(t) = log m(eᵗ)`, one has `g' = 2 N(eᵗ)`, which is monotone by
monotonicity of the Almgren frequency; hence `g` is convex.  The case `u ≡ 0` is trivial.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE.ThreeSpheresProof

theorem result (d : ℕ) (hd : 0 < d) (r₀ : ℝ) (hr₀ : 0 < r₀)
    (u : Vec d → ℝ)
    (hu : ContDiffOn ℝ 2 u (euclideanBall (0 : Vec d) r₀))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) r₀, euclideanCoordLaplacian u x = 0) :
    ConvexOn ℝ (Set.Iio (Real.log r₀))
      (fun t : ℝ => Real.log (sphereMean (0 : Vec d) (Real.exp t) (fun x => u x ^ 2))) := by
  have hexp : ∀ t ∈ Iio (Real.log r₀), Real.exp t ∈ Ioo 0 r₀ := fun t ht =>
    ⟨Real.exp_pos t, by rwa [← Real.lt_log_iff_exp_lt hr₀]⟩
  rcases dichotomy_zero_or_sphereIntegral_sq_pos hd hu hharm with h0 | hpos
  · have hm : ∀ t ∈ Iio (Real.log r₀),
        Real.log (sphereMean (0 : Vec d) (Real.exp t) (fun x => u x ^ 2)) = 0 := by
      intro t ht
      have h := hexp t ht
      rw [sphereMean_congr_of_eqOn hr₀ (by rw [abs_of_pos h.1]; exact h.2) (g := fun _ => 0)
        (fun x hx => by simp [h0 x hx])]
      simp [sphereMean]
    exact (convexOn_const (0 : ℝ) (convex_Iio _)).congr (fun t ht => (hm t ht).symm)
  · have hmono := monotoneOn_almgrenFrequency hd hu hharm
    have hder : ∀ t ∈ Iio (Real.log r₀), HasDerivAt
        (fun t : ℝ => Real.log (sphereMean (0 : Vec d) (Real.exp t) (fun x => u x ^ 2)))
        (2 * almgrenFrequency u (Real.exp t)) t := by
      intro t ht
      have h := hexp t ht
      have h1 := (LogMean.hasDerivAt_log_mean hd hu hharm h.1 h.2 (hpos _ h)).scomp t
        (Real.hasDerivAt_exp t)
      have hv : Real.exp t • (2 * almgrenFrequency u (Real.exp t) / Real.exp t) =
          2 * almgrenFrequency u (Real.exp t) := by
        rw [smul_eq_mul]
        field_simp
      rw [hv] at h1
      exact h1
    refine MonotoneOn.convexOn_of_deriv (convex_Iio _) (fun t ht => (hder t ht).continuousAt.continuousWithinAt)
      (fun t ht => ?_) (fun a ha b hb hab => ?_)
    · rw [interior_Iio] at ht
      exact (hder t ht).differentiableAt.differentiableWithinAt
    · rw [interior_Iio] at ha hb
      rw [(hder a ha).deriv, (hder b hb).deriv]
      have := hmono (hexp a ha) (hexp b hb) (Real.exp_le_exp.mpr hab)
      linarith
end PDE.ThreeSpheresProof
