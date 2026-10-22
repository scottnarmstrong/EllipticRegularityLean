module

public import PDEFoundation.Monotonicity.Defs
public import PDEFoundation.Sobolev.ClassicalLaplacian
import PDEFoundation.Monotonicity.GrowthFromFrequency.LogMean

/-!
# Proof of `PDE.growth_from_frequency` (Corollary 2.9)

Two-sided growth of the sphere mean of `u²` from the Almgren frequency: with `m = ⨍_{∂B_r} u²`
and `φ_c(t) = log m(t) - 2 c log t`, `φ_c' = 2 (N - c) / t`, so `φ_{N(r)}` is antitone and
`φ_{N(s)}` monotone on `[s, r]` by monotonicity of `N`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE.GrowthFromFrequencyProof

private theorem rpow_mul_le_iff {m₁ m₂ s r c : ℝ} (hs : 0 < s) (hr : 0 < r) (h1 : 0 < m₁)
    (h2 : 0 < m₂) :
    (Real.log m₁ - 2 * c * Real.log r ≤ Real.log m₂ - 2 * c * Real.log s) →
      (s / r) ^ (2 * c) * m₁ ≤ m₂ := by
  intro h
  have hsr : 0 < s / r := div_pos hs hr
  rw [Real.rpow_def_of_pos hsr, ← Real.exp_log h1, ← Real.exp_add, ← Real.exp_log h2,
    Real.exp_le_exp, Real.log_div hs.ne' hr.ne']
  linarith

private theorem le_rpow_mul_iff {m₁ m₂ s r c : ℝ} (hs : 0 < s) (hr : 0 < r) (h1 : 0 < m₁)
    (h2 : 0 < m₂) :
    (Real.log m₂ - 2 * c * Real.log s ≤ Real.log m₁ - 2 * c * Real.log r) →
      m₂ ≤ (s / r) ^ (2 * c) * m₁ := by
  intro h
  have hsr : 0 < s / r := div_pos hs hr
  rw [Real.rpow_def_of_pos hsr, ← Real.exp_log h2, ← Real.exp_log h1, ← Real.exp_add,
    Real.exp_le_exp, Real.log_div hs.ne' hr.ne']
  linarith

theorem result (d : ℕ) (hd : 0 < d) (R : ℝ) (hR : 0 < R)
    (u : Vec d → ℝ)
    (hu : ContDiffOn ℝ 2 u (euclideanBall (0 : Vec d) R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0)
    (hu0 : u 0 = 0) :
    ∀ s r : ℝ, 0 < s → s < r → r < R →
      (s / r) ^ (2 * almgrenFrequency u r) * sphereMean (0 : Vec d) r (fun x => u x ^ 2) ≤
          sphereMean (0 : Vec d) s (fun x => u x ^ 2) ∧
        sphereMean (0 : Vec d) s (fun x => u x ^ 2) ≤
          (s / r) ^ (2 * almgrenFrequency u s) * sphereMean (0 : Vec d) r (fun x => u x ^ 2) := by
  have _ := hu0
  intro s r hs hsr hrR
  have hr : 0 < r := hs.trans hsr
  rcases dichotomy_zero_or_sphereIntegral_sq_pos hd hu hharm with h0 | hpos
  · have hm : ∀ t, |t| < R → sphereMean (0 : Vec d) t (fun x => u x ^ 2) = 0 := by
      intro t ht
      rw [sphereMean_congr_of_eqOn hR ht (g := fun _ => 0) (fun x hx => by simp [h0 x hx])]
      simp [sphereMean]
    rw [hm r (by rw [abs_of_pos hr]; exact hrR), hm s (by rw [abs_of_pos hs]; linarith)]
    simp
  · have hmono := monotoneOn_almgrenFrequency hd hu hharm
    have hsI : s ∈ Ioo 0 R := ⟨hs, hsr.trans hrR⟩
    have hrI : r ∈ Ioo 0 R := ⟨hr, hrR⟩
    have hms := LogMean.mean_pos hd hs (hpos s hsI)
    have hmr := LogMean.mean_pos hd hr (hpos r hrI)
    constructor
    · have := LogMean.antitoneOn_phi hd hu hharm hpos (almgrenFrequency u r) hs hrR
        (fun t ht => hmono ⟨hs.trans ht.1, ht.2.trans hrR⟩ hrI ht.2.le)
        ⟨le_rfl, hsr.le⟩ ⟨hsr.le, le_rfl⟩ hsr.le
      exact rpow_mul_le_iff hs hr hmr hms this
    · have := LogMean.monotoneOn_phi hd hu hharm hpos (almgrenFrequency u s) hs hrR
        (fun t ht => hmono hsI ⟨hs.trans ht.1, ht.2.trans hrR⟩ ht.1.le)
        ⟨le_rfl, hsr.le⟩ ⟨hsr.le, le_rfl⟩ hsr.le
      exact le_rpow_mul_iff hs hr hmr hms this

end PDE.GrowthFromFrequencyProof
