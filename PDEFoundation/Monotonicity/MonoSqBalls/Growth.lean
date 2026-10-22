module

public import PDEFoundation.Monotonicity.Core.FrequencyMonoMonotone
import PDEFoundation.Monotonicity.GrowthFromFrequency.LogMean

/-!
# Two-sided growth of the sphere mean of `u²`

Local copy of the growth inequalities
`(s/r)^(2N(r)) m(r) ≤ m(s) ≤ (s/r)^(2N(s)) m(r)` for `m = sphereMean 0 · (u²)`, under the
standing hypothesis that all sphere integrals of `u²` on `(0, R)` are positive.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE.MonoSqBalls

theorem rpow_mul_le_of_log_le {m₁ m₂ s r c : ℝ} (hs : 0 < s) (hr : 0 < r) (h1 : 0 < m₁)
    (h2 : 0 < m₂)
    (h : Real.log m₁ - 2 * c * Real.log r ≤ Real.log m₂ - 2 * c * Real.log s) :
    (s / r) ^ (2 * c) * m₁ ≤ m₂ := by
  have hsr : 0 < s / r := div_pos hs hr
  rw [Real.rpow_def_of_pos hsr, ← Real.exp_log h1, ← Real.exp_add, ← Real.exp_log h2,
    Real.exp_le_exp, Real.log_div hs.ne' hr.ne']
  linarith

theorem le_rpow_mul_of_log_le {m₁ m₂ s r c : ℝ} (hs : 0 < s) (hr : 0 < r) (h1 : 0 < m₁)
    (h2 : 0 < m₂)
    (h : Real.log m₂ - 2 * c * Real.log s ≤ Real.log m₁ - 2 * c * Real.log r) :
    m₂ ≤ (s / r) ^ (2 * c) * m₁ := by
  have hsr : 0 < s / r := div_pos hs hr
  rw [Real.rpow_def_of_pos hsr, ← Real.exp_log h2, ← Real.exp_log h1, ← Real.exp_add,
    Real.exp_le_exp, Real.log_div hs.ne' hr.ne']
  linarith

variable {d : ℕ} {u : Vec d → ℝ} {R : ℝ}

/-- First growth inequality. -/
theorem growth_first (hd : 0 < d) (hu : ContDiffOn ℝ 2 u (euclideanBall 0 R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0)
    (hpos : ∀ r ∈ Ioo (0 : ℝ) R, 0 < sphereIntegral 0 r (fun x => u x ^ 2))
    {s r : ℝ} (hs : 0 < s) (hsr : s < r) (hrR : r < R) :
    (s / r) ^ (2 * almgrenFrequency u r) * sphereMean (0 : Vec d) r (fun x => u x ^ 2) ≤
      sphereMean (0 : Vec d) s (fun x => u x ^ 2) := by
  have hr : 0 < r := hs.trans hsr
  have hmono := monotoneOn_almgrenFrequency hd hu hharm
  have hsI : s ∈ Ioo 0 R := ⟨hs, hsr.trans hrR⟩
  have hrI : r ∈ Ioo 0 R := ⟨hr, hrR⟩
  have hms := LogMean.mean_pos hd hs (hpos s hsI)
  have hmr := LogMean.mean_pos hd hr (hpos r hrI)
  have := LogMean.antitoneOn_phi hd hu hharm hpos (almgrenFrequency u r) hs hrR
    (fun t ht => hmono ⟨hs.trans ht.1, ht.2.trans hrR⟩ hrI ht.2.le)
    ⟨le_rfl, hsr.le⟩ ⟨hsr.le, le_rfl⟩ hsr.le
  exact rpow_mul_le_of_log_le hs hr hmr hms this

/-- Second growth inequality. -/
theorem growth_second (hd : 0 < d) (hu : ContDiffOn ℝ 2 u (euclideanBall 0 R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0)
    (hpos : ∀ r ∈ Ioo (0 : ℝ) R, 0 < sphereIntegral 0 r (fun x => u x ^ 2))
    {s r : ℝ} (hs : 0 < s) (hsr : s < r) (hrR : r < R) :
    sphereMean (0 : Vec d) s (fun x => u x ^ 2) ≤
      (s / r) ^ (2 * almgrenFrequency u s) * sphereMean (0 : Vec d) r (fun x => u x ^ 2) := by
  have hr : 0 < r := hs.trans hsr
  have hmono := monotoneOn_almgrenFrequency hd hu hharm
  have hsI : s ∈ Ioo 0 R := ⟨hs, hsr.trans hrR⟩
  have hrI : r ∈ Ioo 0 R := ⟨hr, hrR⟩
  have hms := LogMean.mean_pos hd hs (hpos s hsI)
  have hmr := LogMean.mean_pos hd hr (hpos r hrI)
  have := LogMean.monotoneOn_phi hd hu hharm hpos (almgrenFrequency u s) hs hrR
    (fun t ht => hmono hsI ⟨hs.trans ht.1, ht.2.trans hrR⟩ ht.1.le)
    ⟨le_rfl, hsr.le⟩ ⟨hsr.le, le_rfl⟩ hsr.le
  exact le_rpow_mul_of_log_le hs hr hmr hms this

end PDE.MonoSqBalls
