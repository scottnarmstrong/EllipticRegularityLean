module

public import PDEFoundation.Monotonicity.Core.FrequencyMonoMonotone
import PDEFoundation.Monotonicity.MonoSqBalls.Growth
import PDEFoundation.Monotonicity.MonoSqBalls.SphereBound
import PDEFoundation.Monotonicity.GrowthFromFrequency.LogMean
import PDEFoundation.Monotonicity.Core.Dichotomy
import PDEFoundation.Monotonicity.Core.BallDivergence
import PDEFoundation.Monotonicity.Core.RellichSphere

/-!
# The frequency of a nonconstant harmonic function vanishing at the origin is at least one

`u` is Lipschitz at `0` with `u 0 = 0`, so `m(s) = ⨍_{∂B_s} u² ≤ K s²`; combined with the first
growth inequality `(s/r)^(2N(r)) m(r) ≤ m(s)` this forces `N(r) ≥ 1`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace PDE.MonoSqBalls

variable {d : ℕ} {u : Vec d → ℝ} {R : ℝ}

/-- Quadratic bound for the sphere means of `u²` near `0`. -/
theorem exists_sphereMean_sq_le (hd : 0 < d) (hR : 0 < R)
    (hu : ContDiffOn ℝ 2 u (euclideanBall 0 R)) (hu0 : u 0 = 0) :
    ∃ K ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε →
      sphereMean (0 : Vec d) s (fun x => u x ^ 2) ≤ K * s ^ 2 := by
  have : NeZero d := ⟨hd.ne'⟩
  have h0 : (0 : Vec d) ∈ euclideanBall (0 : Vec d) R := by
    have h : vecNormSq (0 : Vec d) = 0 := by simp [vecNormSq, vecDot]
    rw [mem_euclideanBall_zero_iff, h]; positivity
  have hca : ContDiffAt ℝ 1 u 0 :=
    ((hu.contDiffAt ((isOpen_euclideanBall (0 : Vec d) R).mem_nhds h0))).of_le (by norm_num)
  obtain ⟨K, t, ht, hlip⟩ := hca.exists_lipschitzOnWith
  obtain ⟨ε, hε, hεt⟩ := Metric.mem_nhds_iff.mp ht
  refine ⟨(K : ℝ) ^ 2, min ε R, lt_min hε hR, fun s hs hsε => ?_⟩
  have hsε' : s < ε := hsε.trans_le (min_le_left _ _)
  have hsR : s < R := hsε.trans_le (min_le_right _ _)
  refine sphereMean_le_of_le ((hu.continuousOn.mono ?_).pow 2) (fun x hx => ?_)
  · intro x hx
    rw [mem_euclideanSphere_zero_iff] at hx
    rw [mem_euclideanBall_zero_iff, hx]
    exact pow_lt_pow_left₀ hsR hs.le two_ne_zero
  · rw [mem_euclideanSphere_zero_iff] at hx
    have hxn : ‖x‖ ≤ s := by
      refine (pi_norm_le_iff_of_nonneg hs.le).mpr fun i => ?_
      have := abs_apply_le_vecEuclideanNorm x i
      rwa [vecEuclideanNorm, hx, Real.sqrt_sq hs.le] at this
    have hxt : x ∈ t := hεt (by rw [Metric.mem_ball, dist_zero_right]; exact hxn.trans_lt hsε')
    have h0t : (0 : Vec d) ∈ t := hεt (Metric.mem_ball_self hε)
    have h1 := hlip.dist_le_mul x hxt 0 h0t
    rw [hu0, dist_zero_right, dist_zero_right, Real.norm_eq_abs] at h1
    have h2 : |u x| ≤ K * s := h1.trans (mul_le_mul_of_nonneg_left hxn K.2)
    calc u x ^ 2 = |u x| ^ 2 := (sq_abs _).symm
      _ ≤ (K * s) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
      _ = (K : ℝ) ^ 2 * s ^ 2 := by ring

/-- Positivity of all sphere integrals of `u²` for nonconstant harmonic `u`. -/
theorem sphereIntegral_pos_of_nonconstant (hd : 0 < d)
    (hu : ContDiffOn ℝ 2 u (euclideanBall 0 R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0)
    (hnc : ¬ ∃ c : ℝ, ∀ x ∈ euclideanBall (0 : Vec d) R, u x = c) :
    ∀ r ∈ Ioo (0 : ℝ) R, 0 < sphereIntegral 0 r (fun x => u x ^ 2) := by
  rcases dichotomy_zero_or_sphereIntegral_sq_pos hd hu hharm with h0 | h
  · exact absurd ⟨0, h0⟩ hnc
  · exact h

/-- The Almgren frequency of a nonconstant harmonic function vanishing at `0` is at least `1`. -/
theorem one_le_almgrenFrequency (hd : 0 < d)
    (hu : ContDiffOn ℝ 2 u (euclideanBall 0 R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0)
    (hnc : ¬ ∃ c : ℝ, ∀ x ∈ euclideanBall (0 : Vec d) R, u x = c) (hu0 : u 0 = 0)
    {r : ℝ} (hr : 0 < r) (hrR : r < R) : 1 ≤ almgrenFrequency u r := by
  by_contra hlt
  push Not at hlt
  have hR : 0 < R := hr.trans hrR
  have hpos := sphereIntegral_pos_of_nonconstant hd hu hharm hnc
  obtain ⟨K, ε, hε, hK⟩ := exists_sphereMean_sq_le hd hR hu hu0
  have hmr := LogMean.mean_pos hd hr (hpos r ⟨hr, hrR⟩)
  set e : ℝ := 2 * almgrenFrequency u r with he
  set M := sphereMean (0 : Vec d) r (fun x => u x ^ 2) with hM
  have hc : 0 < 2 - e := by rw [he]; linarith
  have hlim : Tendsto (fun s : ℝ => K * r ^ e * s ^ (2 - e)) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => s ^ (2 - e)) (𝓝 0) (𝓝 ((0 : ℝ) ^ (2 - e))) :=
      (Real.continuousAt_rpow_const 0 (2 - e) (Or.inr hc.le)).tendsto
    rw [Real.zero_rpow hc.ne'] at h1
    simpa using (h1.const_mul (K * r ^ e)).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), K * r ^ e * s ^ (2 - e) < M :=
    (hlim.eventually (gt_mem_nhds hmr))
  have hev2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo 0 (min ε r) := Ioo_mem_nhdsGT (lt_min hε hr)
  obtain ⟨s, hs1, hs3, hs2⟩ := (hev.and hev2).exists
  have hs0 : 0 < s := hs3
  have hsε : s < ε := hs2.trans_le (min_le_left _ _)
  have hsr : s < r := hs2.trans_le (min_le_right _ _)
  have hg := growth_first hd hu hharm hpos hs0 hsr hrR
  have hms := hK s hs0 hsε
  have hrp : 0 < r ^ e := Real.rpow_pos_of_pos hr _
  have hsp : 0 < s ^ e := Real.rpow_pos_of_pos hs0 _
  rw [← he, Real.div_rpow hs0.le hr.le, ← hM] at hg
  have h3 : s ^ e / r ^ e * M ≤ K * s ^ 2 := hg.trans hms
  have h4 : s ^ (2 - e) = s ^ 2 / s ^ e := by
    rw [Real.rpow_sub hs0, Real.rpow_two]
  rw [h4] at hs1
  have h5 : M ≤ K * r ^ e * (s ^ 2 / s ^ e) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hrp] at h3
    rw [mul_div_assoc', le_div_iff₀ hsp]
    nlinarith [h3]
  exact absurd hs1 (not_lt.mpr h5)

end PDE.MonoSqBalls
