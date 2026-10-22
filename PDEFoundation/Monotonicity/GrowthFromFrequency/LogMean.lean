module

public import PDEFoundation.Monotonicity.Core.FrequencyMonoMonotone

/-!
# Logarithmic derivative of the sphere mean of `u²`

For harmonic `u` on `B_R` with `u² ` having positive sphere integrals, `log m` has derivative
`2 N / r` where `m = sphereMean 0 r (u²)` and `N` is the Almgren frequency.  Consequences: the
function `log m(t) - 2 c log t` is monotone on `[s, r]` according to the sign of `N - c`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE.LogMean

noncomputable section

variable {d : ℕ} {u : Vec d → ℝ} {R : ℝ}

theorem mean_pos (hd : 0 < d) {r : ℝ} (hr : 0 < r)
    (hpos : 0 < sphereIntegral 0 r (fun x => u x ^ 2)) :
    0 < sphereMean (0 : Vec d) r (fun x => u x ^ 2) := by
  have : NeZero d := ⟨hd.ne'⟩
  rw [sphereIntegral_eq_mul_sphereMean] at hpos
  exact (mul_pos_iff_of_pos_left (mul_pos sphereArea_pos (pow_pos hr _))).mp hpos

theorem hasDerivAt_log_mean (hd : 0 < d)
    (hu : ContDiffOn ℝ 2 u (euclideanBall 0 R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0)
    {r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hpos : 0 < sphereIntegral 0 r (fun x => u x ^ 2)) :
    HasDerivAt (fun s => Real.log (sphereMean 0 s (fun x => u x ^ 2)))
      (2 * almgrenFrequency u r / r) r := by
  have : NeZero d := ⟨hd.ne'⟩
  have hm := mean_pos hd hr hpos
  have h := (hasDerivAt_sphereMean_sq hd hu hharm hr hrR).log hm.ne'
  convert h using 1
  have hσ := sphereArea_pos (d := d)
  have hH := sphereIntegral_eq_mul_sphereMean (0 : Vec d) r (fun x => u x ^ 2)
  unfold almgrenFrequency
  rw [hH]
  have : 0 < sphereArea d * r ^ (d - 1) := mul_pos hσ (pow_pos hr _)
  field_simp

/-- Derivative of `log m(t) - 2 c log t`. -/
theorem hasDerivAt_phi (hd : 0 < d)
    (hu : ContDiffOn ℝ 2 u (euclideanBall 0 R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0)
    {r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hpos : 0 < sphereIntegral 0 r (fun x => u x ^ 2)) (c : ℝ) :
    HasDerivAt (fun t => Real.log (sphereMean 0 t (fun x => u x ^ 2)) - 2 * c * Real.log t)
      (2 * (almgrenFrequency u r - c) / r) r := by
  have h := (hasDerivAt_log_mean hd hu hharm hr hrR hpos).sub
    ((Real.hasDerivAt_log hr.ne').const_mul (2 * c))
  convert h using 1
  field_simp

theorem continuousOn_phi (hd : 0 < d)
    (hu : ContDiffOn ℝ 2 u (euclideanBall 0 R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0)
    (hpos : ∀ r ∈ Ioo (0 : ℝ) R, 0 < sphereIntegral 0 r (fun x => u x ^ 2)) (c : ℝ)
    {a b : ℝ} (h : Icc a b ⊆ Ioo 0 R) :
    ContinuousOn (fun t => Real.log (sphereMean 0 t (fun x => u x ^ 2)) - 2 * c * Real.log t)
      (Icc a b) := fun t ht =>
  (hasDerivAt_phi hd hu hharm (h ht).1 (h ht).2 (hpos t (h ht)) c).continuousAt.continuousWithinAt

/-- If `N ≤ c` on `(s, r)` then `φ_c` is antitone on `[s, r]`. -/
theorem antitoneOn_phi (hd : 0 < d)
    (hu : ContDiffOn ℝ 2 u (euclideanBall 0 R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0)
    (hpos : ∀ r ∈ Ioo (0 : ℝ) R, 0 < sphereIntegral 0 r (fun x => u x ^ 2)) (c : ℝ)
    {s r : ℝ} (hs : 0 < s) (hrR : r < R)
    (hN : ∀ t ∈ Ioo s r, almgrenFrequency u t ≤ c) :
    AntitoneOn (fun t => Real.log (sphereMean 0 t (fun x => u x ^ 2)) - 2 * c * Real.log t)
      (Icc s r) := by
  have hsub : Icc s r ⊆ Ioo 0 R := fun t ht => ⟨hs.trans_le ht.1, ht.2.trans_lt hrR⟩
  refine antitoneOn_of_deriv_nonpos (convex_Icc s r) (continuousOn_phi hd hu hharm hpos c hsub)
    (fun t ht => ?_) (fun t ht => ?_)
  · rw [interior_Icc] at ht
    exact (hasDerivAt_phi hd hu hharm (hsub (Ioo_subset_Icc_self ht)).1
      (hsub (Ioo_subset_Icc_self ht)).2 (hpos t (hsub (Ioo_subset_Icc_self ht))) c
      ).differentiableAt.differentiableWithinAt
  · rw [interior_Icc] at ht
    have ht' := hsub (Ioo_subset_Icc_self ht)
    rw [(hasDerivAt_phi hd hu hharm ht'.1 ht'.2 (hpos t ht') c).deriv]
    have := hN t ht
    have : 0 < t := ht'.1
    apply div_nonpos_of_nonpos_of_nonneg <;> linarith

/-- If `c ≤ N` on `(s, r)` then `φ_c` is monotone on `[s, r]`. -/
theorem monotoneOn_phi (hd : 0 < d)
    (hu : ContDiffOn ℝ 2 u (euclideanBall 0 R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0)
    (hpos : ∀ r ∈ Ioo (0 : ℝ) R, 0 < sphereIntegral 0 r (fun x => u x ^ 2)) (c : ℝ)
    {s r : ℝ} (hs : 0 < s) (hrR : r < R)
    (hN : ∀ t ∈ Ioo s r, c ≤ almgrenFrequency u t) :
    MonotoneOn (fun t => Real.log (sphereMean 0 t (fun x => u x ^ 2)) - 2 * c * Real.log t)
      (Icc s r) := by
  have hsub : Icc s r ⊆ Ioo 0 R := fun t ht => ⟨hs.trans_le ht.1, ht.2.trans_lt hrR⟩
  refine monotoneOn_of_deriv_nonneg (convex_Icc s r) (continuousOn_phi hd hu hharm hpos c hsub)
    (fun t ht => ?_) (fun t ht => ?_)
  · rw [interior_Icc] at ht
    exact (hasDerivAt_phi hd hu hharm (hsub (Ioo_subset_Icc_self ht)).1
      (hsub (Ioo_subset_Icc_self ht)).2 (hpos t (hsub (Ioo_subset_Icc_self ht))) c
      ).differentiableAt.differentiableWithinAt
  · rw [interior_Icc] at ht
    have ht' := hsub (Ioo_subset_Icc_self ht)
    rw [(hasDerivAt_phi hd hu hharm ht'.1 ht'.2 (hpos t ht') c).deriv]
    have := hN t ht
    have : 0 < t := ht'.1
    apply div_nonneg <;> linarith

end

end PDE.LogMean
