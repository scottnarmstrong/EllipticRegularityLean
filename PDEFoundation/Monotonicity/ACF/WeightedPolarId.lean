module

public import PDEFoundation.Monotonicity.ACF.WeightedFlux

/-!
# The limit bound in radial form

`½ ∫_{B_R} u² T₀(|x|²) = ∫_{ρ>0} K₀(ρ²) (-flux(ρ) - ((d-2)/2) a(ρ)) dρ`, and
`K₀(ρ²) = -ker(ρ) / ρ^{d-1}` for `ρ > 0`, where `ker` is the averaging kernel.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace PDE

noncomputable section

variable {r k : ℝ}

theorem acfQ_zero_sq {d : ℕ} (hd : 3 ≤ d) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    acfQ (acfKappa d) 0 (ρ ^ 2) = (ρ ^ (d - 2))⁻¹ := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 3 := ⟨d - 3, by omega⟩
  rcases hρ.eq_or_lt with h0 | hpos
  · subst h0
    have hκ : -acfKappa (n + 3) ≠ 0 := neg_ne_zero.mpr (by
      unfold acfKappa; push_cast; intro h; linarith [Nat.cast_nonneg (α := ℝ) n])
    unfold acfQ
    rw [show ((0 : ℝ) ^ 2 + (0 : ℝ) ^ 2) = 0 by norm_num, Real.zero_rpow hκ,
      show n + 3 - 2 = n + 1 by omega, pow_succ]
    simp
  · unfold acfQ acfKappa
    rw [show (ρ ^ 2 + (0 : ℝ) ^ 2) = ρ ^ (2 : ℝ) by simp]
    rw [← Real.rpow_mul hρ]
    rw [show (2 : ℝ) * -((((n + 3 : ℕ) : ℝ) - 2) / 2) = -((n + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_neg hρ, Real.rpow_natCast, show n + 3 - 2 = n + 1 by omega]

theorem acfK0_sq {d : ℕ} (hd : 2 ≤ d) {ρ : ℝ} (hρ : 0 < ρ) :
    acfK0 d r k (ρ ^ 2) = -(acfKer r k ρ) / ρ ^ (d - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 2 := ⟨d - 2, by omega⟩
  have hs : 0 < ρ ^ 2 := by positivity
  have hder := (hasDerivAt_acfCut (r := r) (k := k) hs).deriv
  rw [Real.sqrt_sq hρ.le] at hder
  have hQ : acfQ (acfKappa (n + 2)) 0 (ρ ^ 2) = (ρ ^ n)⁻¹ := by
    unfold acfQ acfKappa
    rw [show (ρ ^ 2 + (0 : ℝ) ^ 2) = ρ ^ (2 : ℝ) by simp]
    rw [← Real.rpow_mul hρ.le]
    rw [show (2 : ℝ) * -((((n + 2 : ℕ) : ℝ) - 2) / 2) = -(n : ℝ) by push_cast; ring,
      Real.rpow_neg hρ.le, Real.rpow_natCast]
  unfold acfK0
  rw [hder, hQ, show n + 2 - 1 = n + 1 by omega, pow_succ]
  field_simp

/-- **Radial form of the limit bound.** -/
theorem acf_half_T_polar {d : ℕ} (hd : 3 ≤ d) {R : ℝ} (hr : 0 < r) (hk : 0 < k)
    (hrk : r + k < R) (u : H1Function (euclideanBall (0 : Vec d) R))
    (hcont : ContinuousOn u.toFun (euclideanBall (0 : Vec d) R)) :
    (1 / 2) * ∫ x in euclideanBall (0 : Vec d) R, u.toFun x ^ 2 * acfT d r k 0 (vecNormSq x) =
      ∫ ρ in Ioi (0 : ℝ), acfK0 d r k (ρ ^ 2) *
        (-(acfSliceFlux u.toFun u.grad ρ) - (((d : ℝ) - 2) / 2) * acfSliceMass u.toFun ρ) := by
  have : NeZero d := ⟨by omega⟩
  have hR : 0 < R := by linarith
  have hρ₂ : (0 : ℝ) ≤ r + k := by positivity
  have hK0 : ∀ s, (r + k) ^ 2 < s → acfK0 d r k s = 0 := fun s hs => acfK0_eq_zero hk hs
  have hKc : Continuous (acfK0 d r k) := (contDiff_acfK0 hr hk).continuous
  rw [acf_half_T_eq hr hk hrk u hcont]
  have hflux := integrableOn_radial_flux u hKc hρ₂ hK0
  have hmass : IntegrableOn (fun x => acfK0 d r k (vecNormSq x) * u.toFun x ^ 2)
      (euclideanBall (0 : Vec d) R) := by
    have := integrableOn_sq_mul_radial u (G := acfK0 d r k) hKc.continuousOn hρ₂ hK0
    simpa only [mul_comm] using this
  obtain ⟨hI1, hE1⟩ := ball_polar_radial hR.le hρ₂ hrk hK0 hflux
  obtain ⟨hI2, hE2⟩ := ball_polar_radial hR.le hρ₂ hrk hK0 hmass
  have e1 : ∫ x in euclideanBall (0 : Vec d) R,
      u.toFun x * (acfK0 d r k (vecNormSq x) * vecDot x (u.grad x)) =
      ∫ ρ in Ioi (0 : ℝ), acfK0 d r k (ρ ^ 2) * acfSliceFlux u.toFun u.grad ρ := by
    unfold acfSliceFlux
    rw [← hE1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  have e2 : ∫ x in euclideanBall (0 : Vec d) R, u.toFun x ^ 2 * acfK0 d r k (vecNormSq x) =
      ∫ ρ in Ioi (0 : ℝ), acfK0 d r k (ρ ^ 2) * acfSliceMass u.toFun ρ := by
    unfold acfSliceMass
    rw [← hE2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  have hI1' : IntegrableOn (fun ρ => acfK0 d r k (ρ ^ 2) * acfSliceFlux u.toFun u.grad ρ)
      (Ioi (0 : ℝ)) := hI1
  have hI2' : IntegrableOn (fun ρ => acfK0 d r k (ρ ^ 2) * acfSliceMass u.toFun ρ)
      (Ioi (0 : ℝ)) := hI2
  have hI1n : IntegrableOn (fun ρ => -(acfK0 d r k (ρ ^ 2) * acfSliceFlux u.toFun u.grad ρ))
      (Ioi (0 : ℝ)) := hI1'.neg
  rw [e1, e2, ← integral_neg, ← integral_const_mul,
    ← integral_sub hI1n (hI2'.const_mul (((d : ℝ) - 2) / 2))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ρ => ?_)
  ring

end

end PDE
