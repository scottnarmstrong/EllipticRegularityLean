module

public import PDEFoundation.Monotonicity.FriedlandHayman.Transport.Change
public import PDEFoundation.Monotonicity.FriedlandHayman.Transport.LipBarta

/-!
# Friedland--Hayman: cap-to-Gaussian transport bound

If `h` is Lipschitz on `ℝ`, vanishes on `[θ₀, ∞)`, and the cap of radius `θ₀` has fractional measure
at most the Gaussian tail `γ((t, ∞))`, then the Rayleigh quotient of `h` against `sin^{D-2}` is at
least `(D - 2) β(t)`.  Proof: pull `h` back to the Gaussian line along the contraction `tmap D`,
apply the Lipschitz Barta inequality, and push forward again.
-/

@[expose] public section

open Set MeasureTheory Filter Topology

namespace PDE.FHLane

open Transp

noncomputable section

theorem cap_gauss_bound {D : ℕ} (hD : 3 ≤ D) {K : NNReal} {h : ℝ → ℝ} (hh : LipschitzWith K h)
    {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo 0 Real.pi) (hz : ∀ φ, θ₀ ≤ φ → h φ = 0)
    {t : ℝ} (ht : capFrac D θ₀ ≤ gaussTail t) :
    ((D : ℝ) - 2) * gaussBeta t * ∫ φ in (0 : ℝ)..Real.pi, h φ ^ 2 * sinW D φ ≤
      ∫ φ in (0 : ℝ)..Real.pi, deriv h φ ^ 2 * sinW D φ := by
  have hr := rootD_pos hD
  have hκ : ((D : ℝ) - 2) = rootD D ^ 2 := by
    rw [rootD_sq, Nat.cast_sub (by omega : 2 ≤ D)]
    norm_num
  have hc : 0 ≤ zTot D / gTot := (div_pos (zTot_pos D) gTot_pos).le
  have hgL : LipschitzWith (K * Real.toNNReal (rootD D)⁻¹) (fun s => h (tmap D s)) :=
    hh.comp (tmap_lipschitz hD)
  have hzg : ∀ s, s ≤ t → h (tmap D s) = 0 := by
    intro s hst
    by_contra hne
    have hlt : tmap D s < θ₀ := by
      by_contra hge
      exact hne (hz _ (not_lt.1 hge))
    have h1 := (strictMonoOn_capFrac D) (Ioo_subset_Icc_self (tmap_mem D s))
      (Ioo_subset_Icc_self hθ₀) hlt
    rw [capFrac_tmap] at h1
    have h2 : gaussTail t ≤ gaussTail s := strictAnti_gaussTail.antitone hst
    linarith
  have hB := gaussBeta_barta_lipschitz hgL hzg
  have E1 : ∫ φ in (0 : ℝ)..Real.pi, h φ ^ 2 * sinW D φ =
      (zTot D / gTot) * ∫ s, h (tmap D s) ^ 2 * gaussW s := by
    rw [intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ioc_eq_integral_Ioo]
    exact integral_tmap hD (fun φ => h φ ^ 2)
  have E2 : ∫ φ in (0 : ℝ)..Real.pi, deriv h φ ^ 2 * sinW D φ =
      (zTot D / gTot) * ∫ s, deriv h (tmap D s) ^ 2 * gaussW s := by
    rw [intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ioc_eq_integral_Ioo]
    exact integral_tmap hD (fun φ => deriv h φ ^ 2)
  have hN : volume {φ | ¬ DifferentiableAt ℝ h φ} = 0 := ae_iff.1 hh.ae_differentiableAt_real
  have hae : ∀ᵐ s, deriv (fun s => h (tmap D s)) s ^ 2 ≤
      (rootD D ^ 2)⁻¹ * deriv h (tmap D s) ^ 2 := by
    filter_upwards [ae_tmap_not_mem hD hN] with s hs
    have hd : DifferentiableAt ℝ h (tmap D s) := by
      by_contra hc'
      exact hs hc'
    have hder := hd.hasDerivAt.comp s (hasDerivAt_tmap D s)
    have hder' : deriv (fun s => h (tmap D s)) s = deriv h (tmap D s) * dtmap D s := hder.deriv
    rw [hder', mul_pow]
    have hq : dtmap D s ^ 2 ≤ (rootD D ^ 2)⁻¹ := by
      rw [← one_div, le_div_iff₀ (pow_pos hr 2)]
      exact dtmap_sq_le hD s
    calc deriv h (tmap D s) ^ 2 * dtmap D s ^ 2
        ≤ deriv h (tmap D s) ^ 2 * (rootD D ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left hq (sq_nonneg _)
      _ = _ := mul_comm _ _
  have hK : ∀ x, ‖deriv h x‖ ≤ K := fun x => norm_deriv_le_of_lipschitz hh
  have hu : Integrable fun s => deriv h (tmap D s) ^ 2 * gaussW s := by
    refine Integrable.mono' (integrable_gaussW.const_mul ((K : ℝ) ^ 2)) ?_
      (Eventually.of_forall fun s => ?_)
    · exact (((measurable_deriv h).comp (continuous_tmap D).measurable).pow_const 2).mul
        continuous_gaussW.measurable |>.aestronglyMeasurable
    · have hw := gaussW_pos s
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_right ?_ hw.le
      have := hK (tmap D s)
      rw [Real.norm_eq_abs] at this
      calc deriv h (tmap D s) ^ 2 = |deriv h (tmap D s)| ^ 2 := (sq_abs _).symm
        _ ≤ (K : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
  have hI2 : ∫ s in Set.Ioi t, deriv (fun s => h (tmap D s)) s ^ 2 * gaussW s ≤
      (rootD D ^ 2)⁻¹ * ∫ s, deriv h (tmap D s) ^ 2 * gaussW s := by
    calc ∫ s in Set.Ioi t, deriv (fun s => h (tmap D s)) s ^ 2 * gaussW s
        ≤ ∫ s in Set.Ioi t, (rootD D ^ 2)⁻¹ * (deriv h (tmap D s) ^ 2 * gaussW s) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun s => ?_)
            (hu.const_mul _).integrableOn (ae_restrict_of_ae ?_)
          · have := gaussW_pos s
            positivity
          · filter_upwards [hae] with s hs
            calc deriv (fun s => h (tmap D s)) s ^ 2 * gaussW s
                ≤ ((rootD D ^ 2)⁻¹ * deriv h (tmap D s) ^ 2) * gaussW s :=
                  mul_le_mul_of_nonneg_right hs (gaussW_pos s).le
              _ = _ := by ring
      _ = (rootD D ^ 2)⁻¹ * ∫ s in Set.Ioi t, deriv h (tmap D s) ^ 2 * gaussW s :=
          integral_const_mul _ _
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left (setIntegral_le_integral hu
            (Eventually.of_forall fun s => ?_)) (by positivity)
          have := gaussW_pos s
          positivity
  have key : rootD D ^ 2 * (gaussBeta t * ∫ s, h (tmap D s) ^ 2 * gaussW s) ≤
      ∫ s, deriv h (tmap D s) ^ 2 * gaussW s := by
    have h3 := mul_le_mul_of_nonneg_left (hB.trans hI2) (sq_nonneg (rootD D))
    have hne : rootD D ^ 2 ≠ 0 := (pow_pos hr 2).ne'
    rw [← mul_assoc _ ((rootD D ^ 2)⁻¹), mul_inv_cancel₀ hne, one_mul] at h3
    linarith
  rw [hκ, E1, E2]
  calc rootD D ^ 2 * gaussBeta t * ((zTot D / gTot) * ∫ s, h (tmap D s) ^ 2 * gaussW s)
      = (zTot D / gTot) * (rootD D ^ 2 * (gaussBeta t * ∫ s, h (tmap D s) ^ 2 * gaussW s)) := by
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left key hc

end

end PDE.FHLane
