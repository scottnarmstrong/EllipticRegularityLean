module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # One dimensional logarithmic radial moments -/

@[expose] public section

namespace PDE

open MeasureTheory Set

noncomputable section

private def expRadius (R : ℝ) (t : ℝ) : ℝ := R * Real.exp (-t)

private theorem expRadius_image_Ioi {R : ℝ} (hR : 0 < R) :
    expRadius R '' Ioi 0 = Ioo 0 R := by
  ext r
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨mul_pos hR (Real.exp_pos _), ?_⟩
    have ht0 : 0 < t := ht
    have he : Real.exp (-t) < 1 := (Real.exp_lt_one_iff).2 (neg_neg_of_pos ht0)
    simpa only [expRadius, mul_one] using mul_lt_mul_of_pos_left he hR
  · intro hr
    let t := -Real.log (r / R)
    have hratio : 0 < r / R := div_pos hr.1 hR
    have hratioOne : r / R < 1 := (div_lt_one hR).2 hr.2
    have ht : 0 < t := by
      dsimp only [t]
      exact neg_pos.mpr (Real.log_neg hratio hratioOne)
    refine ⟨t, ht, ?_⟩
    dsimp only [expRadius, t]
    rw [neg_neg, Real.exp_log hratio]
    field_simp

private theorem expRadius_injOn_Ioi {R : ℝ} (hR : 0 < R) :
    InjOn (expRadius R) (Ioi 0) := by
  intro x hx y hy hxy
  dsimp only [expRadius] at hxy
  have heq : Real.exp (-x) = Real.exp (-y) :=
    (mul_left_cancel₀ hR.ne' hxy)
  exact neg_injective (Real.exp_injective heq)

private theorem expRadius_hasDerivWithinAt (R : ℝ) (t : ℝ) :
    HasDerivWithinAt (expRadius R) (-R * Real.exp (-t)) (Ioi 0) t := by
  apply HasDerivAt.hasDerivWithinAt
  simpa [expRadius] using!
    (hasDerivAt_const t R).mul ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t))

private theorem expRadius_transform {D R p t : ℝ}
    (hR : 0 < R) (ht : t ∈ Ioi (0 : ℝ)) :
    |-R * Real.exp (-t)| *
        ((expRadius R t) ^ (D - 1) *
          (-Real.log (expRadius R t / R)) ^ p) =
      R ^ D * (t ^ p * Real.exp (-(D * t))) := by
  have ht0 : 0 < t := ht
  have he : 0 < Real.exp (-t) := Real.exp_pos _
  have hphi : 0 < expRadius R t := mul_pos hR he
  have hquot : expRadius R t / R = Real.exp (-t) := by
    dsimp only [expRadius]
    field_simp
  have habs : |-R * Real.exp (-t)| = R * Real.exp (-t) := by
    rw [abs_of_neg (mul_neg_of_neg_of_pos (neg_neg_of_pos hR) (Real.exp_pos _))]
    ring
  rw [habs, hquot, Real.log_exp, neg_neg]
  rw [show expRadius R t = R * Real.exp (-t) by rfl,
    Real.mul_rpow hR.le he.le, Real.rpow_def_of_pos he, Real.log_exp]
  have hRpow : R * R ^ (D - 1) = R ^ D := by
    calc
      R * R ^ (D - 1) = R ^ (1 : ℝ) * R ^ (D - 1) := by rw [Real.rpow_one]
      _ = R ^ (1 + (D - 1)) := (Real.rpow_add hR 1 (D - 1)).symm
      _ = R ^ D := by ring_nf
  calc
    R * Real.exp (-t) *
        (R ^ (D - 1) * Real.exp (-t * (D - 1)) * t ^ p) =
        (R * R ^ (D - 1)) * t ^ p *
          (Real.exp (-t) * Real.exp (-t * (D - 1))) := by ring
    _ = R ^ D * (t ^ p * Real.exp (-(D * t))) := by
      rw [hRpow, ← Real.exp_add]
      have hexp : -t + -t * (D - 1) = -(D * t) := by ring
      rw [hexp]
      ring

private theorem integrableOn_gamma_scaled {D p : ℝ}
    (hD : 0 < D) (hp : -1 < p) :
    IntegrableOn (fun t : ℝ => t ^ p * Real.exp (-(D * t))) (Ioi 0) := by
  have hgamma : IntegrableOn
      (fun y : ℝ => Real.exp (-y) * y ^ p) (Ioi 0) := by
    simpa only [add_sub_cancel_right] using
      Real.GammaIntegral_convergent (by linarith : 0 < p + 1)
  have hcomp : IntegrableOn
      (fun t : ℝ => Real.exp (-(D * t)) * (D * t) ^ p) (Ioi 0) := by
    have hgamma' : IntegrableOn
        (fun y : ℝ => Real.exp (-y) * y ^ p) (Ioi (D * 0)) := by
      simpa using hgamma
    simpa only [mul_zero] using (integrableOn_Ioi_comp_mul_left_iff
      (fun y : ℝ => Real.exp (-y) * y ^ p) 0 hD).2 hgamma'
  have hDp : 0 < D ^ p := Real.rpow_pos_of_pos hD p
  apply (hcomp.const_mul ((D ^ p)⁻¹)).congr
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  rw [Real.mul_rpow hD.le ht0.le]
  field_simp

/-- The logarithmic radial density is genuinely integrable on `(0,R)`. -/
theorem integrableOn_radial_log_moment
    {D R p : ℝ} (hD : 0 < D) (hR : 0 < R) (hp : -1 < p) :
    IntegrableOn
      (fun r : ℝ => r ^ (D - 1) * (-Real.log (r / R)) ^ p)
      (Ioo 0 R) := by
  let g : ℝ → ℝ := fun r =>
    r ^ (D - 1) * (-Real.log (r / R)) ^ p
  rw [← expRadius_image_Ioi hR]
  rw [integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun t _ => expRadius_hasDerivWithinAt R t) (expRadius_injOn_Ioi hR) g]
  have hbase := (integrableOn_gamma_scaled hD hp).const_mul (R ^ D)
  apply hbase.congr
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  simpa only [smul_eq_mul] using (expRadius_transform hR ht).symm

/-- Exact one dimensional logarithmic radial moment. -/
theorem integral_radial_log_moment
    {D R p : ℝ} (hD : 0 < D) (hR : 0 < R) (hp : -1 < p) :
    (∫ r in Ioo (0 : ℝ) R,
      r ^ (D - 1) * (-Real.log (r / R)) ^ p) =
      R ^ D * Real.Gamma (p + 1) / D ^ (p + 1) := by
  let g : ℝ → ℝ := fun r =>
    r ^ (D - 1) * (-Real.log (r / R)) ^ p
  rw [← expRadius_image_Ioi hR]
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun t _ => expRadius_hasDerivWithinAt R t) (expRadius_injOn_Ioi hR) g]
  have hcongr : (∫ t in Ioi (0 : ℝ),
      |-R * Real.exp (-t)| • g (expRadius R t)) =
      ∫ t in Ioi (0 : ℝ),
        R ^ D * (t ^ p * Real.exp (-(D * t))) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change |-R * Real.exp (-t)| * g (expRadius R t) = _
    exact expRadius_transform hR ht
  rw [hcongr, integral_const_mul]
  rw [show p = (p + 1) - 1 by ring,
    Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith : 0 < p + 1) hD]
  ring_nf
  rw [Real.inv_rpow hD.le]
  field_simp

end

end PDE
