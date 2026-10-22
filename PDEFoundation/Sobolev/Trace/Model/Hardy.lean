module

public import PDEFoundation.Sobolev.Trace.Model.HardyPointwise

/-!
# Hardy's inequality

For `p > 1` and measurable `g : ℝ → [0, ∞]`,
`∫_0^∞ ((1/r) ∫_0^r g)^p dr ≤ (p/(p-1))^p ∫_0^∞ g^p`.
The proof is the weighted Hölder argument (`HardyPointwise`) followed by a Tonelli exchange.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set
open scoped ENNReal

/-- Tonelli exchange over the triangle `0 < t ≤ r`. -/
theorem lintegral_triangle_swap (W F : ℝ → ℝ≥0∞) (hW : Measurable W) (hF : Measurable F) :
    ∫⁻ r in Ioi (0 : ℝ), W r * ∫⁻ t in Ioc 0 r, F t =
      ∫⁻ t in Ioi (0 : ℝ), F t * ∫⁻ r in Ici t, W r := by
  set Φ : ℝ × ℝ → ℝ≥0∞ :=
    Set.indicator {p : ℝ × ℝ | p.2 ≤ p.1} (fun p => W p.1 * F p.2) with hΦ
  have hΦm : Measurable Φ :=
    (hW.comp measurable_fst |>.mul (hF.comp measurable_snd)).indicator
      (measurableSet_le measurable_snd measurable_fst)
  have h1 : ∀ r ∈ Ioi (0 : ℝ), W r * ∫⁻ t in Ioc 0 r, F t =
      ∫⁻ t in Ioi (0 : ℝ), Φ (r, t) := by
    intro r _
    have : (fun t => Φ (r, t)) = (Iic r).indicator (fun t => W r * F t) := by
      funext t
      simp only [hΦ, Set.indicator, Set.mem_ofPred_eq, mem_Iic]
    rw [show (∫⁻ t in Ioi (0 : ℝ), Φ (r, t)) = ∫⁻ t in Ioi (0 : ℝ),
      (Iic r).indicator (fun t => W r * F t) t from by rw [this],
      lintegral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
      Iic_inter_Ioi, lintegral_const_mul _ hF]
  have h2 : ∀ t ∈ Ioi (0 : ℝ), ∫⁻ r in Ioi (0 : ℝ), Φ (r, t) = F t * ∫⁻ r in Ici t, W r := by
    intro t ht
    have : (fun r => Φ (r, t)) = (Ici t).indicator (fun r => W r * F t) := by
      funext r
      simp only [hΦ, Set.indicator, Set.mem_ofPred_eq, mem_Ici]
    rw [show (∫⁻ r in Ioi (0 : ℝ), Φ (r, t)) = ∫⁻ r in Ioi (0 : ℝ),
      (Ici t).indicator (fun r => W r * F t) r from by rw [this],
      lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
      show Ici t ∩ Ioi (0 : ℝ) = Ici t from inter_eq_left.2 (fun x hx => lt_of_lt_of_le ht hx),
      lintegral_mul_const _ hW, mul_comm]
  rw [setLIntegral_congr_fun measurableSet_Ioi h1,
    lintegral_lintegral_swap (f := fun r t => Φ (r, t)) hΦm.aemeasurable]
  exact setLIntegral_congr_fun measurableSet_Ioi h2

/-- Real arithmetic for the constant in Hardy's inequality. -/
theorem hardy_constant_arith {p : ℝ} (hp : 1 < p) {t : ℝ} (ht : 0 < t) :
    t ^ (1 / Real.conjExponent p) *
        (Real.conjExponent p ^ (1 / Real.conjExponent p * p) *
          (-t ^ (1 / p - 2 + 1) / (1 / p - 2 + 1))) = (p / (p - 1)) ^ p := by
  set q := Real.conjExponent p with hqdef
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hq0 : 0 < q := hpq.symm.pos
  have hp0 : 0 < p := by linarith
  have hsum : 1 / p + 1 / q = 1 := inv_conj_add hp
  have hs : 1 / p - 2 + 1 = -(1 / q) := by linarith
  have hqp : q = p / (p - 1) := rfl
  have hne : (1 / q) ≠ 0 := by positivity
  have hcq : q ^ (1 / q * p) * q = q ^ p := by
    rw [mul_comm, ← Real.rpow_one_add' hq0.le (by
      have : 0 < 1 / q * p := by positivity
      linarith)]
    congr 1
    have : 1 / q * p = p - 1 := by rw [hqp]; field_simp
    linarith
  have h1 : t ^ (1 / q) * t ^ (-(1 / q)) = 1 := by
    rw [← Real.rpow_add ht]; simp
  rw [hs, ← hqp]
  have h2 : -t ^ (-(1 / q)) / -(1 / q) = q * t ^ (-(1 / q)) := by
    field_simp
  rw [h2]
  calc t ^ (1 / q) * (q ^ (1 / q * p) * (q * t ^ (-(1 / q))))
      = (t ^ (1 / q) * t ^ (-(1 / q))) * (q ^ (1 / q * p) * q) := by ring
    _ = q ^ p := by rw [h1, hcq, one_mul]

/-- **Hardy's inequality** (manuscript (1.49)), `lintegral` form. -/
theorem hardy_lintegral {p : ℝ} (hp : 1 < p) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ r in Ioi (0 : ℝ), ((∫⁻ t in Ioc 0 r, g t) / ENNReal.ofReal r) ^ p ≤
      ENNReal.ofReal ((p / (p - 1)) ^ p) * ∫⁻ t in Ioi (0 : ℝ), g t ^ p := by
  set q := Real.conjExponent p with hqdef
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hq0 : 0 < q := hpq.symm.pos
  have hp0 : 0 < p := by linarith
  set c : ℝ := q ^ (1 / q * p) with hc
  have hc0 : 0 ≤ c := Real.rpow_nonneg hq0.le _
  set W : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (c * r ^ (1 / p - 2)) with hW
  set F : ℝ → ℝ≥0∞ := fun t => g t ^ p * ENNReal.ofReal (t ^ (1 / q)) with hF
  have hWm : Measurable W :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_id.pow_const _))
  have hFm : Measurable F :=
    (hg.pow_const p).mul (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _))
  have h1 : ∫⁻ r in Ioi (0 : ℝ), ((∫⁻ t in Ioc 0 r, g t) / ENNReal.ofReal r) ^ p ≤
      ∫⁻ r in Ioi (0 : ℝ), W r * ∫⁻ t in Ioc 0 r, F t :=
    setLIntegral_mono' measurableSet_Ioi (fun r hr => hardy_key hp g hg hr)
  refine h1.trans (le_of_eq ?_)
  rw [lintegral_triangle_swap W F hWm hFm]
  have h2 : ∀ t ∈ Ioi (0 : ℝ), F t * ∫⁻ r in Ici t, W r =
      g t ^ p * ENNReal.ofReal ((p / (p - 1)) ^ p) := by
    intro t ht
    have ht0 : 0 < t := ht
    have hs : 1 / p - 2 < -1 := by
      have : 1 / p < 1 := by rw [div_lt_one hp0]; exact hp
      linarith
    have hI : ∫⁻ r in Ici t, W r = ENNReal.ofReal c *
        ENNReal.ofReal (-t ^ (1 / p - 2 + 1) / (1 / p - 2 + 1)) := by
      rw [← setLIntegral_congr Ioi_ae_eq_Ici]
      simp only [hW]
      simp_rw [ENNReal.ofReal_mul hc0]
      rw [lintegral_const_mul (f := fun r : ℝ => ENNReal.ofReal (r ^ (1 / p - 2)))
        (ENNReal.ofReal c) (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)),
        lintegral_Ioi_rpow hs ht0]
    rw [hI, hF]
    simp only
    rw [mul_assoc, ← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_mul (Real.rpow_nonneg ht0.le _),
      hardy_constant_arith hp ht0]
  rw [setLIntegral_congr_fun measurableSet_Ioi h2, lintegral_mul_const _ (hg.pow_const p),
    mul_comm]

end PDE.TraceLane
