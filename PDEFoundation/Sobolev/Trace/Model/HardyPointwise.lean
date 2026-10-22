module

public import PDEFoundation.Sobolev.Trace.Model.HardyWeights
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The weighted Hölder step of Hardy's inequality

For `p > 1` with conjugate exponent `q = p/(p-1)` and `r > 0`,
`∫_0^r g ≤ (∫_0^r g^p t^{1/q})^{1/p} (q r^{1/q})^{1/q}`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set
open scoped ENNReal

theorem inv_conj_add {p : ℝ} (hp : 1 < p) :
    1 / p + 1 / Real.conjExponent p = 1 := by
  have h := (Real.HolderConjugate.conjExponent hp).inv_add_inv_eq_one
  simpa [one_div] using h

/-- Weighted Hölder bound on `(0, r]`. -/
theorem hardy_holder_step {p : ℝ} (hp : 1 < p) (g : ℝ → ℝ≥0∞) (hg : Measurable g)
    {r : ℝ} (hr : 0 < r) :
    (∫⁻ t in Ioc 0 r, g t) ≤
      (∫⁻ t in Ioc 0 r, g t ^ p * ENNReal.ofReal (t ^ (1 / Real.conjExponent p))) ^ (1 / p) *
        ENNReal.ofReal (Real.conjExponent p * r ^ (1 / Real.conjExponent p)) ^
          (1 / Real.conjExponent p) := by
  set q := Real.conjExponent p with hqdef
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := hpq.symm.pos
  have hsum : 1 / p + 1 / q = 1 := inv_conj_add hp
  set α : ℝ := 1 / (p * q) with hα
  have hαp : α * p = 1 / q := by rw [hα]; field_simp
  have hαq : α * q = 1 / p := by rw [hα]; field_simp
  -- rewrite the integrand as a product
  have hfac : ∫⁻ t in Ioc 0 r, g t =
      ∫⁻ t in Ioc 0 r, (g t * ENNReal.ofReal (t ^ α)) * ENNReal.ofReal (t ^ (-α)) := by
    refine setLIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    have h1 : ENNReal.ofReal (t ^ α) * ENNReal.ofReal (t ^ (-α)) = 1 := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.1.le _), ← Real.rpow_add ht.1]
      simp
    rw [mul_assoc, h1, mul_one]
  have hmeas1 : AEMeasurable (fun t => g t * ENNReal.ofReal (t ^ α))
      (volume.restrict (Ioc 0 r)) :=
    (hg.mul (ENNReal.measurable_ofReal.comp (measurable_id.pow_const α))).aemeasurable
  have hmeas2 : AEMeasurable (fun t : ℝ => ENNReal.ofReal (t ^ (-α)))
      (volume.restrict (Ioc 0 r)) :=
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const (-α))).aemeasurable
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ioc 0 r)) hpq hmeas1 hmeas2
  have hX : ∫⁻ t in Ioc 0 r, (g t * ENNReal.ofReal (t ^ α)) ^ p =
      ∫⁻ t in Ioc 0 r, g t ^ p * ENNReal.ofReal (t ^ (1 / q)) := by
    refine setLIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg ht.1.le _) hp0.le,
      ← Real.rpow_mul ht.1.le, hαp]
  have hY : ∫⁻ t in Ioc 0 r, ENNReal.ofReal (t ^ (-α)) ^ q =
      ENNReal.ofReal (q * r ^ (1 / q)) := by
    have hneg : -α * q = -(1 / p) := by rw [neg_mul, hαq]
    have h1 : ∫⁻ t in Ioc 0 r, ENNReal.ofReal (t ^ (-α)) ^ q =
        ∫⁻ t in Ioc 0 r, ENNReal.ofReal (t ^ (-(1 / p))) := by
      refine setLIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg ht.1.le _) hq0.le,
        ← Real.rpow_mul ht.1.le, hneg]
    have hlt : -1 < -(1 / p) := by
      have : 1 / p < 1 := by rw [div_lt_one hp0]; exact hp
      linarith
    rw [h1, lintegral_Ioc_rpow hlt hr]
    congr 1
    have h2 : -(1 / p) + 1 = 1 / q := by linarith
    rw [h2]
    field_simp
  rw [hfac]
  simpa only [Pi.mul_apply, hX, hY] using hH

/-- Real-exponent bookkeeping: `(q r^(1/q))^(p/q) r^(-p) = q^(p/q) r^(1/p - 2)`. -/
theorem hardy_exponent_arith {p : ℝ} (hp : 1 < p) {r : ℝ} (hr : 0 < r) :
    (Real.conjExponent p * r ^ (1 / Real.conjExponent p)) ^ (1 / Real.conjExponent p * p) *
        r ^ (-p) =
      Real.conjExponent p ^ (1 / Real.conjExponent p * p) * r ^ (1 / p - 2) := by
  set q := Real.conjExponent p with hqdef
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hq0 : 0 < q := hpq.symm.pos
  have hsum : 1 / p + 1 / q = 1 := inv_conj_add hp
  have hu : 1 / q = 1 - 1 / p := by linarith
  have hp0 : 0 < p := by linarith
  rw [Real.mul_rpow hq0.le (Real.rpow_nonneg hr.le _), ← Real.rpow_mul hr.le, mul_assoc,
    ← Real.rpow_add hr]
  congr 2
  rw [hu]
  field_simp
  ring

/-- The pointwise Hardy bound after Hölder. -/
theorem hardy_key {p : ℝ} (hp : 1 < p) (g : ℝ → ℝ≥0∞) (hg : Measurable g)
    {r : ℝ} (hr : 0 < r) :
    ((∫⁻ t in Ioc 0 r, g t) / ENNReal.ofReal r) ^ p ≤
      ENNReal.ofReal (Real.conjExponent p ^ (1 / Real.conjExponent p * p) * r ^ (1 / p - 2)) *
        ∫⁻ t in Ioc 0 r, g t ^ p * ENNReal.ofReal (t ^ (1 / Real.conjExponent p)) := by
  set q := Real.conjExponent p with hqdef
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := hpq.symm.pos
  set X := ∫⁻ t in Ioc 0 r, g t ^ p * ENNReal.ofReal (t ^ (1 / q)) with hX
  have hH := hardy_holder_step hp g hg hr
  have h1 : ((∫⁻ t in Ioc 0 r, g t) / ENNReal.ofReal r) ^ p ≤
      ((X ^ (1 / p) * ENNReal.ofReal (q * r ^ (1 / q)) ^ (1 / q)) / ENNReal.ofReal r) ^ p :=
    ENNReal.rpow_le_rpow (ENNReal.div_le_div_right hH _) hp0.le
  refine h1.trans (le_of_eq ?_)
  have hrp : ((ENNReal.ofReal r)⁻¹) ^ p = ENNReal.ofReal (r ^ (-p)) := by
    rw [ENNReal.inv_rpow, ENNReal.ofReal_rpow_of_nonneg hr.le hp0.le, Real.rpow_neg hr.le,
      ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hr _)]
  have hY : (ENNReal.ofReal (q * r ^ (1 / q)) ^ (1 / q)) ^ p =
      ENNReal.ofReal ((q * r ^ (1 / q)) ^ (1 / q * p)) := by
    rw [← ENNReal.rpow_mul, ENNReal.ofReal_rpow_of_nonneg
      (mul_nonneg hq0.le (Real.rpow_nonneg hr.le _)) (by positivity)]
  rw [div_eq_mul_inv, ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
    ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, hrp, hY]
  have hone : 1 / p * p = 1 := by field_simp
  rw [hone, ENNReal.rpow_one]
  have hb : 0 ≤ (q * r ^ (1 / q)) ^ (1 / q * p) :=
    Real.rpow_nonneg (mul_nonneg hq0.le (Real.rpow_nonneg hr.le _)) _
  calc X * ENNReal.ofReal ((q * r ^ (1 / q)) ^ (1 / q * p)) * ENNReal.ofReal (r ^ (-p))
      = (ENNReal.ofReal ((q * r ^ (1 / q)) ^ (1 / q * p)) * ENNReal.ofReal (r ^ (-p))) * X := by
        ring
    _ = _ := by
      rw [← ENNReal.ofReal_mul hb]
      congr 2
      exact hardy_exponent_arith hp hr

end PDE.TraceLane
