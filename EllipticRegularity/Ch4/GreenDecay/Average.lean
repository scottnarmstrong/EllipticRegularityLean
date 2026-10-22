module

public import EllipticRegularity.Ch4.GreenDecay.Helpers

/-!
# The mean minimizes the `L²` deviation
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4GreenDecay

open MeasureTheory PDE

noncomputable section

variable {d : ℕ}

theorem integral_sub_integralAverage {U : Set (Vec d)} (hpos : 0 < (volume U).toReal)
    (hfin : volume U ≠ ⊤) {f : Vec d → ℝ} (hf : IntegrableOn f U) :
    (∫ x in U, (f x - integralAverage U f)) = 0 := by
  have : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hfin
  rw [integral_sub hf (integrable_const _), setIntegral_const, smul_eq_mul]
  unfold integralAverage
  show (∫ x in U, f x) - (volume U).toReal * ((volume U).toReal⁻¹ * ∫ x in U, f x) = 0
  rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul, sub_self]

/-- The mean minimizes the `L²` deviation from a constant. -/
theorem integral_sq_sub_average_le {U : Set (Vec d)} (hpos : 0 < (volume U).toReal)
    (hfin : volume U ≠ ⊤) {f : Vec d → ℝ} (hf : MemL2On U f) (c : ℝ) :
    (∫ x in U, (f x - integralAverage U f) ^ 2) ≤ ∫ x in U, (f x - c) ^ 2 := by
  have : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hfin
  set a := integralAverage U f with ha
  have hf1 : IntegrableOn f U := hf.integrable (by norm_num)
  have hfa : MemL2On U (fun x => f x - a) := hf.sub (memLp_const a)
  have hfc : MemL2On U (fun x => f x - c) := hf.sub (memLp_const c)
  have hi1 : IntegrableOn (fun x => (f x - a) ^ 2) U := hfa.integrable_sq
  have hi2 : IntegrableOn (fun x => (f x - a)) U := hf1.sub (integrable_const _)
  have hzero := integral_sub_integralAverage hpos hfin hf1
  have hpt : ∀ x, (f x - c) ^ 2 = (f x - a) ^ 2 + (2 * (a - c)) * (f x - a) + (a - c) ^ 2 := by
    intro x; ring
  simp_rw [hpt]
  have h3 : IntegrableOn (fun x => (f x - a) ^ 2 + 2 * (a - c) * (f x - a)) U :=
    hi1.add (hi2.const_mul _)
  rw [integral_add (f := fun x => (f x - a) ^ 2 + 2 * (a - c) * (f x - a))
      (g := fun _ => (a - c) ^ 2) h3 (integrable_const _),
    integral_add (f := fun x => (f x - a) ^ 2) (g := fun x => 2 * (a - c) * (f x - a))
      hi1 (hi2.const_mul _), integral_const_mul, hzero, mul_zero, add_zero,
    setIntegral_const, smul_eq_mul]
  have : 0 ≤ (a - c) ^ 2 * (volume U).toReal := mul_nonneg (sq_nonneg _) hpos.le
  show _ ≤ _ + volume.real U * (a - c) ^ 2
  have hr : volume.real U = (volume U).toReal := rfl
  rw [hr]
  nlinarith

end

end PDE.Ch4GreenDecay
