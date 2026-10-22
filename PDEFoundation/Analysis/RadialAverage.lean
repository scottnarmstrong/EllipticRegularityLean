module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Monotonicity of dimension-weighted radial averages

The normalized integral of a continuous monotone radial profile increases with
radius. The factor `d / r ^ d` is exact, so this lemma spends no constant when
passing from spherical submean inequalities to ball averages.

The proof is adapted from the sibling Superdiffusion harmonic-gradient
submean development and requires no ambient-space realization.
-/

@[expose] public section

namespace PDE

open MeasureTheory

variable {d : ℕ}

/-- Dimension-weighted radial averages preserve monotonicity of a continuous
profile on positive radii. No positivity of the profile is required. -/
theorem normalized_radialIntegral_mono [NeZero d]
    {F : ℝ → ℝ} (hF : Continuous F)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hFmono : MonotoneOn F (Set.Ioc 0 b)) :
    (d : ℝ) / a ^ d * ∫ t in (0 : ℝ)..a, t ^ (d - 1) * F t ≤
      (d : ℝ) / b ^ d * ∫ t in (0 : ℝ)..b, t ^ (d - 1) * F t := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hb : 0 < b := ha.trans_le hab
  have hpowCont : Continuous (fun t : ℝ ↦ t ^ (d - 1)) := continuous_pow _
  have hIntCont : Continuous (fun t : ℝ ↦ t ^ (d - 1) * F t) := hpowCont.mul hF
  have hIa : ∫ t in (0 : ℝ)..a, t ^ (d - 1) * F t ≤ F a * (a ^ d / d) := by
    calc
      ∫ t in (0 : ℝ)..a, t ^ (d - 1) * F t ≤
          ∫ t in (0 : ℝ)..a, t ^ (d - 1) * F a := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo ha.le
          (hIntCont.intervalIntegrable 0 a)
          ((hpowCont.mul continuous_const).intervalIntegrable 0 a)
        intro t ht
        exact mul_le_mul_of_nonneg_left
          (hFmono ⟨ht.1, ht.2.le.trans hab⟩ ⟨ha, hab⟩ ht.2.le) (pow_nonneg ht.1.le _)
      _ = F a * (a ^ d / d) := by
        rw [intervalIntegral.integral_mul_const, integral_pow]
        simp only [zero_pow (NeZero.ne d), Nat.sub_add_cancel
          (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)), Nat.cast_sub
          (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)), Nat.cast_one]
        ring
  have hJ : F a * ((b ^ d - a ^ d) / d) ≤
      ∫ t in a..b, t ^ (d - 1) * F t := by
    calc
      F a * ((b ^ d - a ^ d) / d) =
          ∫ t in a..b, t ^ (d - 1) * F a := by
        rw [intervalIntegral.integral_mul_const, integral_pow]
        simp only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)),
          Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)), Nat.cast_one]
        ring
      _ ≤ ∫ t in a..b, t ^ (d - 1) * F t := by
        apply intervalIntegral.integral_mono_on hab
          ((hpowCont.mul continuous_const).intervalIntegrable a b)
          (hIntCont.intervalIntegrable a b)
        intro t ht
        exact mul_le_mul_of_nonneg_left
          (hFmono ⟨ha, hab⟩ ⟨ha.trans_le ht.1, ht.2⟩ ht.1)
          (pow_nonneg (ha.le.trans ht.1) _)
  have hsplit : ∫ t in (0 : ℝ)..b, t ^ (d - 1) * F t =
      (∫ t in (0 : ℝ)..a, t ^ (d - 1) * F t) +
        ∫ t in a..b, t ^ (d - 1) * F t := by
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hIntCont.intervalIntegrable 0 a) (hIntCont.intervalIntegrable a b)).symm
  have haPow : 0 < a ^ d := pow_pos ha d
  have hbPow : 0 < b ^ d := pow_pos hb d
  have hgap : 0 ≤ b ^ d - a ^ d :=
    sub_nonneg.mpr (pow_le_pow_left₀ ha.le hab d)
  have hkey : (b ^ d - a ^ d) *
      (∫ t in (0 : ℝ)..a, t ^ (d - 1) * F t) ≤
        a ^ d * ∫ t in a..b, t ^ (d - 1) * F t := by
    calc
      _ ≤ (b ^ d - a ^ d) * (F a * (a ^ d / d)) :=
        mul_le_mul_of_nonneg_left hIa hgap
      _ = a ^ d * (F a * ((b ^ d - a ^ d) / d)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hJ haPow.le
  rw [hsplit]
  field_simp
  nlinarith only [hkey]

end PDE
