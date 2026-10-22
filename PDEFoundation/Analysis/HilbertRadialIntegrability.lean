module

public import PDEFoundation.Analysis.HilbertPolar
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-! # Internal radial power integrability -/

@[expose] public section

open scoped Real ENNReal
open MeasureTheory Metric Set

namespace PDE.Internal

noncomputable section

variable {d : ℕ}

/-- A radial real power is locally integrable at the origin in dimension `d`
exactly above exponent `-d`. -/
theorem integrableOn_norm_rpow_euclideanBall_iff
    [NeZero d] {R s : ℝ} (hR : 0 < R) :
    IntegrableOn (fun x : HilbertVec d => ‖x‖ ^ s) (ball 0 R) ↔ -(d : ℝ) < s := by
  let f : ℝ → ℝ := fun r => (Ioo (0 : ℝ) R).indicator (fun _ => r ^ s) r
  have hpolar := integrable_fun_norm_addHaar (μ := (volume : Measure (HilbertVec d))) (f := f)
  have hleft : Integrable (fun x : HilbertVec d => f ‖x‖) ↔
      IntegrableOn (fun x : HilbertVec d => ‖x‖ ^ s) (ball 0 R) := by
    rw [← integrable_indicator_iff (isOpen_ball.measurableSet)]
    apply integrable_congr
    filter_upwards [(countable_singleton (0 : HilbertVec d)).ae_notMem volume] with x hx
    have hx0 : x ≠ 0 := by simpa only [mem_singleton_iff] using hx
    by_cases hxb : x ∈ ball (0 : HilbertVec d) R
    · have hnorm : ‖x‖ ∈ Ioo (0 : ℝ) R := by
        simpa only [mem_Ioo, norm_pos_iff, mem_ball_zero_iff] using And.intro hx0 hxb
      simp only [f, Set.indicator_of_mem hnorm, Set.indicator_of_mem hxb]
    · have hnorm : ‖x‖ ∉ Ioo (0 : ℝ) R := by
        intro hn
        apply hxb
        simpa only [mem_ball_zero_iff] using hn.2
      simp only [f, Set.indicator_of_notMem hnorm, Set.indicator_of_notMem hxb]
  rw [hleft] at hpolar
  rw [hpolar]
  have hdim : Module.finrank ℝ (HilbertVec d) = d := by
    calc
      Module.finrank ℝ (HilbertVec d) = Module.finrank ℝ (Fin d → ℝ) :=
        (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).finrank_eq
      _ = d := by simp
  rw [hdim]
  have hcongr : IntegrableOn
      (fun y : ℝ => y ^ (d - 1) • f y) (Ioi 0) ↔
      IntegrableOn (fun y : ℝ => y ^ (s + (d : ℝ) - 1)) (Ioo 0 R) := by
    rw [← integrable_indicator_iff measurableSet_Ioi,
      ← integrable_indicator_iff measurableSet_Ioo]
    apply integrable_congr
    filter_upwards with y
    simp only [f, indicator_apply, smul_eq_mul]
    by_cases hyr : y ∈ Ioo (0 : ℝ) R
    · have hy0 : y ∈ Ioi (0 : ℝ) := hyr.1
      rw [ite_eq_left hy0, ite_eq_left hyr, ite_eq_left hyr]
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_add hyr.1]
      congr 1
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))]
      push_cast
      ring
    · by_cases hy0 : y ∈ Ioi (0 : ℝ)
      · rw [ite_eq_left hy0, ite_eq_right hyr, ite_eq_right hyr, mul_zero]
      · rw [ite_eq_right hy0, ite_eq_right hyr]
  rw [hcongr, intervalIntegral.integrableOn_Ioo_rpow_iff hR]
  have hdreal : (1 : ℝ) ≤ d := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))
  constructor <;> intro h <;> linarith

end

end PDE.Internal
