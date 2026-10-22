/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.WeakHarnack.PowerStepFinal

/-! # Finiteness of the `L^{qχ}` norm on `posCyl d 1`

One application of the positive power step (`holder_pos`) from `B_{7/8} × (-15/16, -5/16)` to
`posCyl d 1 = B_{3/4} × (-7/8, -3/8)` with `p = q`, together with `v^q ≤ 1 + v` and `u ∈ L²`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.WeakHarnack

open MeasureTheory Set PDE

theorem rpow_le_one_add {x q : ℝ} (hx : 0 ≤ x) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    x ^ q ≤ 1 + x := by
  by_cases h : x ≤ 1
  · have := Real.rpow_le_one hx h hq0.le
    linarith
  · push Not at h
    have := Real.rpow_le_rpow_of_exponent_le h.le hq1
    rw [Real.rpow_one] at this
    linarith

/-- **Finiteness hypothesis `H1fin`** of `weakHarnack_of_steps`. -/
theorem parabPowerStepPosFinite (d : ℕ) (hd : 0 < d) (Lam : ℝ) (hLam : 1 ≤ Lam) (q : ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) :
    ∀ (a : ParCoeffField d),
      IsParabolicCoeff 1 Lam a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) →
      ∀ u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0),
      IsParabolicWeakSupersolution a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u →
      (∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
        0 ≤ u.toFun z) →
      ∀ ε : ℝ, 0 < ε →
        eLpNorm (fun z => u.toFun z + ε) (ENNReal.ofReal (q * (1 + 2 / (d : ℝ))))
          ((cylMeasure (posCyl d 1)).restrict (posCyl d 1)) < ⊤ := by
  obtain ⟨C, hC1, hC⟩ := holder_pos d hd Lam (by linarith) q hq0 hq1
  intro a ha u hu hu0 ε hε
  have hχ := chi_eq d hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hχ0 : 0 < 1 + 2 / (d : ℝ) := by positivity
  have hhol := hC a ha u hu hu0 ε hε (r' := 3 / 4) (ρ := 7 / 8) (s := -15 / 16) (s' := -7 / 8)
    (t' := -3 / 8) (t := -5 / 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) q hq0 le_rfl
  rw [hχ] at hhol
  -- the right-hand side is finite
  set Q : Set (Vec d × ℝ) := euclideanBall (0 : Vec d) (7 / 8) ×ˢ Ioo (-15 / 16 : ℝ) (-5 / 16)
    with hQ
  have hQU : Q ⊆ euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0 :=
    prod_mono (euclideanBall_mono (by norm_num) (by norm_num))
      (fun τ hτ => ⟨by linarith [hτ.1], by linarith [hτ.2]⟩)
  have : IsFiniteMeasure (volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)) :=
    ⟨by
      rw [Measure.restrict_apply_univ, Measure.volume_eq_prod, Measure.prod_prod]
      exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 (volume_euclideanBall_ne_top _ zero_le_one))
        (by simp)⟩
  have hint : Integrable (fun z => (1 + ε) + u.toFun z)
      (volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)) :=
    (integrable_const _).add (u.memL2.integrable one_le_two)
  have hR : ∫⁻ z in Q, ENNReal.ofReal ((u.toFun z + ε) ^ q) < ⊤ := by
    calc ∫⁻ z in Q, ENNReal.ofReal ((u.toFun z + ε) ^ q)
        ≤ ∫⁻ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0,
            ENNReal.ofReal ((u.toFun z + ε) ^ q) := lintegral_mono_set hQU
      _ ≤ ∫⁻ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0,
            ENNReal.ofReal ((1 + ε) + u.toFun z) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hu0] with z hz
          refine ENNReal.ofReal_le_ofReal ?_
          have := rpow_le_one_add (show 0 ≤ u.toFun z + ε by linarith) hq0 hq1.le
          linarith
      _ < ⊤ := hint.lintegral_lt_top
  have hQ'eq : posCyl d 1 = euclideanBall (0 : Vec d) (3 / 4) ×ˢ Ioo (-7 / 8 : ℝ) (-3 / 8) :=
    posCyl_one
  have hQ'U : posCyl d 1 ⊆ euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0 :=
    posCyl_subset (by norm_num) le_rfl
  have hQ'm : MeasurableSet (posCyl d 1) := measurableSet_posCyl 1
  have hfin1 : (∫⁻ z in euclideanBall (0 : Vec d) (3 / 4) ×ˢ Ioo (-7 / 8 : ℝ) (-3 / 8),
      ENNReal.ofReal ((u.toFun z + ε) ^ (q * (1 + 2 / (d : ℝ))))) ≠ ⊤ := by
    intro htop
    have h1 : (∫⁻ z in euclideanBall (0 : Vec d) (3 / 4) ×ˢ Ioo (-7 / 8 : ℝ) (-3 / 8),
        ENNReal.ofReal ((u.toFun z + ε) ^ (q * (1 + 2 / (d : ℝ))))) ^ (1 / (1 + 2 / (d : ℝ))) = ⊤ := by
      rw [htop]; exact ENNReal.top_rpow_of_pos (by positivity)
    have h3 : ENNReal.ofReal (C / min (7 / 8 - 3 / 4 : ℝ) (min (-7 / 8 - -15 / 16 : ℝ)
        (-5 / 16 - -3 / 8)) ^ 2) * ∫⁻ z in Q, ENNReal.ofReal ((u.toFun z + ε) ^ q) < ⊤ :=
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hR
    have h4 := hhol
    rw [h1] at h4
    exact absurd (lt_of_le_of_lt h4 h3) (lt_irrefl _)
  rw [eLpNorm_cylMeasure hQ'm subset_rfl _ (aesm_shift u (posCyl d 1) hQ'U ε) (by positivity),
    lintegral_enorm_shift u hu0 hε hQ'U (by positivity), hQ'eq]
  refine ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_
  refine ENNReal.mul_ne_top ?_ hfin1
  rw [Ne, ENNReal.inv_eq_top, ← hQ'eq]
  exact (volume_posCyl_pos (σ := 1) (by norm_num)).ne'

end PDE.Parabolic.WeakHarnack
