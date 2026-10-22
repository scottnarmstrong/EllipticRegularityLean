/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.WeakHarnack.PowerShift

/-! # The power step for general nested cylinders, normalized `eLpNorm` form

* `posStep_general`: for `v = u + ε`, `0 < p ≤ q`, nested cylinders
  `B_{r'} × (s',t') ⊆ B_ρ × (s,t) ⊆ B_1 × (-1,0]`, gap `g = min (ρ-r') (min (s'-s) (t-t'))`:
  `‖v‖_{L^{χp}(ν|Q')} ≤ (A g^{-2})^{1/p} ‖v‖_{L^p(ν|Q)}` for `ν = cylMeasure S₁`, `Q ⊆ S₁`.
* `negStep_general`: the same for `1/v`, all `p > 0`, cylinders `B_{r'} × (s',0] ⊆ B_ρ × (s,0]`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.WeakHarnack

open MeasureTheory Set PDE

variable {d : ℕ}

theorem chi_eq (d : ℕ) (hd : 0 < d) : ((d : ℝ) + 2) / d = 1 + 2 / (d : ℝ) := by
  have : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

theorem posStep_general (d : ℕ) (hd : 0 < d) (Λ : ℝ) (hΛ : 0 ≤ Λ) (q : ℝ) (hq0 : 0 < q)
    (hq1 : q < 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (a : ParCoeffField d),
      IsParabolicCoeff 1 Λ a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) →
      ∀ u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0),
      IsParabolicWeakSupersolution a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u →
      (∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
        0 ≤ u.toFun z) →
      ∀ ε : ℝ, 0 < ε → ∀ {S₁ : Set (Vec d × ℝ)}, volume S₁ ≠ 0 → volume S₁ ≠ ⊤ →
      ∀ {r' ρ s s' t' t : ℝ}, 0 ≤ r' → r' < ρ → ρ ≤ 1 → -1 < s → s < s' → s' < t' → t' < t →
        t < 0 → euclideanBall (0 : Vec d) ρ ×ˢ Ioo s t ⊆ S₁ → ∀ p : ℝ, 0 < p → p ≤ q →
      eLpNorm (fun z => u.toFun z + ε) (ENNReal.ofReal ((1 + 2 / (d : ℝ)) * p))
          ((cylMeasure S₁).restrict (euclideanBall (0 : Vec d) r' ×ˢ Ioo s' t')) ≤
        ENNReal.ofReal ((((volume S₁).toReal⁻¹) ^ (1 / (1 + 2 / (d : ℝ))) *
            (C / (min (ρ - r') (min (s' - s) (t - t'))) ^ 2) * (volume S₁).toReal) ^ (1 / p)) *
          eLpNorm (fun z => u.toFun z + ε) (ENNReal.ofReal p)
            ((cylMeasure S₁).restrict (euclideanBall (0 : Vec d) ρ ×ˢ Ioo s t)) := by
  obtain ⟨C, hC1, hC⟩ := holder_pos d hd Λ hΛ q hq0 hq1
  refine ⟨C, hC1, ?_⟩
  intro a ha u hu hu0 ε hε S₁ hS0 hSt r' ρ s s' t' t hr' hr'ρ hρ1 hs1 hss' hst hlt ht0 hQS p hp hpq
  have hχ := chi_eq d hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hχ1 : 1 < 1 + 2 / (d : ℝ) := by have : 0 < 2 / (d : ℝ) := by positivity
                                       linarith
  have hhol := hC a ha u hu hu0 ε hε hr' hr'ρ hρ1 hs1 hss' hst hlt ht0 p hp hpq
  rw [hχ] at hhol
  set g : ℝ := min (ρ - r') (min (s' - s) (t - t')) with hg
  have hg0 : 0 < g := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hρU : euclideanBall (0 : Vec d) ρ ⊆ euclideanBall (0 : Vec d) 1 :=
    euclideanBall_mono (hr'.trans hr'ρ.le) hρ1
  have hQU : euclideanBall (0 : Vec d) ρ ×ˢ Ioo s t ⊆
      euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0 :=
    prod_mono hρU (fun τ hτ => ⟨by linarith [hτ.1], by linarith [hτ.2]⟩)
  have hQ'Q : euclideanBall (0 : Vec d) r' ×ˢ Ioo s' t' ⊆ euclideanBall (0 : Vec d) ρ ×ˢ Ioo s t :=
    prod_mono (euclideanBall_mono hr' hr'ρ.le) (Ioo_subset_Ioo (by linarith) (by linarith))
  have hQ'm : MeasurableSet (euclideanBall (0 : Vec d) r' ×ˢ Ioo s' t') :=
    (measurableSet_euclideanBall _ _).prod measurableSet_Ioo
  have hQm : MeasurableSet (euclideanBall (0 : Vec d) ρ ×ˢ Ioo s t) :=
    (measurableSet_euclideanBall _ _).prod measurableSet_Ioo
  refine eLpNorm_step_of_lintegral hQ'm hQm (hQ'Q.trans hQS) hQS hS0 hSt _
    (aesm_shift u S₁ (hQ'Q.trans hQU) ε) (aesm_shift u S₁ hQU ε) hp hχ1
    (div_nonneg (by linarith) (by positivity)) ?_
  rw [lintegral_enorm_shift u hu0 hε (hQ'Q.trans hQU) (by positivity),
    lintegral_enorm_shift u hu0 hε hQU hp.le, mul_comm (1 + 2 / (d : ℝ)) p]
  exact hhol

theorem negStep_general (d : ℕ) (hd : 0 < d) (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (a : ParCoeffField d),
      IsParabolicCoeff 1 Λ a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) →
      ∀ u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0),
      IsParabolicWeakSupersolution a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u →
      (∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
        0 ≤ u.toFun z) →
      ∀ ε : ℝ, 0 < ε → ∀ {S₁ : Set (Vec d × ℝ)}, volume S₁ ≠ 0 → volume S₁ ≠ ⊤ →
      ∀ {r' ρ s s' : ℝ}, 0 ≤ r' → r' < ρ → ρ ≤ 1 → -1 < s → s < s' → s' ≤ 0 →
        euclideanBall (0 : Vec d) ρ ×ˢ Ioc s 0 ⊆ S₁ → ∀ p : ℝ, 0 < p →
      eLpNorm (fun z => 1 / (u.toFun z + ε)) (ENNReal.ofReal ((1 + 2 / (d : ℝ)) * p))
          ((cylMeasure S₁).restrict (euclideanBall (0 : Vec d) r' ×ˢ Ioc s' 0)) ≤
        ENNReal.ofReal ((((volume S₁).toReal⁻¹) ^ (1 / (1 + 2 / (d : ℝ))) *
            (C / (min (ρ - r') (s' - s)) ^ 2) * (volume S₁).toReal) ^ (1 / p)) *
          eLpNorm (fun z => 1 / (u.toFun z + ε)) (ENNReal.ofReal p)
            ((cylMeasure S₁).restrict (euclideanBall (0 : Vec d) ρ ×ˢ Ioc s 0)) := by
  obtain ⟨C, hC1, hC⟩ := holder_neg d hd Λ hΛ
  refine ⟨C, hC1, ?_⟩
  intro a ha u hu hu0 ε hε S₁ hS0 hSt r' ρ s s' hr' hr'ρ hρ1 hs1 hss' hs'0 hQS p hp
  have hχ := chi_eq d hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hχ1 : 1 < 1 + 2 / (d : ℝ) := by have : 0 < 2 / (d : ℝ) := by positivity
                                       linarith
  have hhol := hC a ha u hu hu0 ε hε hr' hr'ρ hρ1 hs1 hss' hs'0 (-p) (by linarith)
  rw [hχ] at hhol
  set g : ℝ := min (ρ - r') (s' - s) with hg
  have hg0 : 0 < g := lt_min (by linarith) (by linarith)
  have hρU : euclideanBall (0 : Vec d) ρ ⊆ euclideanBall (0 : Vec d) 1 :=
    euclideanBall_mono (hr'.trans hr'ρ.le) hρ1
  have hQU : euclideanBall (0 : Vec d) ρ ×ˢ Ioc s 0 ⊆
      euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0 :=
    prod_mono hρU (Ioc_subset_Ioc hs1.le le_rfl)
  have hQ'Q : euclideanBall (0 : Vec d) r' ×ˢ Ioc s' 0 ⊆ euclideanBall (0 : Vec d) ρ ×ˢ Ioc s 0 :=
    prod_mono (euclideanBall_mono hr' hr'ρ.le) (Ioc_subset_Ioc hss'.le le_rfl)
  have hQ'm : MeasurableSet (euclideanBall (0 : Vec d) r' ×ˢ Ioc s' 0) :=
    (measurableSet_euclideanBall _ _).prod measurableSet_Ioc
  have hQm : MeasurableSet (euclideanBall (0 : Vec d) ρ ×ˢ Ioc s 0) :=
    (measurableSet_euclideanBall _ _).prod measurableSet_Ioc
  refine eLpNorm_step_of_lintegral hQ'm hQm (hQ'Q.trans hQS) hQS hS0 hSt _
    (aesm_inv_shift u S₁ (hQ'Q.trans hQU) ε) (aesm_inv_shift u S₁ hQU ε) hp hχ1
    (div_nonneg (by linarith) (by positivity)) ?_
  rw [lintegral_enorm_inv_shift u hu0 hε (hQ'Q.trans hQU) (by positivity),
    lintegral_enorm_inv_shift u hu0 hε hQU hp.le]
  have e1 : -((1 + 2 / (d : ℝ)) * p) = -p * (1 + 2 / (d : ℝ)) := by ring
  rw [e1]
  exact hhol

end PDE.Parabolic.WeakHarnack
