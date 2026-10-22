module

public import EllipticRegularity.DeGiorgi.LogPackage.LayerCake
public import EllipticRegularity.DeGiorgi.LogPackage.Bmo

/-!
# Product of exponential moments from an exponential tail bound
-/

@[expose] public section

namespace PDE.DGNMLog

open MeasureTheory

/-- If `F = v - avg v` has an exponential tail on `B`, then the product of the exponential
moments of `± γ v` is bounded by `(1 + C_J)² |B|²`. -/
theorem exp_moment_product_le {d : ℕ} {B : Set (Vec d)}
    (hBfin : volume B < ⊤) {v : Vec d → ℝ}
    (hv : AEMeasurable v (volume.restrict B)) {CJ M γ : ℝ} (hCJ : 0 < CJ) (hM : 0 < M)
    (hγ : 0 < γ) (hγM : γ ≤ 1 / (2 * CJ * M))
    (htail : ∀ t : ℝ, 0 < t →
      (volume {z ∈ B | t < |v z - integralAverage B v|}).toReal ≤
        CJ * Real.exp (-(t / (CJ * M))) * (volume B).toReal) :
    (∫⁻ z in B, ENNReal.ofReal (Real.exp (γ * v z))) *
        (∫⁻ z in B, ENNReal.ofReal (Real.exp (-γ * v z))) ≤
      ENNReal.ofReal ((1 + CJ) ^ 2) * volume B ^ 2 := by
  set m := integralAverage B v with hm
  set F : Vec d → ℝ := fun z => v z - m with hFdef
  have hF : AEMeasurable F (volume.restrict B) := hv.sub_const m
  have htail' : ∀ t : ℝ, 0 < t → (volume.restrict B) {z | t < |F z|} ≤
      ENNReal.ofReal (CJ * Real.exp (-(t / (CJ * M)))) * (volume.restrict B) Set.univ := by
    intro t ht
    have hnull : NullMeasurableSet {z | t < |F z|} (volume.restrict B) :=
      (continuous_abs.measurable.comp_aemeasurable hF).nullMeasurable measurableSet_Ioi
    rw [Measure.restrict_apply₀ hnull, Measure.restrict_apply_univ]
    have hsub : {z | t < |F z|} ∩ B = {z ∈ B | t < |v z - m|} := by
      ext z; constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h2, h1⟩
    rw [hsub]
    have hne : volume {z ∈ B | t < |v z - m|} ≠ ⊤ :=
      ne_top_of_le_ne_top hBfin.ne (measure_mono fun z hz => hz.1)
    rw [← ENNReal.ofReal_toReal hBfin.ne, ← ENNReal.ofReal_mul (by positivity)]
    rw [← ENNReal.ofReal_toReal hne]
    exact ENNReal.ofReal_le_ofReal (htail t ht)
  have hE := lintegral_exp_abs_le hF hCJ hM hγ hγM htail'
  rw [Measure.restrict_apply_univ] at hE
  have hE' := lintegral_exp_abs_le hF hCJ hM hγ hγM htail'
  rw [Measure.restrict_apply_univ] at hE'
  have h1 : ∫⁻ z in B, ENNReal.ofReal (Real.exp (γ * v z)) ≤
      ENNReal.ofReal (Real.exp (γ * m)) * ((1 + ENNReal.ofReal CJ) * volume B) := by
    calc ∫⁻ z in B, ENNReal.ofReal (Real.exp (γ * v z))
        ≤ ∫⁻ z in B, ENNReal.ofReal (Real.exp (γ * m)) *
            ENNReal.ofReal (Real.exp (γ * |F z|)) := by
          refine lintegral_mono fun z => ?_
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
          have := le_abs_self (F z)
          simp only [hFdef] at this ⊢
          nlinarith
      _ ≤ _ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          gcongr
  have h2 : ∫⁻ z in B, ENNReal.ofReal (Real.exp (-γ * v z)) ≤
      ENNReal.ofReal (Real.exp (-γ * m)) * ((1 + ENNReal.ofReal CJ) * volume B) := by
    calc ∫⁻ z in B, ENNReal.ofReal (Real.exp (-γ * v z))
        ≤ ∫⁻ z in B, ENNReal.ofReal (Real.exp (-γ * m)) *
            ENNReal.ofReal (Real.exp (γ * |F z|)) := by
          refine lintegral_mono fun z => ?_
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
          have := neg_abs_le (F z)
          simp only [hFdef] at this ⊢
          nlinarith
      _ ≤ _ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          gcongr
  calc _ ≤ (ENNReal.ofReal (Real.exp (γ * m)) * ((1 + ENNReal.ofReal CJ) * volume B)) *
        (ENNReal.ofReal (Real.exp (-γ * m)) * ((1 + ENNReal.ofReal CJ) * volume B)) :=
        mul_le_mul' h1 h2
    _ = (ENNReal.ofReal (Real.exp (γ * m)) * ENNReal.ofReal (Real.exp (-γ * m))) *
          ((1 + ENNReal.ofReal CJ) ^ 2 * volume B ^ 2) := by ring
    _ = ENNReal.ofReal ((1 + CJ) ^ 2) * volume B ^ 2 := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        have : γ * m + -γ * m = 0 := by ring
        rw [this, Real.exp_zero, ENNReal.ofReal_one, one_mul,
          ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_add zero_le_one hCJ.le,
          ENNReal.ofReal_one]

end PDE.DGNMLog
