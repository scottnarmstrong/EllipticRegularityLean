module

public import PDEFoundation

/-!
# Stampacchia's layer-cake bound

If `ν {f > t} ≤ A t^{-γ}` for all `t > 0` with `γ > 1`, then
`∫ f dν ≤ γ/(γ-1) · A^{1/γ} · ν(univ)^{1 - 1/γ}` (layer-cake formula, split at the level
`t₀ = (A / ν(univ))^{1/γ}`).  Used in Step 5 of Proposition 4.40 with `γ = d/(d-2)`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4Green

open MeasureTheory Set

variable {α : Type*} [MeasurableSpace α] {ν : Measure α}

/-- Algebra of the layer-cake split. -/
theorem layerCake_algebra {A m γ : ℝ} (hA : 0 < A) (hm : 0 < m) (hγ : 1 < γ) :
    m * (A / m) ^ (1 / γ) + A * ((A / m) ^ (1 / γ)) ^ (-γ + 1) / (γ - 1) =
      γ / (γ - 1) * A ^ (1 / γ) * m ^ (1 - 1 / γ) := by
  have hγ0 : 0 < γ := by linarith
  have hγ1 : 0 < γ - 1 := by linarith
  set t₀ := (A / m) ^ (1 / γ) with ht₀
  have hAm : 0 < A / m := div_pos hA hm
  have ht₀pos : 0 < t₀ := Real.rpow_pos_of_pos hAm _
  have hpow : t₀ ^ (-γ + 1) = t₀ * (m / A) := by
    rw [Real.rpow_add ht₀pos, Real.rpow_one, ht₀, ← Real.rpow_mul hAm.le,
      show 1 / γ * -γ = -1 by field_simp, Real.rpow_neg_one, inv_div]
    ring
  have hmt : m * t₀ = A ^ (1 / γ) * m ^ (1 - 1 / γ) := by
    rw [ht₀, Real.div_rpow hA.le hm.le, Real.rpow_sub hm, Real.rpow_one]
    field_simp
  rw [hpow]
  have : A * (t₀ * (m / A)) = m * t₀ := by field_simp
  rw [this, hmt]
  field_simp
  ring

/-- **Layer-cake bound** from a power-law tail. -/
theorem lintegral_ofReal_le_of_tail {f : α → ℝ} (hf : AEMeasurable f ν) (hf0 : 0 ≤ᵐ[ν] f)
    (hfin : ν univ ≠ ⊤) {A γ : ℝ} (hA : 0 < A) (hγ : 1 < γ)
    (htail : ∀ t : ℝ, 0 < t → ν {x | t < f x} ≤ ENNReal.ofReal (A * t ^ (-γ))) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂ν ≤
      ENNReal.ofReal (γ / (γ - 1) * A ^ (1 / γ) * (ν univ).toReal ^ (1 - 1 / γ)) := by
  set m := (ν univ).toReal with hmdef
  rcases (ENNReal.toReal_nonneg : 0 ≤ m).eq_or_lt with hm | hm
  · have h0 : ν univ = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff _).1 hm.symm with h | h
      · exact h
      · exact absurd h hfin
    rw [Measure.measure_univ_eq_zero.1 h0]
    simp
  have hγ0 : 0 < γ := by linarith
  set t₀ := (A / m) ^ (1 / γ) with ht₀
  have ht₀pos : 0 < t₀ := Real.rpow_pos_of_pos (div_pos hA hm) _
  rw [lintegral_eq_lintegral_meas_lt ν hf0 hf, ← Ioc_union_Ioi_eq_Ioi ht₀pos.le,
    lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl)]
  have h1 : ∫⁻ t in Ioc 0 t₀, ν {x | t < f x} ≤ ENNReal.ofReal (m * t₀) := by
    calc ∫⁻ t in Ioc 0 t₀, ν {x | t < f x} ≤ ∫⁻ _ in Ioc 0 t₀, ν univ :=
          lintegral_mono fun t => measure_mono (subset_univ _)
      _ = ENNReal.ofReal (m * t₀) := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero, hmdef,
            ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin]
  have hint : IntegrableOn (fun t : ℝ => A * t ^ (-γ)) (Ioi t₀) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) ht₀pos).const_mul A
  have h2 : ∫⁻ t in Ioi t₀, ν {x | t < f x} ≤
      ENNReal.ofReal (A * t₀ ^ (-γ + 1) / (γ - 1)) := by
    calc ∫⁻ t in Ioi t₀, ν {x | t < f x} ≤ ∫⁻ t in Ioi t₀, ENNReal.ofReal (A * t ^ (-γ)) :=
          setLIntegral_mono' measurableSet_Ioi fun t ht => htail t (ht₀pos.trans ht)
      _ = ENNReal.ofReal (∫ t in Ioi t₀, A * t ^ (-γ)) := by
          rw [ofReal_integral_eq_lintegral_ofReal hint]
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact mul_nonneg hA.le (Real.rpow_nonneg (ht₀pos.trans ht).le _)
      _ = ENNReal.ofReal (A * t₀ ^ (-γ + 1) / (γ - 1)) := by
          rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) ht₀pos]
          congr 1
          rw [mul_div_assoc]
          congr 1
          conv_lhs => rw [show (-γ + 1) = -(γ - 1) by ring]
          rw [div_neg, neg_div, neg_neg, show -(γ - 1) = -γ + 1 by ring]
  calc (∫⁻ t in Ioc 0 t₀, ν {x | t < f x}) + ∫⁻ t in Ioi t₀, ν {x | t < f x}
      ≤ ENNReal.ofReal (m * t₀) + ENNReal.ofReal (A * t₀ ^ (-γ + 1) / (γ - 1)) :=
        add_le_add h1 h2
    _ = ENNReal.ofReal (m * t₀ + A * t₀ ^ (-γ + 1) / (γ - 1)) := by
        rw [ENNReal.ofReal_add (mul_nonneg hm.le ht₀pos.le)
          (div_nonneg (mul_nonneg hA.le (Real.rpow_nonneg ht₀pos.le _)) (by linarith))]
    _ = _ := by rw [layerCake_algebra hA hm hγ]

end PDE.Ch4Green
