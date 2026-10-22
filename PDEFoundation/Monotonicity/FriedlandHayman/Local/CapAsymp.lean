module

public import PDEFoundation.Monotonicity.FriedlandHayman.Local.Cap

/-!
# Friedland--Hayman: asymptotics of the cap moments

`m_ε > 0` for `0 < ε < π`, and `m'_ε / m_ε → 0` as `ε → 0⁺`, from `(1 - cos φ)² ≤ φ⁴ / 4` and
`sin φ ≥ 2φ / π` on `[0, π / 2]`.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PDE.FHLane

noncomputable section

namespace Local

theorem intervalIntegrable_sin_pow (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun φ : ℝ => Real.sin φ ^ n) volume a b :=
  (Real.continuous_sin.pow n).intervalIntegrable _ _

theorem intervalIntegrable_cap' (k : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun φ : ℝ => (1 - Real.cos φ) ^ 2 * Real.sin φ ^ k) volume a b :=
  (((continuous_const.sub Real.continuous_cos).pow 2).mul (Real.continuous_sin.pow k))
    |>.intervalIntegrable _ _

theorem integral_sin_pow_pos (D : ℕ) {ε : ℝ} (hε : 0 < ε) (hε' : ε < Real.pi) :
    0 < ∫ φ in (0 : ℝ)..ε, Real.sin φ ^ D := by
  refine intervalIntegral.intervalIntegral_pos_of_pos_on (intervalIntegrable_sin_pow D 0 ε)
    (fun φ hφ => pow_pos (Real.sin_pos_of_pos_of_lt_pi hφ.1 (hφ.2.trans hε')) D) hε

theorem integral_cap'_nonneg (k : ℕ) {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ Real.pi) :
    0 ≤ ∫ φ in (0 : ℝ)..ε, (1 - Real.cos φ) ^ 2 * Real.sin φ ^ k := by
  refine intervalIntegral.integral_nonneg hε.le fun φ hφ => ?_
  exact mul_nonneg (sq_nonneg _) (pow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hφ.1
    (hφ.2.trans hε')) _)

/-- Upper bound for the `m'` integral. -/
theorem integral_cap'_le (k : ℕ) {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ Real.pi / 2) :
    ∫ φ in (0 : ℝ)..ε, (1 - Real.cos φ) ^ 2 * Real.sin φ ^ k ≤
      ε ^ (k + 5) / (4 * ((k : ℝ) + 5)) := by
  have hpi := Real.pi_pos
  have h1 : ∫ φ in (0 : ℝ)..ε, (1 - Real.cos φ) ^ 2 * Real.sin φ ^ k ≤
      ∫ φ in (0 : ℝ)..ε, φ ^ (k + 4) / 4 := by
    refine intervalIntegral.integral_mono_on hε.le (intervalIntegrable_cap' k 0 ε)
      ((continuous_pow _).div_const _ |>.intervalIntegrable _ _) fun φ hφ => ?_
    have hc := Real.one_sub_sq_div_two_le_cos (x := φ)
    have hc0 : 0 ≤ 1 - Real.cos φ := by linarith [Real.cos_le_one φ]
    have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hφ.1 (by linarith [hφ.2])
    have hs1 := Real.sin_le hφ.1
    have e1 : (1 - Real.cos φ) ^ 2 ≤ (φ ^ 2 / 2) ^ 2 :=
      pow_le_pow_left₀ hc0 (by linarith) 2
    have e2 : Real.sin φ ^ k ≤ φ ^ k := pow_le_pow_left₀ hs0 hs1 k
    calc (1 - Real.cos φ) ^ 2 * Real.sin φ ^ k ≤ (φ ^ 2 / 2) ^ 2 * φ ^ k :=
          mul_le_mul e1 e2 (pow_nonneg hs0 _) (sq_nonneg _)
      _ = φ ^ (k + 4) / 4 := by ring
  refine h1.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_div, integral_pow]
  have : ((k + 4 : ℕ) : ℝ) + 1 = (k : ℝ) + 5 := by push_cast; ring
  rw [this]
  have h5 : (k + 4 + 1) = k + 5 := rfl
  rw [h5]
  field_simp
  simp

/-- Lower bound for the `m` integral. -/
theorem integral_sin_pow_ge (D : ℕ) {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ Real.pi / 2) :
    (2 / Real.pi) ^ D * ε ^ (D + 1) / ((D : ℝ) + 1) ≤ ∫ φ in (0 : ℝ)..ε, Real.sin φ ^ D := by
  have hpi := Real.pi_pos
  have h1 : ∫ φ in (0 : ℝ)..ε, (2 / Real.pi) ^ D * φ ^ D ≤ ∫ φ in (0 : ℝ)..ε, Real.sin φ ^ D := by
    refine intervalIntegral.integral_mono_on hε.le
      ((continuous_const.mul (continuous_pow _)).intervalIntegrable _ _)
      (intervalIntegrable_sin_pow D 0 ε) fun φ hφ => ?_
    have hs : 2 / Real.pi * φ ≤ Real.sin φ := Real.mul_le_sin hφ.1 (hφ.2.trans hε')
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity [hφ.1]) hs D
  refine le_trans (le_of_eq ?_) h1
  rw [intervalIntegral.integral_const_mul, integral_pow]
  simp
  ring

end Local

open Local

theorem capMom_pos {D : ℕ} (hD : 2 ≤ D) {ε : ℝ} (hε : 0 < ε) (hε' : ε < Real.pi) :
    0 < capMom D ε := by
  have : NeZero (D - 1) := ⟨by omega⟩
  have hD' : (2 : ℝ) ≤ D := by exact_mod_cast hD
  unfold capMom
  exact mul_pos (div_pos sphereArea_pos (by linarith)) (integral_sin_pow_pos D hε hε')

theorem capMom'_nonneg {D : ℕ} (hD : 2 ≤ D) {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ Real.pi) :
    0 ≤ capMom' D ε := by
  have : NeZero (D - 1) := ⟨by omega⟩
  exact mul_nonneg sphereArea_pos.le (integral_cap'_nonneg _ hε hε')

theorem tendsto_capMom'_div_capMom {D : ℕ} (hD : 2 ≤ D) :
    Tendsto (fun ε => capMom' D ε / capMom D ε) (𝓝[>] 0) (𝓝 0) := by
  have : NeZero (D - 1) := ⟨by omega⟩
  have hpi := Real.pi_pos
  have hD' : (2 : ℝ) ≤ D := by exact_mod_cast hD
  obtain ⟨k, rfl⟩ : ∃ k, D = k + 2 := ⟨D - 2, by omega⟩
  set c : ℝ := ((k + 2 : ℕ) - 1 : ℝ) * (((k + 2 : ℕ) : ℝ) + 1) /
    (4 * ((k : ℝ) + 5) * (2 / Real.pi) ^ (k + 2)) with hc
  have hlim : Tendsto (fun ε : ℝ => c * ε ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun ε : ℝ => c * ε ^ 2) (𝓝 0) (𝓝 (c * 0 ^ 2)) :=
      (continuous_const.mul (continuous_pow 2)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < Real.pi / 2 by positivity)] with ε hε
    exact div_nonneg (capMom'_nonneg hD hε.1 (by linarith [hε.2])) (capMom_pos hD hε.1
      (by linarith [hε.2])).le
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < Real.pi / 2 by positivity)] with ε hε
    have hε0 := hε.1
    have hε1 := hε.2
    have hm := capMom_pos hD hε0 (by linarith)
    rw [div_le_iff₀ hm]
    have hA := integral_cap'_le k hε0 hε1.le
    have hB := integral_sin_pow_ge (k + 2) hε0 hε1.le
    set A := ∫ φ in (0 : ℝ)..ε, (1 - Real.cos φ) ^ 2 * Real.sin φ ^ k
    set B := ∫ φ in (0 : ℝ)..ε, Real.sin φ ^ (k + 2)
    have hσ := (sphereArea_pos (d := k + 2 - 1))
    have hD1 : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) - 1 := by push_cast; linarith
    have hcB : (2 / Real.pi) ^ (k + 2) > 0 := by positivity
    unfold capMom' capMom
    have hdiff : (A : ℝ) ≤ c * ε ^ 2 * B * (((k + 2 : ℕ) : ℝ) - 1)⁻¹ := by
      have hb : (2 / Real.pi) ^ (k + 2) * ε ^ (k + 2 + 1) / (((k + 2 : ℕ) : ℝ) + 1) ≤ B := hB
      have h3 : c * ε ^ 2 * ((2 / Real.pi) ^ (k + 2) * ε ^ (k + 2 + 1) /
          (((k + 2 : ℕ) : ℝ) + 1)) * (((k + 2 : ℕ) : ℝ) - 1)⁻¹ =
          ε ^ (k + 5) / (4 * ((k : ℝ) + 5)) := by
        rw [hc]
        have : ε ^ (k + 5) = ε ^ (k + 2 + 1) * ε ^ 2 := by ring
        rw [this]
        have : (((k + 2 : ℕ) : ℝ) - 1) ≠ 0 := hD1.ne'
        have : (((k + 2 : ℕ) : ℝ) + 1) ≠ 0 := by positivity
        have : ((k : ℝ) + 5) ≠ 0 := by positivity
        field_simp
      calc A ≤ ε ^ (k + 5) / (4 * ((k : ℝ) + 5)) := hA
        _ = c * ε ^ 2 * ((2 / Real.pi) ^ (k + 2) * ε ^ (k + 2 + 1) /
            (((k + 2 : ℕ) : ℝ) + 1)) * (((k + 2 : ℕ) : ℝ) - 1)⁻¹ := h3.symm
        _ ≤ c * ε ^ 2 * B * (((k + 2 : ℕ) : ℝ) - 1)⁻¹ := by
            gcongr
    calc sphereArea (k + 2 - 1) * A ≤ sphereArea (k + 2 - 1) *
          (c * ε ^ 2 * B * (((k + 2 : ℕ) : ℝ) - 1)⁻¹) := mul_le_mul_of_nonneg_left hdiff hσ.le
      _ = _ := by ring

end

end PDE.FHLane
