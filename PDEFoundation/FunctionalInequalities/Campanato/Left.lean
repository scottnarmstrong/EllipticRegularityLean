module

public import PDEFoundation.FunctionalInequalities.Campanato.Averages
public import PDEFoundation.FunctionalInequalities.Campanato.Scales
public import PDEFoundation.FunctionalInequalities.Campanato.Doubling
public import PDEFoundation.FunctionalInequalities.Campanato.Differentiation
public import PDEFoundation.FunctionalInequalities.Campanato.Right
public import PDEFoundation.Regularity.Holder

/-!
# Hölder representative from a Campanato bound

Part (1) of the Campanato characterisation.  Telescoping the averages over `B_{2^{-k} r}(x)` gives a
limit `v x`, which agrees with the function at Lebesgue points and satisfies
`|v x - (u)_{B_r(x)}| ≤ C α⁻¹ K r ^ α`; comparing two points through a common ball gives the Hölder
estimate.
-/

@[expose] public section

namespace PDE.CampanatoProof

open MeasureTheory Filter Topology

variable {d : ℕ}

section Left

variable {α K : ℝ} {u : Vec d → ℝ}

/-- The Campanato hypothesis in multiplied-out form. -/
theorem osc_le_of_campanato
    (hA : ∀ x ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ, 0 < r → r < 1 / 4 →
      r ^ (-α) * integralAverage (euclideanBall x r)
        (fun y => |u y - integralAverage (euclideanBall x r) u|) ≤ K)
    {x : Vec d} (hx : x ∈ euclideanBall (0 : Vec d) (1 / 2)) {r : ℝ} (hr : 0 < r)
    (hr4 : r < 1 / 4) :
    integralAverage (euclideanBall x r)
        (fun y => |u y - integralAverage (euclideanBall x r) u|) ≤ K * r ^ α := by
  have h := hA x hx r hr hr4
  have hrα : 0 < r ^ α := Real.rpow_pos_of_pos hr α
  have : r ^ (-α) * r ^ α = 1 := by
    rw [← Real.rpow_add hr]; simp
  calc _ = r ^ α * (r ^ (-α) * integralAverage (euclideanBall x r)
        (fun y => |u y - integralAverage (euclideanBall x r) u|)) := by
        rw [← mul_assoc, mul_comm (r ^ α), this, one_mul]
    _ ≤ r ^ α * K := mul_le_mul_of_nonneg_left h hrα.le
    _ = K * r ^ α := mul_comm _ _

/-- Comparable scales have comparable averages. -/
theorem abs_avg_sub_avg_le
    (hu : IntegrableOn u (euclideanBall (0 : Vec d) 1))
    (hA : ∀ x ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ, 0 < r → r < 1 / 4 →
      r ^ (-α) * integralAverage (euclideanBall x r)
        (fun y => |u y - integralAverage (euclideanBall x r) u|) ≤ K)
    {x : Vec d} (hx : x ∈ euclideanBall (0 : Vec d) (1 / 2)) {ρ ρ' : ℝ}
    (hρ : 0 < ρ) (hρ4 : ρ < 1 / 4) (hρ' : ρ / 2 ≤ ρ') (hle : ρ' ≤ ρ) :
    |integralAverage (euclideanBall x ρ') u - integralAverage (euclideanBall x ρ) u| ≤
      2 ^ d * K * ρ ^ α := by
  have hρ'0 : 0 < ρ' := lt_of_lt_of_le (by positivity) hρ'
  have hsub : euclideanBall x ρ' ⊆ euclideanBall x ρ := euclideanBall_mono hρ'0.le hle
  have h1 := abs_integralAverage_sub_le_of_euclideanBall_subset hρ'0 hρ hsub
    (hu.mono_set (euclideanBall_subset_unit hx hρ4 hρ))
  have h2 := osc_le_of_campanato hA hx hρ hρ4
  have h3 : (ρ / ρ') ^ d ≤ 2 ^ d := by
    apply pow_le_pow_left₀ (by positivity)
    rw [div_le_iff₀ hρ'0]; linarith
  have h4 : 0 ≤ integralAverage (euclideanBall x ρ)
      (fun y => |u y - integralAverage (euclideanBall x ρ) u|) :=
    integralAverage_nonneg (measurableSet_euclideanBall x ρ) (fun _ _ => abs_nonneg _)
  calc _ ≤ _ := h1
    _ ≤ 2 ^ d * (K * ρ ^ α) :=
      (mul_le_mul h3 h2 h4 (by positivity))
    _ = _ := by ring

/-- The pointwise limit along dyadic scales, with its quantitative bound. -/
theorem exists_pointLimit (hα : 0 < α) (hK : 0 ≤ K)
    (hu : IntegrableOn u (euclideanBall (0 : Vec d) 1))
    (hA : ∀ x ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ, 0 < r → r < 1 / 4 →
      r ^ (-α) * integralAverage (euclideanBall x r)
        (fun y => |u y - integralAverage (euclideanBall x r) u|) ≤ K)
    {x : Vec d} (hx : x ∈ euclideanBall (0 : Vec d) (1 / 2)) :
    ∃ L : ℝ, Tendsto (fun n => integralAverage (euclideanBall x (dyadicScale n)) u) atTop
        (𝓝 L) ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < 1 / 4 →
        |L - integralAverage (euclideanBall x ρ) u| ≤
          2 ^ d * K * ρ ^ α / (1 - (2 : ℝ) ^ (-α)) :=
  exists_scale_limit (M := fun ρ => integralAverage (euclideanBall x ρ) u)
    (by positivity) hα
    (fun _ _ hρ hρ4 hρ' hle => abs_avg_sub_avg_le hu hA hx hρ hρ4 hρ' hle)

/-- Local Hölder estimate for any function with the pointwise limit bound. -/
theorem local_holder (hα : 0 < α) (hα1 : α ≤ 1) (hK : 0 ≤ K)
    (hu : IntegrableOn u (euclideanBall (0 : Vec d) 1))
    (hA : ∀ x ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ, 0 < r → r < 1 / 4 →
      r ^ (-α) * integralAverage (euclideanBall x r)
        (fun y => |u y - integralAverage (euclideanBall x r) u|) ≤ K)
    {v : Vec d → ℝ}
    (hv : ∀ x ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ ρ : ℝ, 0 < ρ → ρ < 1 / 4 →
      |v x - integralAverage (euclideanBall x ρ) u| ≤
        2 ^ d * K * ρ ^ α / (1 - (2 : ℝ) ^ (-α)))
    {y z : Vec d} (hy : y ∈ euclideanBall (0 : Vec d) (1 / 2))
    (hz : z ∈ euclideanBall (0 : Vec d) (1 / 2))
    (hδ : vecEuclideanNorm (y - z) < 1 / 8) :
    |v y - v z| ≤ (12 * 2 ^ d * K / α) * vecEuclideanNorm (y - z) ^ α := by
  set δ := vecEuclideanNorm (y - z) with hδdef
  have hδ0 : 0 ≤ δ := vecEuclideanNorm_nonneg _
  rcases hδ0.eq_or_lt with h0 | hpos
  · have : y = z := by
      have : vecEuclideanNorm (y - z) = 0 := h0.symm
      rw [vecEuclideanNorm_eq_zero_iff] at this
      exact sub_eq_zero.mp this
    rw [this, sub_self, abs_zero]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (vecEuclideanNorm_nonneg _) _)
  set c : ℝ := 2 ^ d * K with hc
  have hc0 : 0 ≤ c := by positivity
  set G : ℝ := 1 / (1 - (2 : ℝ) ^ (-α)) with hG
  have hq1 := two_rpow_neg_lt_one hα
  have hq0 : 0 < (2 : ℝ) ^ (-α) := Real.rpow_pos_of_pos (by norm_num) _
  have hG1 : 1 ≤ G := by
    rw [hG, le_div_iff₀ (by linarith)]; linarith
  have hG2 : G ≤ 2 / α := inv_one_sub_two_rpow_neg_le hα hα1
  have hvG : ∀ x ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ ρ : ℝ, 0 < ρ → ρ < 1 / 4 →
      |v x - integralAverage (euclideanBall x ρ) u| ≤ c * ρ ^ α * G := by
    intro x hx ρ hρ hρ4
    refine (hv x hx ρ hρ hρ4).trans (le_of_eq ?_)
    rw [hG, hc]; ring
  have h2δ : 0 < 2 * δ := by positivity
  have h2δ4 : 2 * δ < 1 / 4 := by linarith
  have t1 := hvG y hy (2 * δ) h2δ h2δ4
  have t2 := hvG z hz δ hpos (by linarith)
  have hpow : (2 * δ) ^ α ≤ 2 * δ ^ α := by
    rw [Real.mul_rpow (by norm_num) hδ0]
    have : (2 : ℝ) ^ α ≤ 2 := by
      calc (2 : ℝ) ^ α ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1
        _ = 2 := Real.rpow_one 2
    exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hδ0 _)
  have hδα : δ ^ α ≤ (2 * δ) ^ α := Real.rpow_le_rpow hδ0 (by linarith) hα.le
  have hsub : euclideanBall z δ ⊆ euclideanBall y (2 * δ) := by
    intro w hw
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hpos] at hw
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt h2δ]
    have : w - y = (w - z) + (z - y) := by abel
    rw [this]
    have h5 := vecEuclideanNorm_add_le (w - z) (z - y)
    have h6 := vecEuclideanNorm_sub_comm z y
    linarith
  have t3a := abs_integralAverage_sub_le_of_euclideanBall_subset hpos h2δ hsub
    (hu.mono_set (euclideanBall_subset_unit hy h2δ4 h2δ))
  have t3b := osc_le_of_campanato hA hy h2δ h2δ4
  have hr2 : (2 * δ / δ) ^ d = 2 ^ d := by
    rw [mul_div_assoc, div_self hpos.ne', mul_one]
  rw [hr2] at t3a
  have h4 : 0 ≤ integralAverage (euclideanBall y (2 * δ))
      (fun w => |u w - integralAverage (euclideanBall y (2 * δ)) u|) :=
    integralAverage_nonneg (measurableSet_euclideanBall y _) (fun _ _ => abs_nonneg _)
  have t3 : |integralAverage (euclideanBall z δ) u -
      integralAverage (euclideanBall y (2 * δ)) u| ≤ c * (2 * δ) ^ α := by
    refine t3a.trans ?_
    calc _ ≤ 2 ^ d * (K * (2 * δ) ^ α) := mul_le_mul_of_nonneg_left t3b (by positivity)
      _ = _ := by rw [hc]; ring
  have hX : 0 ≤ c * δ ^ α := mul_nonneg hc0 (Real.rpow_nonneg hδ0 _)
  have hY : 0 ≤ c * (2 * δ) ^ α := mul_nonneg hc0 (Real.rpow_nonneg h2δ.le _)
  have tri : |v y - v z| ≤ |v y - integralAverage (euclideanBall y (2 * δ)) u| +
      |integralAverage (euclideanBall y (2 * δ)) u - integralAverage (euclideanBall z δ) u| +
      |integralAverage (euclideanBall z δ) u - v z| := by
    calc |v y - v z| ≤ |v y - integralAverage (euclideanBall z δ) u| +
          |integralAverage (euclideanBall z δ) u - v z| := abs_sub_le _ _ _
      _ ≤ _ := by
        gcongr
        exact abs_sub_le _ _ _
  rw [abs_sub_comm (integralAverage (euclideanBall y (2 * δ)) u)
    (integralAverage (euclideanBall z δ) u)] at tri
  rw [abs_sub_comm (integralAverage (euclideanBall z δ) u) (v z)] at tri
  have e1 : c * (2 * δ) ^ α ≤ 2 * (c * δ ^ α) := by
    linarith [mul_le_mul_of_nonneg_left hpow hc0]
  have hG0 : 0 ≤ G := by linarith
  set X := c * δ ^ α with hXdef
  have hsum : |v y - v z| ≤ 5 * X * G := by
    have a1 : c * (2 * δ) ^ α * G ≤ 2 * X * G := mul_le_mul_of_nonneg_right e1 hG0
    have a2 : c * (2 * δ) ^ α ≤ 2 * X * G := by
      have : 2 * X ≤ 2 * X * G := le_mul_of_one_le_right (by linarith) hG1
      linarith
    have a3 : c * δ ^ α * G = X * G := rfl
    linarith
  have hXG : X * G ≤ X * (2 / α) := mul_le_mul_of_nonneg_left hG2 hX
  have hfin : 5 * X * G ≤ 12 * X / α := by
    have : 0 ≤ X / α := div_nonneg hX hα.le
    have h5 : 5 * (X * G) ≤ 5 * (X * (2 / α)) := by linarith
    calc 5 * X * G = 5 * (X * G) := by ring
      _ ≤ 5 * (X * (2 / α)) := h5
      _ = 10 * (X / α) := by ring
      _ ≤ 12 * X / α := by
        have e : 12 * X / α = 12 * (X / α) := by ring
        rw [e]; linarith
  have hrhs : (12 * 2 ^ d * K / α) * δ ^ α = 12 * X / α := by
    rw [hXdef, hc]; ring
  rw [hrhs]
  exact hsum.trans hfin

end Left

end PDE.CampanatoProof
