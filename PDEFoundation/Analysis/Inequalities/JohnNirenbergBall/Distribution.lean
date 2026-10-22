module

public import PDEFoundation.Analysis.Inequalities.JohnNirenbergBall.Integrate

/-!
# Step 5: the distribution function of `u - (u)_H`
-/

@[expose] public section

namespace PDE.JohnNirenbergBall

open BoxIntegral MeasureTheory Set PDE.JohnNirenberg
open scoped ENNReal

variable {d : ℕ} {R : ℝ} {x : Vec d} {u : Vec d → ℝ} {M : ℝ}

/-- The exponential rate `θ` of the distribution estimate. -/
noncomputable def jnTheta (d : ℕ) : ℝ := min (jnRate d / 2) (1 / (8 * chainConst d))

theorem jnTheta_pos (hd : 0 < d) : 0 < jnTheta d := by
  have := jnRate_pos hd
  have := chainConst_pos hd
  unfold jnTheta
  exact lt_min (by positivity) (by positivity)

section Distribution

variable (hd : 0 < d) (hR : 0 < R) (hloc : LocallyIntegrableOn u (euclideanBall x R) volume)
  (hM : BMOBound (euclideanBall x R) u M) (hMpos : 0 < M)

include hd hR hloc hM hMpos

/-- Step 5: `|{x ∈ B : |u - (u)_H| > t}| ≤ 2 d (2 e² + 4) exp(-θ t / M) |B|`. -/
theorem volume_tail_H_le {t : ℝ} (ht : 0 < t) :
    (volume {z ∈ euclideanBall x R |
        t < |u z - integralAverage (euclideanBall x (3 * R / 4)) u|}).toReal ≤
      2 * d * ((2 * Real.exp 2 + 4) * Real.exp (-(jnTheta d * (t / M)))) *
        (volume (euclideanBall x R)).toReal := by
  set P : Vec d → Prop := fun z => t < |u z - integralAverage (euclideanBall x (3 * R / 4)) u|
  have hBtop := volume_euclideanBall_ne_top x hR.le
  have hK := chainConst_pos hd
  have ha := jnRate_pos hd
  have hτ : 0 ≤ t / M := by positivity
  obtain ⟨hsumm, hbound⟩ := series_bound (jnRate d) (chainConst d) (t / M) ha hK hτ
  set m : ℕ → ℝ := fun k => min 1 (Real.exp 2 *
    Real.exp (-((t / M - chainConst d * (k + 1)) * jnRate d))) with hm
  have hm0 : ∀ k, 0 ≤ m k := fun k => le_min zero_le_one (by positivity)
  have hstep : ∀ k : ℕ, volume {z ∈ layerUnion hd hR x k | P z} ≤
      ENNReal.ofReal (2 * d * ((1 / 2 : ℝ) ^ k * m k)) * volume (euclideanBall x R) := by
    intro k
    have h1 := measure_layerUnion_inter_le hd hR k P (ENNReal.ofReal (m k))
      (fun n hn => volume_tail_layerCube_le hd hR hloc hM hMpos hn ht)
    refine h1.trans ?_
    calc _ ≤ ENNReal.ofReal (m k) * (ENNReal.ofReal (2 * d / 2 ^ k) * volume (euclideanBall x R)) := by
          gcongr; exact volume_layerUnion_le_ofReal hd hR k
      _ = _ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (hm0 k)]
          congr 2
          rw [div_eq_mul_inv, ← inv_pow, ← one_div]; ring
  have hsub : {z ∈ euclideanBall x R | P z} ⊆ ⋃ k : ℕ, {z ∈ layerUnion hd hR x k | P z} := by
    rintro z ⟨hz, hPz⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (ball_subset_iUnion_layerUnion hd hR hz)
    exact Set.mem_iUnion.mpr ⟨k, hk, hPz⟩
  have hmain : volume {z ∈ euclideanBall x R | P z} ≤
      ENNReal.ofReal (2 * d * ((2 * Real.exp 2 + 4) * Real.exp (-(jnTheta d * (t / M))))) *
        volume (euclideanBall x R) := by
    calc volume {z ∈ euclideanBall x R | P z}
        ≤ volume (⋃ k : ℕ, {z ∈ layerUnion hd hR x k | P z}) := measure_mono hsub
      _ ≤ ∑' k : ℕ, volume {z ∈ layerUnion hd hR x k | P z} := measure_iUnion_le _
      _ ≤ ∑' k : ℕ, ENNReal.ofReal (2 * d * ((1 / 2 : ℝ) ^ k * m k)) *
            volume (euclideanBall x R) := ENNReal.tsum_le_tsum hstep
      _ = ENNReal.ofReal (2 * d * ∑' k : ℕ, ((1 / 2 : ℝ) ^ k * m k)) *
            volume (euclideanBall x R) := by
          rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg
            (fun k => by have := hm0 k; positivity) (hsumm.mul_left _), tsum_mul_left]
      _ ≤ _ := by
          gcongr
          simpa [jnTheta, hm] using hbound
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBtop) hmain
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  exact this

end Distribution

end PDE.JohnNirenbergBall
