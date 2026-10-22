module

public import PDEFoundation.Analysis.Gehring.WhitneyFamily

/-!
# Existence of the Whitney family for `E_t`
-/

@[expose] public section

namespace PDE.Gehring

open Set MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- The averaging estimate on one Whitney cube: if `y ∉ E_t` lies in the closed cube of
half-side `(4σ + 1) ℓ / 2` around `c`, then `(⨍_{σ Q} g ^ θ) ^ (1 / θ) ≤ H t`. -/
theorem avg_rpow_le_of_not_mem (hd : 0 < d) {g : Vec d → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (hg : Integrable g volume) {t : ℝ} (ht : 0 < t) {σ : ℝ} (hσ : 2 ≤ σ) (c : Vec d) {ℓ : ℝ}
    (hℓ : 0 < ℓ) {y : Vec d} (hy : y ∈ closedCenteredAxisCube c ((4 * σ + 1) * ℓ / 2))
    (hyE : y ∉ gehringE g t) :
    (integralAverage (centeredAxisCube c (σ * ℓ / 2)) (fun x => g x ^ gehringTheta d)) ^
        (((d : ℝ) + 1) / d) ≤ gehringH d * t := by
  have hθ := gehringTheta_pos hd
  set θ := gehringTheta d with hθdef
  set f : Vec d → ℝ := fun x => g x ^ θ with hfdef
  have hf0 : ∀ x, 0 ≤ f x := fun x => Real.rpow_nonneg (hg0 x) _
  have hfm : AEStronglyMeasurable f volume := (hg.aemeasurable.pow_const _).aestronglyMeasurable
  have hσ0 : 0 < σ := by linarith
  have hR : 0 < (4 * σ + 1) * ℓ / 2 := by positivity
  have hM : cubeMaximal f y ≤ ENNReal.ofReal (t ^ θ) :=
    not_lt.1 (fun h => hyE ((mem_gehringE_iff hd g ht.le y).2 h))
  have hAvg := (cubeAvg_le_cubeMaximal f hR hy).trans hM
  unfold cubeAvg at hAvg
  have hVe : volume (closedCenteredAxisCube c ((4 * σ + 1) * ℓ / 2)) =
      ENNReal.ofReal (((4 * σ + 1) * ℓ) ^ d) := by
    rw [volume_closedCenteredAxisCube c hR.le]
    congr 2; ring
  rw [ENNReal.div_le_iff (volume_closedCenteredAxisCube_pos c hR).ne'
    (volume_closedCenteredAxisCube_ne_top c _), hVe] at hAvg
  -- the open dilate lies in the big closed cube
  have hsub : centeredAxisCube c (σ * ℓ / 2) ⊆ closedCenteredAxisCube c ((4 * σ + 1) * ℓ / 2) := by
    intro x hx i _
    have := hx i (mem_univ i)
    exact ⟨by nlinarith [this.1], by nlinarith [this.2]⟩
  have hint : ∫ x in centeredAxisCube c (σ * ℓ / 2), f x ≤
      t ^ θ * ((4 * σ + 1) * ℓ) ^ d := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => hf0 x)
      hfm.restrict]
    have h1 : ∫⁻ x in centeredAxisCube c (σ * ℓ / 2), ENNReal.ofReal (f x) ≤
        ENNReal.ofReal (t ^ θ) * ENNReal.ofReal (((4 * σ + 1) * ℓ) ^ d) := by
      have h0 : ∫⁻ x in centeredAxisCube c (σ * ℓ / 2), ENNReal.ofReal (f x) =
          ∫⁻ x in centeredAxisCube c (σ * ℓ / 2), ‖f x‖ₑ := by
        simp_rw [Real.enorm_eq_ofReal (hf0 _)]
      rw [h0]
      exact (lintegral_mono_set hsub).trans hAvg
    have h2 := ENNReal.toReal_mono (by
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg ht.le _),
      ENNReal.toReal_ofReal (by positivity)] at h2
  have hvol : (volume (centeredAxisCube c (σ * ℓ / 2))).toReal = (σ * ℓ) ^ d := by
    rw [volume_centeredAxisCube_toReal c (by positivity)]
    congr 1; ring
  set X : ℝ := (4 * σ + 1) / σ with hX
  have hX0 : 0 ≤ X := by positivity
  have hX92 : X ≤ 9 / 2 := by
    rw [hX, div_le_iff₀ hσ0]; linarith
  have hposσℓ : 0 < (σ * ℓ) ^ d := by positivity
  have hpow : ((4 * σ + 1) * ℓ) ^ d = X ^ d * (σ * ℓ) ^ d := by
    rw [← mul_pow]; congr 1; rw [hX]; field_simp
  have havg : integralAverage (centeredAxisCube c (σ * ℓ / 2)) f ≤ t ^ θ * X ^ d := by
    unfold integralAverage
    rw [hvol]
    calc ((σ * ℓ) ^ d)⁻¹ * ∫ x in centeredAxisCube c (σ * ℓ / 2), f x
        ≤ ((σ * ℓ) ^ d)⁻¹ * (t ^ θ * ((4 * σ + 1) * ℓ) ^ d) :=
          mul_le_mul_of_nonneg_left hint (by positivity)
      _ = t ^ θ * X ^ d := by rw [hpow]; field_simp
  have havg0 : 0 ≤ integralAverage (centeredAxisCube c (σ * ℓ / 2)) f :=
    integralAverage_nonneg (isOpen_centeredAxisCube _ _).measurableSet (fun x _ => hf0 x)
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hθe : θ * (((d : ℝ) + 1) / d) = 1 := by
    rw [hθdef]; unfold gehringTheta; field_simp
  have hde : (d : ℝ) * (((d : ℝ) + 1) / d) = (d : ℝ) + 1 := by field_simp
  calc (integralAverage (centeredAxisCube c (σ * ℓ / 2)) f) ^ (((d : ℝ) + 1) / d)
      ≤ (t ^ θ * X ^ d) ^ (((d : ℝ) + 1) / d) :=
        Real.rpow_le_rpow havg0 havg (by positivity)
    _ = t * X ^ (d + 1) := by
        rw [Real.mul_rpow (Real.rpow_nonneg ht.le _) (by positivity), ← Real.rpow_mul ht.le, hθe,
          Real.rpow_one, ← Real.rpow_natCast, ← Real.rpow_mul hX0, ← Real.rpow_natCast X (d + 1)]
        congr 2
        push_cast
        exact hde
    _ ≤ gehringH d * t := by
        unfold gehringH
        rw [mul_comm (_ : ℝ) t]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hX0 hX92 _) ht.le

/-- **Lemma 4.6**: for `g ≥ 0` integrable with compact support, `t > 0`,
`σ ∈ {2, 4}`, a Whitney family for `E_t = {V > t}` exists. -/
theorem exists_whitneyFamily (hd : 0 < d) {g : Vec d → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (hg : Integrable g volume) (hc : HasCompactSupport g) {t : ℝ} (ht : 0 < t) {σ : ℝ}
    (hσ : σ = 2 ∨ σ = 4) : Nonempty (WhitneyFamily d g t σ) := by
  have hσ2 : 2 ≤ σ := by
    rcases hσ with h | h
    · rw [h]
    · rw [h]; norm_num
  obtain ⟨W⟩ := exists_whitneyCover hd (isOpen_gehringE hd g ht.le)
    (isBounded_gehringE hd hg0 hg hc ht) (by linarith : 1 ≤ σ)
  refine ⟨{ toWhitneyCover := W, avg_le := fun i => ?_ }⟩
  obtain ⟨y, hy, hyE⟩ := W.exists_not_mem i
  exact avg_rpow_le_of_not_mem hd hg0 hg ht hσ2 _ (dyadicSide_pos _) hy hyE

end PDE.Gehring
