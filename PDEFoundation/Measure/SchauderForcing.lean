module

public import PDEFoundation.Measure.ForcingScale

/-!
# Scale-invariant forcing bound for Schauder estimates

At the source exponent `d / (1 - α)`, the factor `R^(1 - α)` cancels the
volume normalization of a round ball. The remaining unit-ball volume factor
is bounded by a constant depending only on the dimension.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

/-- The finite source exponent associated with a Hölder exponent. -/
noncomputable def schauderSourceExponent (d : ℕ) (α : ℝ) : ℝ :=
  (d : ℝ) / (1 - α)

theorem two_le_schauderSourceExponent {d : ℕ} {α : ℝ}
    (hd : 2 ≤ d) (hα : 0 < α) (hαone : α < 1) :
    2 ≤ schauderSourceExponent d α := by
  have hden : 0 < 1 - α := by linarith
  unfold schauderSourceExponent
  rw [le_div_iff₀ hden]
  have hdReal : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  nlinarith

theorem schauderSourceExponent_scale_identity {d : ℕ} {α : ℝ}
    (hd : 2 ≤ d) (hαone : α < 1) :
    (d : ℝ) / schauderSourceExponent d α = 1 - α := by
  have hden : 1 - α ≠ 0 := ne_of_gt (by linarith)
  unfold schauderSourceExponent
  field_simp [hden]

/-- A dimension-only price for converting the unit-ball volume factor at a
source exponent to a uniform constant. -/
noncomputable def schauderForcingVolumePrice (d : ℕ) : ℝ :=
  max 1 ((volume (euclideanBall (0 : Vec d) 1)).toReal)⁻¹

theorem schauderForcingVolumePrice_pos (d : ℕ) :
    0 < schauderForcingVolumePrice d := by
  unfold schauderForcingVolumePrice
  exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)

private theorem unitBall_volume_rpow_neg_inv_le_price
    {d : ℕ} {p : ℝ} (hp : 1 ≤ p) :
    (volume (euclideanBall (0 : Vec d) 1)).toReal ^ (-1 / p) ≤
      schauderForcingVolumePrice d := by
  let v := (volume (euclideanBall (0 : Vec d) 1)).toReal
  have hv : 0 < v := by
    dsimp [v]
    exact volume_euclideanBall_toReal_pos (0 : Vec d) (by norm_num)
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hrecip : 1 / p ≤ 1 := (div_le_one hp0).2 hp
  have hexpNonpos : -1 / p ≤ 0 := by
    rw [neg_div]
    exact neg_nonpos.mpr (div_nonneg (by norm_num) hp0.le)
  have hexpLower : -1 ≤ -1 / p := by
    rw [neg_div]
    linarith
  by_cases hvone : 1 ≤ v
  · have hpow := Real.rpow_le_one_of_one_le_of_nonpos hvone hexpNonpos
    unfold schauderForcingVolumePrice
    dsimp [v] at hpow ⊢
    exact hpow.trans (le_max_left _ _)
  · have hvle : v ≤ 1 := le_of_not_ge hvone
    have hpow : v ^ (-1 / p) ≤ v ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hv hvle hexpLower
    unfold schauderForcingVolumePrice
    dsimp [v] at hpow ⊢
    rw [Real.rpow_neg_one] at hpow
    exact hpow.trans (le_max_right _ _)

theorem schauder_scale_mul_euclideanBall_volume_factor
    {d : ℕ} {α R : ℝ} (hd : 2 ≤ d) (hα : 0 < α)
    (hαone : α < 1) (z : Vec d) (hR : 0 < R) :
    R ^ (1 - α) *
        (volume (euclideanBall z R)).toReal ^
          (-1 / schauderSourceExponent d α) =
      (volume (euclideanBall (0 : Vec d) 1)).toReal ^
        (-1 / schauderSourceExponent d α) := by
  let v := (volume (euclideanBall (0 : Vec d) 1)).toReal
  have hv : 0 < v := by
    dsimp [v]
    exact volume_euclideanBall_toReal_pos (0 : Vec d) (by norm_num)
  have hexp :
      (1 - α) + (d : ℝ) * (-1 / schauderSourceExponent d α) = 0 := by
    have hid := schauderSourceExponent_scale_identity hd hαone
    rw [← hid]
    have hpne : schauderSourceExponent d α ≠ 0 := by
      have hp := two_le_schauderSourceExponent hd hα hαone
      linarith
    field_simp [hpne]
    ring
  calc
    R ^ (1 - α) *
        (volume (euclideanBall z R)).toReal ^
          (-1 / schauderSourceExponent d α) =
      R ^ (1 - α) *
        (R ^ d * (volume (euclideanBall (0 : Vec d) 1)).toReal) ^
          (-1 / schauderSourceExponent d α) := by
            rw [volume_euclideanBall_toReal_eq_unit_mul_of_pos z hR]
    _ = R ^ (1 - α) *
          ((R ^ d) ^ (-1 / schauderSourceExponent d α) *
            (volume (euclideanBall (0 : Vec d) 1)).toReal ^
              (-1 / schauderSourceExponent d α)) := by
            rw [Real.mul_rpow (pow_nonneg hR.le d) hv.le]
    _ = (R ^ (1 - α) *
          R ^ ((d : ℝ) * (-1 / schauderSourceExponent d α))) *
          (volume (euclideanBall (0 : Vec d) 1)).toReal ^
            (-1 / schauderSourceExponent d α) := by
            rw [← Real.rpow_natCast R d, ← Real.rpow_mul hR.le]
            exact (mul_assoc _ _ _).symm
    _ = R ^ ((1 - α) +
          (d : ℝ) * (-1 / schauderSourceExponent d α)) *
          (volume (euclideanBall (0 : Vec d) 1)).toReal ^
            (-1 / schauderSourceExponent d α) := by
            rw [← Real.rpow_add hR]
    _ = (volume (euclideanBall (0 : Vec d) 1)).toReal ^
          (-1 / schauderSourceExponent d α) := by
            rw [hexp, Real.rpow_zero, one_mul]

/-- The scale-invariant forcing estimate on a subball of the unit ball.
Its constant depends only on the dimension. -/
theorem schauder_forcing_euclideanBall_le_unitLp
    {d : ℕ} {α R : ℝ} (hd : 2 ≤ d) (hα : 0 < α)
    (hαone : α < 1) (z : Vec d) (hR : 0 < R)
    {F : Vec d → Vec d}
    (hBV : euclideanBall z R ⊆ euclideanBall (0 : Vec d) 1)
    (hF : MemLp (fun x => vecEuclideanNorm (F x))
      (ENNReal.ofReal (schauderSourceExponent d α))
      (volumeOn (euclideanBall (0 : Vec d) 1))) :
    R ^ (1 - α) *
        Real.sqrt (integralAverage (euclideanBall z R)
          (fun x => vecNormSq (F x))) ≤
      schauderForcingVolumePrice d *
        euclideanFieldLpNormOn (euclideanBall (0 : Vec d) 1)
          (ENNReal.ofReal (schauderSourceExponent d α)) F hF := by
  let p := schauderSourceExponent d α
  have hp : 2 ≤ p := by
    dsimp [p]
    exact two_le_schauderSourceExponent hd hα hαone
  have hlocal :=
    sqrt_integralAverage_vecNormSq_euclideanBall_le_euclideanFieldLpNormOn
      (F := F) (p := p) hp z hR hBV hF
  have hvolume :=
    schauder_scale_mul_euclideanBall_volume_factor hd hα hαone z hR
  have hprice := unitBall_volume_rpow_neg_inv_le_price (d := d)
    (le_trans (by norm_num : (1 : ℝ) ≤ 2) hp)
  have hrawNonneg :
      0 ≤ euclideanFieldLpNormOn (euclideanBall (0 : Vec d) 1)
        (ENNReal.ofReal p) F hF := by
    unfold euclideanFieldLpNormOn
    rw [lpNormOn_eq_toReal]
    exact ENNReal.toReal_nonneg
  calc
    R ^ (1 - α) *
        Real.sqrt (integralAverage (euclideanBall z R)
          (fun x => vecNormSq (F x))) ≤
      R ^ (1 - α) *
        ((volume (euclideanBall z R)).toReal ^ (-1 / p) *
          euclideanFieldLpNormOn (euclideanBall (0 : Vec d) 1)
            (ENNReal.ofReal p) F hF) :=
      mul_le_mul_of_nonneg_left hlocal (Real.rpow_nonneg hR.le _)
    _ = ((volume (euclideanBall (0 : Vec d) 1)).toReal ^ (-1 / p)) *
          euclideanFieldLpNormOn (euclideanBall (0 : Vec d) 1)
            (ENNReal.ofReal p) F hF := by
          dsimp [p] at hvolume ⊢
          rw [← mul_assoc, hvolume]
    _ ≤ schauderForcingVolumePrice d *
          euclideanFieldLpNormOn (euclideanBall (0 : Vec d) 1)
            (ENNReal.ofReal p) F hF :=
          mul_le_mul_of_nonneg_right hprice hrawNonneg

end PDE
