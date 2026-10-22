module

public import EllipticRegularity.Ch4.GreenFunction.D3Harnack

/-!
# The upper bound of Proposition 4.42 (Step 1): the mean of `G` on `A_r`

`|A_r| ≥ |B_1| r^d / 2`, and Stampacchia's bound gives `⨍_{A_r} G ≤ C₀ |A_r|^{2/d - 1}`.  Hence a
lower Harnack constant `m ≤ G` on `A_r` satisfies `m ≤ C₀ (|B_1|/2)^{(2-d)/d} r^{2-d}`.
-/

@[expose] public section

open scoped Topology ENNReal

namespace PDE.Ch4Green

open MeasureTheory PDE Filter

variable {d : ℕ}

/-- `|B_r \ B_{r/2}| ≥ |B_1| r^d / 2`. -/
theorem volume_annulus_toReal_ge (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) :
    (volume (euclideanBall (0 : Vec d) 1)).toReal * r ^ d / 2 ≤
      (volume (euclideanBall (0 : Vec d) r \ euclideanBall (0 : Vec d) (r / 2))).toReal := by
  have hsub : euclideanBall (0 : Vec d) (r / 2) ⊆ euclideanBall (0 : Vec d) r :=
    euclideanBall_mono (by positivity) (by linarith)
  rw [measure_sdiff hsub (measurableSet_euclideanBall _ _).nullMeasurableSet
    (volume_euclideanBall_ne_top _ (by positivity)),
    ENNReal.toReal_sub_of_le (measure_mono hsub) (volume_euclideanBall_ne_top _ hr.le),
    volume_euclideanBall_toReal_eq_unit_mul_of_pos _ hr,
    volume_euclideanBall_toReal_eq_unit_mul_of_pos _ (by positivity : 0 < r / 2)]
  have hb := (ENNReal.toReal_nonneg : 0 ≤ (volume (euclideanBall (0 : Vec d) 1)).toReal)
  have h2 : (r / 2) ^ d ≤ r ^ d / 2 := by
    rw [div_pow]
    have : (2 : ℝ) ≤ 2 ^ d := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) hd
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have hrd : 0 ≤ r ^ d := by positivity
    nlinarith
  nlinarith

/-- **Mean bound**: a constant `m ≥ 0` below `G` a.e. on `A_r` satisfies
`m ≤ C₀ (|B_1|/2)^{(2-d)/d} r^{2-d}`. -/
theorem le_of_ae_le_of_stampacchia (hd : 3 ≤ d) {r : ℝ} (hr : 0 < r) {G : Vec d → ℝ}
    {C₀ m : ℝ} (hC₀ : 0 ≤ C₀) (hm : 0 ≤ m)
    (hmG : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) r \ euclideanBall (0 : Vec d) (r / 2)),
      m ≤ G x)
    (hstamp : ∫⁻ x in euclideanBall (0 : Vec d) r \ euclideanBall (0 : Vec d) (r / 2),
        ENNReal.ofReal (G x) ≤
      ENNReal.ofReal (C₀ * (volume (euclideanBall (0 : Vec d) r \
        euclideanBall (0 : Vec d) (r / 2))).toReal ^ ((2 : ℝ) / d))) :
    m ≤ C₀ * ((volume (euclideanBall (0 : Vec d) 1)).toReal / 2) ^ ((2 - (d : ℝ)) / d) *
      r ^ (2 - (d : ℝ)) := by
  set A := euclideanBall (0 : Vec d) r \ euclideanBall (0 : Vec d) (r / 2)
  have hAm : MeasurableSet A := (measurableSet_euclideanBall _ _).diff (measurableSet_euclideanBall
      _ _)
  have hAfin : volume A ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_euclideanBall_ne_top _ hr.le) (measure_mono Set.sdiff_subset)
  set α := (volume A).toReal with hα
  have hb : 0 < (volume (euclideanBall (0 : Vec d) 1)).toReal :=
    volume_euclideanBall_toReal_pos _ one_pos
  have hαlow := volume_annulus_toReal_ge (d := d) (by omega) hr
  rw [← hα] at hαlow
  have hαpos : 0 < α := lt_of_lt_of_le (by positivity) hαlow
  -- `m α ≤ C₀ α^{2/d}`
  have h1 : ENNReal.ofReal (m * α) ≤ ENNReal.ofReal (C₀ * α ^ ((2 : ℝ) / d)) := by
    calc ENNReal.ofReal (m * α) = ∫⁻ _ in A, ENNReal.ofReal m := by
          rw [setLIntegral_const, ENNReal.ofReal_mul hm, hα, ENNReal.ofReal_toReal hAfin]
      _ ≤ ∫⁻ x in A, ENNReal.ofReal (G x) :=
          lintegral_mono_ae (hmG.mono fun x hx => ENNReal.ofReal_le_ofReal hx)
      _ ≤ _ := hstamp
  have h2 : m * α ≤ C₀ * α ^ ((2 : ℝ) / d) :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC₀ (Real.rpow_nonneg hαpos.le _))).1 h1
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have h3 : m ≤ C₀ * α ^ ((2 - (d : ℝ)) / d) := by
    have hsplit : α ^ ((2 : ℝ) / d) = α ^ ((2 - (d : ℝ)) / d) * α := by
      rw [← Real.rpow_add_one hαpos.ne']
      congr 1
      field_simp
      ring
    rw [hsplit, ← mul_assoc] at h2
    exact le_of_mul_le_mul_right h2 hαpos
  rw [mul_assoc]
  refine h3.trans (mul_le_mul_of_nonneg_left ?_ hC₀)
  have hexp : (2 - (d : ℝ)) / d ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by
      have : (3 : ℝ) ≤ d := by exact_mod_cast hd
      linarith) hdpos.le
  have h4 : α ^ ((2 - (d : ℝ)) / d) ≤
      ((volume (euclideanBall (0 : Vec d) 1)).toReal * r ^ d / 2) ^ ((2 - (d : ℝ)) / d) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hαlow hexp
  refine h4.trans (le_of_eq ?_)
  rw [show (volume (euclideanBall (0 : Vec d) 1)).toReal * r ^ d / 2 =
      (volume (euclideanBall (0 : Vec d) 1)).toReal / 2 * r ^ d by ring,
    Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hr.le]
  congr 2
  field_simp

end PDE.Ch4Green
