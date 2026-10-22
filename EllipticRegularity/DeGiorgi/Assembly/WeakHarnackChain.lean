module

public import EllipticRegularity.DeGiorgi.Assembly.Scaling
public import EllipticRegularity.DeGiorgi.Assembly.WeakHarnackAlgebra

/-!
# The chain of estimates in the proof of the weak Harnack inequality

Given `E1` (reverse estimate for `ū⁻¹`), `E2` (reverse Hölder for `ū`) and `E3` (crossover for
`u`), where `ū(y) = u(y/2)`, we derive the bound of `‖u‖_{L^{qχ}(B_{1/4})}^g` by
`inf_{B_{1/4}} u ^ g` with explicit constants.
-/

@[expose] public section

open scoped ENNReal Pointwise

namespace PDE.DGNMAssembly

open MeasureTheory Filter

variable {d : ℕ}

/-- The ball of radius at most `1` carries volume at most `1` when the radius is at most `1/2`. -/
theorem volume_euclideanBall_le_one {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 1 / 2) (x : Vec d) :
    volume (euclideanBall x ρ) ≤ 1 := by
  calc volume (euclideanBall x ρ) ≤ volume (Metric.ball x ρ) :=
        measure_mono (euclideanBall_subset_supBall hρ)
    _ ≤ volume (Metric.ball x (1 / 2)) :=
        measure_mono (Metric.ball_subset_ball hρ2)
    _ = 1 := by
        simp

theorem aestronglyMeasurable_ball (u : H1Function (euclideanBall (0 : Vec d) 1)) {ρ : ℝ}
    (hρ : ρ ≤ 1) (hρ0 : 0 < ρ) :
    AEStronglyMeasurable u.toFun (volumeOn (euclideanBall (0 : Vec d) ρ)) := by
  have hsub : euclideanBall (0 : Vec d) ρ ⊆ euclideanBall (0 : Vec d) 1 := by
    exact euclideanBall_mono hρ0.le hρ
  exact u.memL2.aestronglyMeasurable.mono_measure (Measure.restrict_mono hsub le_rfl)

theorem ae_pos_ball {u : H1Function (euclideanBall (0 : Vec d) 1)}
    (hpos : ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 < u.toFun x) {ρ : ℝ}
    (hρ : ρ ≤ 1) (hρ0 : 0 < ρ) :
    ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) ρ)), 0 < u.toFun x := by
  have hsub : euclideanBall (0 : Vec d) ρ ⊆ euclideanBall (0 : Vec d) 1 :=
    euclideanBall_mono hρ0.le hρ
  exact ae_mono (Measure.restrict_mono hsub le_rfl) hpos

/-- Restricted `L^g` power identity: for `0 < g`, `(‖f‖_{L^g})^g = ∫ ‖f‖ₑ^g`. -/
theorem eLpNorm_ofReal_rpow_eq {μ : Measure (Vec d)} {f : Vec d → ℝ} {g : ℝ} (hg : 0 < g)
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f (ENNReal.ofReal g) μ ^ g = ∫⁻ x, ‖f x‖ₑ ^ g ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hg) ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hg.le, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hg.ne',
    ENNReal.rpow_one]

theorem enorm_rpow_of_pos {x g : ℝ} (hx : 0 < x) :
    ‖x ^ g‖ₑ = ENNReal.ofReal (x ^ g) := by
  rw [Real.enorm_of_nonneg (Real.rpow_nonneg hx.le g)]

theorem inv_rpow_enorm_eq {x g : ℝ} (hx : 0 < x) :
    ENNReal.ofReal (x⁻¹ ^ g) = ‖x ^ (-g)‖ₑ := by
  rw [enorm_rpow_of_pos hx, Real.rpow_neg hx.le, Real.inv_rpow hx.le]

theorem enorm_rpow_eq_of_pos {x g : ℝ} (hx : 0 < x) (hg : 0 ≤ g) :
    ‖x‖ₑ ^ g = ‖x ^ g‖ₑ := by
  rw [enorm_rpow_of_pos hx, Real.enorm_of_nonneg hx.le, ENNReal.ofReal_rpow_of_nonneg hx.le hg]

theorem one_le_rpow_of_nonneg {x : ℝ≥0∞} {z : ℝ} (hx : 1 ≤ x) (hz : 0 ≤ z) : 1 ≤ x ^ z := by
  rcases hz.eq_or_lt with h | h
  · rw [← h, ENNReal.rpow_zero]
  · exact ENNReal.one_le_rpow hx h

/-- Real bound of the constant in `E2`. -/
theorem coeff_bound {Λ g q : ℝ} (hΛ : 0 ≤ Λ) (hΛg : Λ * g ^ 2 ≤ 1) (hq0 : 0 < 1 - q) (hq : q < 1)
    (hq1 : 0 < q) :
    (Λ * g ^ 2 / (1 - q) ^ 2 + 1) ^ (((d : ℝ) + 2) / 2) ≤
      2 ^ (((d : ℝ) + 2) / 2) * (1 - q) ^ (-((d : ℝ) + 2)) := by
  have ht2 : 0 < (1 - q) ^ 2 := by positivity
  have hle : (1 - q) ^ 2 ≤ 1 := pow_le_one₀ hq0.le (by linarith)
  have h1 : Λ * g ^ 2 / (1 - q) ^ 2 + 1 ≤ 2 * (1 - q) ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hq0.le, Real.rpow_two]
    have h3 : 1 ≤ 1 / (1 - q) ^ 2 := by rw [le_div_iff₀ ht2]; linarith
    have h4 : Λ * g ^ 2 / (1 - q) ^ 2 ≤ 1 / (1 - q) ^ 2 :=
      div_le_div_of_nonneg_right hΛg ht2.le
    calc Λ * g ^ 2 / (1 - q) ^ 2 + 1 ≤ 1 / (1 - q) ^ 2 + 1 / (1 - q) ^ 2 := by linarith
      _ = 2 * ((1 - q) ^ 2)⁻¹ := by ring
  have hnn : 0 ≤ Λ * g ^ 2 / (1 - q) ^ 2 + 1 := by positivity
  calc (Λ * g ^ 2 / (1 - q) ^ 2 + 1) ^ (((d : ℝ) + 2) / 2)
      ≤ (2 * (1 - q) ^ (-(2 : ℝ))) ^ (((d : ℝ) + 2) / 2) :=
        Real.rpow_le_rpow hnn h1 (by positivity)
    _ = 2 ^ (((d : ℝ) + 2) / 2) * (1 - q) ^ (-((d : ℝ) + 2)) := by
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hq0.le _), ← Real.rpow_mul hq0.le]
        congr 2
        ring

/-- Half-dilation constant. -/
theorem half_dilation_const : ((( 1 / 2 : ℝ) ^ d)⁻¹) = 2 ^ d := by
  rw [one_div, inv_pow, inv_inv]

/-- The chain of estimates `E1`, `E2`, `E3`, `E4`. -/
theorem weakHarnack_chain_instance (hd : 3 ≤ d)
    (u ub : H1Function (euclideanBall (0 : Vec d) 1))
    (hub : ∀ y, ub.toFun y = u.toFun (0 + (1 / 2 : ℝ) • y))
    (hpos : ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 < u.toFun x)
    (C0 C1 Λ g q : ℝ) (hC0 : 0 < C0) (hC1 : 0 < C1) (hg : 0 < g) (hgq : g ≤ q) (hq : q < 1)
    (hΛg : Λ * g ^ 2 ≤ 1) (hΛ : 0 < Λ)
    (E1 : ENNReal.ofReal ((Λ * g ^ 2 + 1) ^ (-((d : ℝ) / 2))) *
        (∫⁻ x in euclideanBall (0 : Vec d) 1, ENNReal.ofReal ((ub.toFun x)⁻¹ ^ g) ∂volume)⁻¹ ≤
          ENNReal.ofReal C0 *
            (essInf (fun x => ENNReal.ofReal (ub.toFun x))
              (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) ^ g)
    (E2 : (eLpNorm ub.toFun (ENNReal.ofReal (q * d / (d - 2)))
          (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) ^ g ≤
        ENNReal.ofReal (C0 * (Λ * g ^ 2 / (1 - q) ^ 2 + 1) ^ (((d : ℝ) + 2) / 2)) *
          (eLpNorm ub.toFun (ENNReal.ofReal g) (volumeOn (euclideanBall (0 : Vec d) 1))) ^ g)
    (E3 : eLpMeanNormOn (euclideanBall (0 : Vec d) (1 / 2)) 1
            (fun x => u.toFun x ^ g) *
          eLpMeanNormOn (euclideanBall (0 : Vec d) (1 / 2)) 1
            (fun x => u.toFun x ^ (-g)) ≤ ENNReal.ofReal C1) :
    (eLpNorm u.toFun (ENNReal.ofReal (q * d / (d - 2)))
        (volumeOn (euclideanBall (0 : Vec d) (1 / 4)))) ^ g ≤
      ENNReal.ofReal (C0 * 2 ^ (((d : ℝ) + 2) / 2) * 2 ^ (d : ℝ) * 2 ^ ((d : ℝ) / 2) *
          2 ^ (d : ℝ) * C0 * C1 * (1 - q) ^ (-((d : ℝ) + 2))) *
        (essInf (fun x => ENNReal.ofReal (u.toFun x))
          (volumeOn (euclideanBall (0 : Vec d) (1 / 4)))) ^ g := by
  have hr : (0 : ℝ) < 1 / 2 := by norm_num
  have h14 : (1 / 2 : ℝ) * (1 / 2) = 1 / 4 := by norm_num
  have h12 : (1 / 2 : ℝ) * 1 = 1 / 2 := by norm_num
  have hubfun : ub.toFun = fun y => u.toFun (0 + (1 / 2 : ℝ) • y) := funext hub
  set c' : ℝ≥0∞ := ENNReal.ofReal (((1 / 2 : ℝ) ^ d)⁻¹) with hc'
  have hc'eq : c' = ENNReal.ofReal (2 ^ d) := by rw [hc', half_dilation_const]
  have hc'0 : c' ≠ 0 := ofReal_inv_pow_ne_zero hr
  have hc'top : c' ≠ ⊤ := ENNReal.ofReal_ne_top
  have hc'1 : 1 ≤ c' := by
    rw [hc'eq]
    have : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
    simpa using ENNReal.ofReal_le_ofReal this
  have hpos12 := ae_pos_ball (u := u) hpos (ρ := 1 / 2) (by norm_num) (by norm_num)
  have hmeas12 := aestronglyMeasurable_ball u (ρ := 1 / 2) (by norm_num) (by norm_num)
  -- E2 transformed: the left side dominates the `L^{qχ}(B_{1/4})` norm of `u`.
  set P : ℝ≥0∞ := ENNReal.ofReal (q * d / (d - 2)) with hP
  have hXle : eLpNorm u.toFun P (volumeOn (euclideanBall (0 : Vec d) (1 / 4))) ≤
      eLpNorm ub.toFun P (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) := by
    rw [hubfun, eLpNorm_comp_aff_ball 0 hr hr, h14]
    exact le_mul_of_one_le_left (zero_le) (one_le_rpow_of_nonneg hc'1 ENNReal.toReal_nonneg)
  have hnormg : eLpNorm ub.toFun (ENNReal.ofReal g) (volumeOn (euclideanBall (0 : Vec d) 1)) ^ g =
      c' * ∫⁻ x in euclideanBall (0 : Vec d) (1 / 2), ‖u.toFun x‖ₑ ^ g := by
    rw [hubfun, eLpNorm_comp_aff_ball 0 hr one_pos, h12,
      ENNReal.mul_rpow_of_nonneg _ _ hg.le, eLpNorm_ofReal_rpow_eq hg hmeas12,
      ← ENNReal.rpow_mul]
    congr 1
    have : (1 / ENNReal.ofReal g).toReal * g = 1 := by
      rw [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofReal hg.le, inv_mul_cancel₀ hg.ne']
    rw [this, ENNReal.rpow_one]
  -- the integrals over `B_{1/2}`
  set J : ℝ≥0∞ := ∫⁻ x in euclideanBall (0 : Vec d) (1 / 2), ‖u.toFun x‖ₑ ^ g with hJ
  set K : ℝ≥0∞ :=
    ∫⁻ x in euclideanBall (0 : Vec d) (1 / 2), ENNReal.ofReal ((u.toFun x)⁻¹ ^ g) with hK
  have hE1int : ∫⁻ x in euclideanBall (0 : Vec d) 1,
      ENNReal.ofReal ((ub.toFun x)⁻¹ ^ g) ∂volume = c' * K := by
    have := lintegral_comp_aff_ball (0 : Vec d) hr one_pos
      (fun x => ENNReal.ofReal ((u.toFun x)⁻¹ ^ g))
    rw [h12] at this
    rw [hubfun]
    exact this
  have hessInf : essInf (fun x => ENNReal.ofReal (ub.toFun x))
      (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) =
      essInf (fun x => ENNReal.ofReal (u.toFun x))
        (volumeOn (euclideanBall (0 : Vec d) (1 / 4))) := by
    have := essInf_comp_aff_ball (0 : Vec d) hr hr (fun x => ENNReal.ofReal (u.toFun x))
    rw [h14] at this
    rw [hubfun]
    exact this
  -- the crossover estimate in terms of `J` and `K`
  set V : ℝ≥0∞ := volume (euclideanBall (0 : Vec d) (1 / 2)) with hV
  have hV1 : V ≤ 1 := volume_euclideanBall_le_one (by norm_num) le_rfl 0
  have hVtop : V ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hV1
  have hmean : ∀ f : Vec d → ℝ, V⁻¹ * ∫⁻ x in euclideanBall (0 : Vec d) (1 / 2), ‖f x‖ₑ ≤
      eLpMeanNormOn (euclideanBall (0 : Vec d) (1 / 2)) 1 f := by
    intro f
    rw [eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn (lt_top_iff_ne_top.2 hVtop)]
    simp only [ENNReal.toReal_one, div_one, ENNReal.rpow_one, eLpNormOn]
    gcongr
    exact lintegral_enorm_le_eLpNorm_one
  have hJc : ∫⁻ x in euclideanBall (0 : Vec d) (1 / 2), ‖u.toFun x ^ g‖ₑ = J :=
    lintegral_congr_ae (hpos12.mono fun x hx => (enorm_rpow_eq_of_pos hx hg.le).symm)
  have hKc : ∫⁻ x in euclideanBall (0 : Vec d) (1 / 2), ‖u.toFun x ^ (-g)‖ₑ = K :=
    lintegral_congr_ae (hpos12.mono fun x hx => (inv_rpow_enorm_eq hx).symm)
  have hE3' : (V⁻¹ * J) * (V⁻¹ * K) ≤ ENNReal.ofReal C1 := by
    refine le_trans ?_ E3
    have h1 := hmean (fun x => u.toFun x ^ g)
    have h2 := hmean (fun x => u.toFun x ^ (-g))
    rw [hJc] at h1
    rw [hKc] at h2
    exact mul_le_mul' h1 h2
  -- constants
  have hΛg1 : Λ * g ^ 2 + 1 ≤ 2 := by linarith
  have hΛg0 : 0 < Λ * g ^ 2 + 1 := by positivity
  have hAdef : ENNReal.ofReal ((Λ * g ^ 2 + 1) ^ (-((d : ℝ) / 2))) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hΛg0 _)).ne'
  have hFpos : 0 < (Λ * g ^ 2 / (1 - q) ^ 2 + 1) ^ (((d : ℝ) + 2) / 2) :=
    Real.rpow_pos_of_pos (by have : 0 < 1 - q := by linarith
                             positivity) _
  have hF0 : ENNReal.ofReal (C0 * (Λ * g ^ 2 / (1 - q) ^ 2 + 1) ^ (((d : ℝ) + 2) / 2)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (mul_pos hC0 hFpos)).ne'
  have hchain := weakHarnack_chain_algebra
    (X := (eLpNorm u.toFun P (volumeOn (euclideanBall (0 : Vec d) (1 / 4)))) ^ g)
    (F := ENNReal.ofReal (C0 * (Λ * g ^ 2 / (1 - q) ^ 2 + 1) ^ (((d : ℝ) + 2) / 2)))
    (c := c') (J := J) (K := K) (V := V)
    (A := ENNReal.ofReal ((Λ * g ^ 2 + 1) ^ (-((d : ℝ) / 2))))
    (C0 := ENNReal.ofReal C0) (C1 := ENNReal.ofReal C1)
    (M := (essInf (fun x => ENNReal.ofReal (u.toFun x))
          (volumeOn (euclideanBall (0 : Vec d) (1 / 4)))) ^ g)
    (by
      calc _ ≤ (eLpNorm ub.toFun P (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) ^ g :=
            ENNReal.rpow_le_rpow hXle hg.le
        _ ≤ _ := E2
        _ = _ := by rw [hnormg])
    (by rw [hE1int, hessInf] at E1; exact E1)
    hE3' hV1 hAdef ENNReal.ofReal_ne_top hc'0 hc'top
    (ENNReal.ofReal_pos.2 hC0).ne' ENNReal.ofReal_ne_top
    (ENNReal.ofReal_pos.2 hC1).ne' ENNReal.ofReal_ne_top hF0
  refine hchain.trans ?_
  -- bound the coefficient
  have hq0 : 0 < 1 - q := by linarith
  have hf0 := coeff_bound (d := d) hΛ.le hΛg hq0 hq (by linarith)
  have hf : C0 * (Λ * g ^ 2 / (1 - q) ^ 2 + 1) ^ (((d : ℝ) + 2) / 2) ≤
      C0 * 2 ^ (((d : ℝ) + 2) / 2) * (1 - q) ^ (-((d : ℝ) + 2)) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hf0 hC0.le
  have hAinv : (ENNReal.ofReal ((Λ * g ^ 2 + 1) ^ (-((d : ℝ) / 2))))⁻¹ ≤
      ENNReal.ofReal (2 ^ ((d : ℝ) / 2)) := by
    rw [← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hΛg0 _), ← Real.rpow_neg hΛg0.le,
      neg_neg]
    exact ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow hΛg0.le hΛg1 (by positivity))
  have hcoef : ENNReal.ofReal (C0 * (Λ * g ^ 2 / (1 - q) ^ 2 + 1) ^ (((d : ℝ) + 2) / 2)) * c' *
      (ENNReal.ofReal ((Λ * g ^ 2 + 1) ^ (-((d : ℝ) / 2))))⁻¹ * ENNReal.ofReal C0 * c' *
        ENNReal.ofReal C1 ≤
      ENNReal.ofReal (C0 * 2 ^ (((d : ℝ) + 2) / 2) * 2 ^ (d : ℝ) * 2 ^ ((d : ℝ) / 2) *
          2 ^ (d : ℝ) * C0 * C1 * (1 - q) ^ (-((d : ℝ) + 2))) := by
    have h2d : c' = ENNReal.ofReal (2 ^ (d : ℝ)) := by
      rw [hc'eq, Real.rpow_natCast]
    calc _ ≤ ENNReal.ofReal (C0 * 2 ^ (((d : ℝ) + 2) / 2) * (1 - q) ^ (-((d : ℝ) + 2))) * c' *
          ENNReal.ofReal (2 ^ ((d : ℝ) / 2)) * ENNReal.ofReal C0 * c' * ENNReal.ofReal C1 := by
          gcongr
      _ = _ := by
          rw [h2d, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  gcongr

end PDE.DGNMAssembly
