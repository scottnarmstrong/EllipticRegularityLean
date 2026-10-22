module

public import EllipticRegularity.Ch4.Planar.WirtingerCoeff

/-!
# The Wirtinger inequality (Lemma 4.23)

Fourier proof: by Parseval, the Fourier coefficients of `w'` are `i n c_n`, and the
zeroth coefficient of `w` is its mean.
-/

@[expose] public section

namespace PDE.Ch4Planar

open MeasureTheory

/-- Wirtinger inequality (Lemma 4.23), in the exact form of the statement `wirtinger_inequality`. -/
theorem wirtinger_inequality_full (w : ℝ → ℝ)
    (hper : Function.Periodic w (2 * Real.pi))
    (hac : AbsolutelyContinuousOnInterval w 0 (2 * Real.pi))
    (hderiv : MemLp (deriv w) 2 (volume.restrict (Set.Icc 0 (2 * Real.pi)))) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (w θ - (1 / (2 * Real.pi)) * ∫ t in (0 : ℝ)..(2 * Real.pi), w t) ^ 2 ≤
      ∫ θ in (0 : ℝ)..(2 * Real.pi), (deriv w θ) ^ 2 := by
  have hab := zero_lt_two_pi'
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcont : ContinuousOn w (Set.Icc 0 (2 * Real.pi)) := by
    simpa [Set.uIcc_of_le hab.le] using hac.continuousOn
  -- the function is in L² on the period
  have hwL2 : MemLp w 2 (volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
    have hm : AEStronglyMeasurable w (volume.restrict (Set.Ioc 0 (2 * Real.pi))) :=
      (hcont.aestronglyMeasurable measurableSet_Icc).mono_measure
        (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl)
    refine MemLp.of_bound hm C ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hC x (Set.Ioc_subset_Icc_self hx)
  have hdL2 : MemLp (deriv w) 2 (volume.restrict (Set.Ioc 0 (2 * Real.pi))) :=
    hderiv.mono_measure (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl)
  have hwC : MemLp (fun x => (w x : ℂ)) 2 (volume.restrict (Set.Ioc 0 (2 * Real.pi))) :=
    hwL2.ofReal
  have hdC : MemLp (fun x => ((deriv w x : ℝ) : ℂ)) 2
      (volume.restrict (Set.Ioc 0 (2 * Real.pi))) := hdL2.ofReal
  have hPw := hasSum_sq_fourierCoeffOn hab hwC
  have hPd := hasSum_sq_fourierCoeffOn hab hdC
  have hnorm : ∀ g : ℝ → ℝ, (fun x => ‖(g x : ℂ)‖ ^ 2) = fun x => g x ^ 2 := by
    intro g; funext x; rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [hnorm, sub_zero] at hPw hPd
  -- zeroth coefficient
  have hc0 : ‖fourierCoeffOn hab (fun x => (w x : ℂ)) 0‖ ^ 2 =
      ((1 / (2 * Real.pi)) * ∫ t in (0 : ℝ)..(2 * Real.pi), w t) ^ 2 := by
    rw [norm_sq_fourierCoeffOn_ofReal (hcont.intervalIntegrable_of_Icc hab.le)]
    simp
    ring
  -- termwise comparison
  have hterm : ∀ n : ℤ, ‖fourierCoeffOn hab (fun x => (w x : ℂ)) n‖ ^ 2 -
      (if n = 0 then ‖fourierCoeffOn hab (fun x => (w x : ℂ)) 0‖ ^ 2 else 0) ≤
      ‖fourierCoeffOn hab (fun x => ((deriv w x : ℝ) : ℂ)) n‖ ^ 2 := by
    intro n
    rw [norm_sq_fourierCoeffOn_deriv hper hac n]
    by_cases hn : n = 0
    · subst hn; simp
    · simp only [hn, ↓reduceIte, sub_zero]
      have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
        have : (1 : ℤ) ≤ n ^ 2 := by
          have := Int.one_le_abs hn
          nlinarith [sq_abs n]
        exact_mod_cast this
      nlinarith [sq_nonneg ‖fourierCoeffOn hab (fun x => (w x : ℂ)) n‖]
  have hsumw : HasSum (fun n : ℤ => ‖fourierCoeffOn hab (fun x => (w x : ℂ)) n‖ ^ 2 -
      (if n = 0 then ‖fourierCoeffOn hab (fun x => (w x : ℂ)) 0‖ ^ 2 else 0))
      ((2 * Real.pi)⁻¹ • (∫ x in (0 : ℝ)..(2 * Real.pi), w x ^ 2) -
        ‖fourierCoeffOn hab (fun x => (w x : ℂ)) 0‖ ^ 2) := by
    refine hPw.sub ?_
    convert hasSum_ite_eq (0 : ℤ) (‖fourierCoeffOn hab (fun x => (w x : ℂ)) 0‖ ^ 2) using 1
  have hle := hasSum_le hterm hsumw hPd
  -- expand the left side
  set I1 := ∫ t in (0 : ℝ)..(2 * Real.pi), w t with hI1
  set I2 := ∫ t in (0 : ℝ)..(2 * Real.pi), w t ^ 2 with hI2
  have hw1 : IntervalIntegrable w volume 0 (2 * Real.pi) :=
    hcont.intervalIntegrable_of_Icc hab.le
  have hw2 : IntervalIntegrable (fun t => w t ^ 2) volume 0 (2 * Real.pi) :=
    (hcont.pow 2).intervalIntegrable_of_Icc hab.le
  have hexp : ∫ θ in (0 : ℝ)..(2 * Real.pi),
      (w θ - (1 / (2 * Real.pi)) * I1) ^ 2 =
      I2 - (1 / (2 * Real.pi)) * I1 * (2 * I1) + (1 / (2 * Real.pi) * I1) ^ 2 * (2 * Real.pi) := by
    have : ∀ θ : ℝ, (w θ - (1 / (2 * Real.pi)) * I1) ^ 2 =
        w θ ^ 2 - (2 * ((1 / (2 * Real.pi)) * I1)) * w θ + (1 / (2 * Real.pi) * I1) ^ 2 := by
      intro θ; ring
    simp_rw [this]
    rw [intervalIntegral.integral_add (hw2.sub (hw1.const_mul _)) intervalIntegrable_const,
      intervalIntegral.integral_sub hw2 (hw1.const_mul _), intervalIntegral.integral_const_mul]
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    ring
  rw [hexp]
  have hd2 : (2 * Real.pi)⁻¹ • (∫ x in (0 : ℝ)..(2 * Real.pi), deriv w x ^ 2) =
      ∑' n : ℤ, ‖fourierCoeffOn hab (fun x => ((deriv w x : ℝ) : ℂ)) n‖ ^ 2 := hPd.tsum_eq.symm
  rw [hc0] at hle
  rw [smul_eq_mul] at hle
  have key : (2 * Real.pi)⁻¹ * I2 - (1 / (2 * Real.pi) * I1) ^ 2 ≤
      (2 * Real.pi)⁻¹ * ∫ x in (0 : ℝ)..(2 * Real.pi), deriv w x ^ 2 := by
    simpa [smul_eq_mul, hPd.tsum_eq] using hle
  have h2pi : (2 * Real.pi) ≠ 0 := by positivity
  have := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
  have e1 : 2 * Real.pi * ((2 * Real.pi)⁻¹ * I2 - (1 / (2 * Real.pi) * I1) ^ 2) =
      I2 - (1 / (2 * Real.pi)) * I1 * (2 * I1) + (1 / (2 * Real.pi) * I1) ^ 2 * (2 * Real.pi) := by
    field_simp
    ring
  have e2 : 2 * Real.pi * ((2 * Real.pi)⁻¹ * ∫ x in (0 : ℝ)..(2 * Real.pi), deriv w x ^ 2) =
      ∫ x in (0 : ℝ)..(2 * Real.pi), deriv w x ^ 2 := by
    field_simp
  rw [e1, e2] at this
  exact this

end PDE.Ch4Planar
