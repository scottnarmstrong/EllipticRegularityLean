module

public import PDEFoundation.Measure.BallVolume
public import EllipticRegularity.Parabolic.Cauchy.L1.Contraction

@[expose] public section

namespace PDE.Parabolic.Cauchy.OnDiag

open MeasureTheory Set

/-- The logarithmic factor in the scale is bounded below by one when
the ellipticity ratio is at least one. -/
theorem nashLogFactor_ge_one {Lam : ℝ} (hLam : 1 ≤ Lam) :
    1 ≤ Real.log (Real.exp 1 * Lam) := by
  have hLampos : 0 < Lam := lt_of_lt_of_le (by norm_num) hLam
  have hlog : 0 ≤ Real.log Lam := Real.log_nonneg hLam
  rw [Real.log_mul (ne_of_gt (Real.exp_pos 1)) hLampos.ne', Real.log_exp]
  linarith

/-- The input support-radius restriction is already below the on-diagonal
scale, up to any dimensional constant at least one. -/
theorem support_radius_le_onDiag_scale {Lam τ ε C₁ : ℝ}
    (hLam : 1 ≤ Lam) (hτ : 0 < τ) (hε : ε ^ 2 ≤ Lam * τ)
    (hC₁ : 1 ≤ C₁) :
    ε ≤ C₁ * Real.sqrt (Lam * τ * Real.log (Real.exp 1 * Lam)) := by
  by_cases hεneg : ε < 0
  · have hscale : 0 ≤ Real.sqrt (Lam * τ * Real.log (Real.exp 1 * Lam)) := by
      positivity
    have hC₁pos : 0 ≤ C₁ := le_trans (by norm_num) hC₁
    calc
      ε ≤ 0 := le_of_lt hεneg
      _ ≤ C₁ * Real.sqrt (Lam * τ * Real.log (Real.exp 1 * Lam)) :=
        mul_nonneg hC₁pos hscale
  · have hεnonneg : 0 ≤ ε := le_of_not_gt hεneg
    have hLamτ : 0 ≤ Lam * τ := mul_nonneg (le_of_lt (lt_of_lt_of_le (by norm_num) hLam)) hτ.le
    have hεsqrt : ε ≤ Real.sqrt (Lam * τ) := by
      have hsquare : Real.sqrt (ε ^ 2) = ε := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hεnonneg]
      rw [← hsquare]
      exact Real.sqrt_le_sqrt hε
    have hlog := nashLogFactor_ge_one hLam
    have hrad : Real.sqrt (Lam * τ) ≤
        Real.sqrt (Lam * τ * Real.log (Real.exp 1 * Lam)) := by
      apply Real.sqrt_le_sqrt
      nlinarith [hLamτ, hlog]
    have hroot : 0 ≤ Real.sqrt (Lam * τ * Real.log (Real.exp 1 * Lam)) := by positivity
    calc
      ε ≤ Real.sqrt (Lam * τ) := hεsqrt
      _ ≤ Real.sqrt (Lam * τ * Real.log (Real.exp 1 * Lam)) := hrad
      _ ≤ C₁ * Real.sqrt (Lam * τ * Real.log (Real.exp 1 * Lam)) :=
        le_mul_of_one_le_left hroot hC₁

/-- Half of the mass in a finite round ball forces a quantitative lower bound
on the global square integral. -/
theorem square_integral_lower_of_half_mass {d : ℕ} (y : Vec d) {R : ℝ}
    (hR : 0 < R) (v : Vec d → ℝ)
    (hv2 : MemLp v 2 volume) (hvnonneg : 0 ≤ᵐ[volume] v)
    (hmass : (1 / 2 : ℝ) ≤ ∫ x in euclideanBall y R, v x) :
    (1 / 4 : ℝ) ≤ (volume (euclideanBall y R)).toReal *
      ∫ x : Vec d, v x ^ 2 := by
  let B : Set (Vec d) := euclideanBall y R
  let μ : Measure (Vec d) := volume.restrict B
  have hfinite : volume B ≠ ⊤ := PDE.volume_euclideanBall_ne_top y hR.le
  let : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.mpr hfinite⟩
  have hmem : MemLp v 2 μ := hv2.mono_measure Measure.restrict_le_self
  have hone : MemLp (fun _ : Vec d => (1 : ℝ)) 2 μ := memLp_const 1
  have hpos : 0 ≤ᵐ[μ] v :=
    ae_restrict_of_ae hvnonneg
  have honepos : 0 ≤ᵐ[μ] (fun _ : Vec d => (1 : ℝ)) :=
    Filter.Eventually.of_forall fun _ => by norm_num
  have hmem' : MemLp v (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hmem
  have hone' : MemLp (fun _ : Vec d => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hone
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := μ) (p := 2) (q := 2) Real.HolderConjugate.two_two
    hpos honepos hmem' hone'
  have hholder' :
      (∫ x in B, v x) ≤
        (∫ x in B, v x ^ 2) ^ (1 / (2 : ℝ)) *
          (volume B).toReal ^ (1 / (2 : ℝ)) := by
    simpa [μ, B, Measure.real, integral_const, one_pow, mul_one] using hholder
  have hmass' : (1 / 2 : ℝ) ≤ ∫ x in B, v x := by
    simpa [B] using hmass
  have hsqInt : 0 ≤ ∫ x in B, v x ^ 2 :=
    integral_nonneg_of_ae (ae_of_all _ fun x => sq_nonneg (v x))
  have hvol : 0 ≤ (volume B).toReal := ENNReal.toReal_nonneg
  have hmul :
      (1 / 2 : ℝ) ≤ Real.sqrt (∫ x in B, v x ^ 2) *
        Real.sqrt (volume B).toReal := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    exact hmass'.trans hholder'
  have hsqmul :
      (1 / 2 : ℝ) ^ 2 ≤
        (Real.sqrt (∫ x in B, v x ^ 2) * Real.sqrt (volume B).toReal) ^ 2 :=
    (sq_le_sq₀ (by norm_num) (by positivity)).2 hmul
  have hsqrtInt := Real.sq_sqrt hsqInt
  have hsqrtVol := Real.sq_sqrt hvol
  have hlocal :
      (1 / 4 : ℝ) ≤ (volume B).toReal * ∫ x in B, v x ^ 2 := by
    nlinarith [hsqmul, hsqrtInt, hsqrtVol]
  have hglobalInt : IntegrableOn (fun x : Vec d => v x ^ 2) univ volume := by
    simpa [IntegrableOn, Real.norm_eq_abs, sq_abs] using hv2.integrable_sq
  have hglobal :
      ∫ x in B, v x ^ 2 ≤ ∫ x : Vec d, v x ^ 2 := by
    have hglobal' : ∫ x in B, v x ^ 2 ≤ ∫ x in univ, v x ^ 2 :=
      setIntegral_mono_set hglobalInt
      (ae_of_all _ fun x => sq_nonneg (v x))
      (ae_of_all _ fun x hx => Set.mem_univ x)
    simpa only [setIntegral_univ] using hglobal'
  exact hlocal.trans (mul_le_mul_of_nonneg_left hglobal hvol)

/-- The round-ball version with the dimensional unit-ball volume and the
radius scaling made explicit. -/
theorem square_integral_lower_of_half_mass_scaled {d : ℕ} (y : Vec d)
    {R : ℝ} (hR : 0 < R) (v : Vec d → ℝ)
    (hv2 : MemLp v 2 volume) (hvnonneg : 0 ≤ᵐ[volume] v)
    (hmass : (1 / 2 : ℝ) ≤ ∫ x in euclideanBall y R, v x) :
    1 / (4 * (volume (euclideanBall (0 : Vec d) 1)).toReal * R ^ d) ≤
      ∫ x : Vec d, v x ^ 2 := by
  have hbase := square_integral_lower_of_half_mass y hR v hv2 hvnonneg hmass
  have hscale := PDE.volume_euclideanBall_toReal_eq_unit_mul_of_pos y hR
  have hvolpos := PDE.volume_euclideanBall_toReal_pos y hR
  have hRpow : 0 < R ^ d := pow_pos hR _
  rw [hscale] at hbase
  have hcoef :
      (1 / 4 : ℝ) / (R ^ d * (volume (euclideanBall (0 : Vec d) 1)).toReal) =
        1 / (4 * (volume (euclideanBall (0 : Vec d) 1)).toReal * R ^ d) := by ring
  have hdiv :
      (1 / 4 : ℝ) / (R ^ d * (volume (euclideanBall (0 : Vec d) 1)).toReal) ≤
        ∫ x : Vec d, v x ^ 2 := by
    apply (div_le_iff₀ (mul_pos hRpow
      (PDE.volume_euclideanBall_toReal_pos (0 : Vec d) (by norm_num)))).2
    simpa [mul_comm] using hbase
  simpa only [hcoef] using hdiv

/-- ENNReal packaging of the half-mass square-integral lower bound. -/
theorem lintegral_square_lower_of_half_mass_scaled {d : ℕ} (y : Vec d)
    {R : ℝ} (hR : 0 < R) (v : Vec d → ℝ)
    (hv2 : MemLp v 2 volume) (hvnonneg : 0 ≤ᵐ[volume] v)
    (hmass : (1 / 2 : ℝ) ≤ ∫ x in euclideanBall y R, v x) :
    ENNReal.ofReal
        (1 / (4 * (volume (euclideanBall (0 : Vec d) 1)).toReal * R ^ d)) ≤
      ∫⁻ x : Vec d, ENNReal.ofReal (v x ^ 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal hv2.integrable_sq
    (ae_of_all _ fun x : Vec d => sq_nonneg (v x))]
  exact ENNReal.ofReal_le_ofReal
    (square_integral_lower_of_half_mass_scaled y hR v hv2 hvnonneg hmass)

/-- Cauchy--Schwarz converts half of the mass in the Nash radius to
the corresponding dimensionally scaled `L²` lower bound. -/
theorem lintegral_square_lower_at_nash_scale {d : ℕ} (y : Vec d)
    {Lam τ C₁ : ℝ} (hLam : 1 ≤ Lam) (hτ : 0 < τ) (hC₁ : 1 ≤ C₁)
    (v : Vec d → ℝ) (hv2 : MemLp v 2 volume)
    (hvnonneg : 0 ≤ᵐ[volume] v)
    (hmass : (1 / 2 : ℝ) ≤ ∫ x in euclideanBall y
      (C₁ * Real.sqrt (Lam * τ * Real.log (Real.exp 1 * Lam))), v x) :
    ENNReal.ofReal
        ((1 / (4 * (volume (euclideanBall (0 : Vec d) 1)).toReal * C₁ ^ d)) *
          (Lam * τ * Real.log (Real.exp 1 * Lam)) ^ (-(d : ℝ) / 2)) ≤
      ∫⁻ x : Vec d, ENNReal.ofReal (v x ^ 2) := by
  let K : ℝ := Lam * τ * Real.log (Real.exp 1 * Lam)
  let R : ℝ := C₁ * Real.sqrt K
  have hlog := nashLogFactor_ge_one hLam
  have hKpos : 0 < K := by
    dsimp [K]
    exact mul_pos (mul_pos (lt_of_lt_of_le (by norm_num) hLam) hτ)
      (lt_of_lt_of_le (by norm_num) hlog)
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hmass' : (1 / 2 : ℝ) ≤ ∫ x in euclideanBall y R, v x := by
    simpa [R, K] using hmass
  have hbase := lintegral_square_lower_of_half_mass_scaled y hRpos v
    hv2 hvnonneg hmass'
  have hrootPow : (Real.sqrt K) ^ d = K ^ ((d : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hKpos.le]
    congr 1
    ring
  have hRpow : R ^ d = C₁ ^ d * K ^ ((d : ℝ) / 2) := by
    rw [show R = C₁ * Real.sqrt K by rfl, mul_pow, hrootPow]
  have hVpos : 0 < (volume (euclideanBall (0 : Vec d) 1)).toReal :=
    PDE.volume_euclideanBall_toReal_pos 0 (by norm_num)
  have hCpow : 0 < C₁ ^ d := pow_pos (lt_of_lt_of_le (by norm_num) hC₁) _
  have hKpow : 0 < K ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos hKpos _
  have hKneg : K ^ (-(d : ℝ) / 2) = (K ^ ((d : ℝ) / 2))⁻¹ := by
    rw [show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring, Real.rpow_neg hKpos.le]
  have hcoef :
      1 / (4 * (volume (euclideanBall (0 : Vec d) 1)).toReal * R ^ d) =
        (1 / (4 * (volume (euclideanBall (0 : Vec d) 1)).toReal * C₁ ^ d)) *
          K ^ (-(d : ℝ) / 2) := by
    rw [hRpow, hKneg]
    field_simp [ne_of_gt hVpos, ne_of_gt hCpow, ne_of_gt hKpow]
  simpa only [K, hcoef] using hbase

end PDE.Parabolic.Cauchy.OnDiag
