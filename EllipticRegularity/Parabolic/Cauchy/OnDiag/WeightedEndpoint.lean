module

public import EllipticRegularity.Parabolic.Cauchy.OnDiag.Moment
public import EllipticRegularity.Parabolic.Cauchy.Weights.TruncatedEnergyLimit
public import EllipticRegularity.Parabolic.Cauchy.Energy.Exhaustion
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# A Gaussian weighted square bound for a compactly supported datum

The polynomial Nash time moment controls the truncated-distance Gaussian
energy.  Fatou's lemma then removes the spatial cap and gives a bound for the
full distance weight.
-/

@[expose] public section

namespace PDE.Parabolic.Cauchy.OnDiag

open MeasureTheory Set Filter Topology

/-- Dimensional constant in the weighted square estimate. -/
noncomputable def nashWeightedSquareConstant (d : ℕ) (hd : 0 < d) : ℝ :=
  1 + (((d : ℝ) + 2) / 2) *
      Real.exp (2 * (((d : ℝ) + 2) / 2)) *
        2 ^ ((d : ℝ) / 2) * (1 + cauchyUnitMassNashConstant d hd)

/-- The weighted square constant is positive. -/
theorem nashWeightedSquareConstant_pos (d : ℕ) (hd : 0 < d) :
    0 < nashWeightedSquareConstant d hd := by
  unfold nashWeightedSquareConstant
  have hN := cauchyUnitMassNashConstant_pos d hd
  positivity

private theorem nashSupport_subset_closedBall {d : ℕ} {y : Vec d} {ε : ℝ} :
    euclideanBall y ε ⊆ euclideanClosedBall y |ε| := by
  intro x hx
  change vecNormSq (x - y) < ε ^ 2 at hx
  rw [mem_euclideanClosedBall_iff_vecEuclideanNorm_le (abs_nonneg ε)]
  calc
    vecEuclideanNorm (x - y) = Real.sqrt (vecNormSq (x - y)) := rfl
    _ ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt hx.le
    _ = |ε| := Real.sqrt_sq_eq_abs ε

private theorem euclideanSetDistance_centerBall_lower {d : ℕ} {y : Vec d}
    {S : ℝ} (hS : 0 ≤ S) (x : Vec d) :
    vecEuclideanNorm (x - y) - S ≤
      PDE.Parabolic.Cauchy.Weights.euclideanSetDistance
        (euclideanClosedBall y S) x := by
  let K : Set (Vec d) := euclideanClosedBall y S
  have hK : K.Nonempty := by
    refine ⟨y, ?_⟩
    change y ∈ euclideanClosedBall y S
    rw [mem_euclideanClosedBall_iff_vecEuclideanNorm_le hS]
    simpa [vecEuclideanNorm, vecNormSq, vecDot] using hS
  change vecEuclideanNorm (x - y) - S ≤
    sInf (Set.range fun z : K => vecEuclideanNorm (x - (z : Vec d)))
  have hrange : (Set.range fun z : K => vecEuclideanNorm (x - (z : Vec d))).Nonempty := by
    rcases hK with ⟨z, hz⟩
    exact ⟨vecEuclideanNorm (x - z), ⟨⟨z, hz⟩, rfl⟩⟩
  apply le_csInf hrange
  rintro _ ⟨⟨z, hz⟩, rfl⟩
  change z ∈ euclideanClosedBall y S at hz
  have hzNorm : vecEuclideanNorm (z - y) ≤ S :=
    (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hS).mp hz
  have htri : vecEuclideanNorm (x - y) ≤
      vecEuclideanNorm (x - z) + vecEuclideanNorm (z - y) := by
    calc
      vecEuclideanNorm (x - y) = vecEuclideanNorm ((x - z) + (z - y)) := by
        congr 1
        abel
      _ ≤ vecEuclideanNorm (x - z) + vecEuclideanNorm (z - y) :=
        vecEuclideanNorm_add_le _ _
  linarith

/-- A unit-mass solution whose datum is supported in the ball `B_ε(y)` has a
dimensionally controlled Gaussian weighted square integral at positive time.
The exponent uses `6 Λ (t-s)` so that the positive regularizing shift can be
removed uniformly. -/
theorem cauchy_unit_mass_weighted_square_bound {d : ℕ} (hd : 0 < d)
    {Lam s H σ ε : ℝ} (hH : 0 < H) (hLam : 1 ≤ Lam)
    (hσ : 0 < σ) (hσH : σ ≤ H / 2)
    (a : ParCoeffField d)
    (ha : IsParabolicCoeff 1 Lam a univ (Icc s (s + H)))
    (y : Vec d) (f : Vec d → ℝ) (hf1 : Integrable f volume)
    (hf2 : MemLp f 2 volume)
    (hσData : σ ^ (((d : ℝ) + 2) / 2) * (∫ x : Vec d, f x ^ 2) ≤ H)
    (hfnonneg : 0 ≤ᵐ[volume] f) (hfmass : ∫ x, f x = 1)
    (hfsupp : ∀ᵐ x : Vec d, x ∉ euclideanBall y ε → f x = 0)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s (s + H)))
    (hu : IsCauchySolution a s (s + H) f u) :
    ∫⁻ x : Vec d, ENNReal.ofReal
        (Real.exp (PDE.Parabolic.Cauchy.Weights.euclideanSetDistance
          (euclideanClosedBall y |ε|) x ^ 2 / (6 * Lam * H)) *
          u.toFun (x, s + H) ^ 2) ≤
      ENNReal.ofReal
        (nashWeightedSquareConstant d hd * H ^ (-(d : ℝ) / 2)) := by
  let p : ℝ := (d : ℝ) / 2
  let κ : ℝ := ((d : ℝ) + 2) / 2
  let I : ℝ := ∫ x : Vec d, f x ^ 2
  let K : Set (Vec d) := euclideanClosedBall y |ε|
  let E : ℝ := nashWeightedSquareConstant d hd
  let Q : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s (s + H)
  have hsH : s < s + H := by linarith [hH]
  have hκ : κ = p + 1 := by dsimp [κ, p]; ring
  have hK : K.Nonempty := by
    refine ⟨y, ?_⟩
    change y ∈ euclideanClosedBall y |ε|
    rw [mem_euclideanClosedBall_iff_vecEuclideanNorm_le (abs_nonneg ε)]
    simp [vecEuclideanNorm, vecNormSq, vecDot]
  have hfsuppK : ∀ᵐ x : Vec d ∂volume, x ∉ K → f x = 0 := by
    filter_upwards [hfsupp] with x hx hxK
    exact hx (fun hball => hxK (nashSupport_subset_closedBall hball))
  have hσData' : σ ^ κ * I ≤ H := by simpa [κ, I] using hσData
  have hMoment := cauchy_unit_mass_time_moment hd hσ hσH a ha f hf1 hf2
    hσData' hfnonneg hfmass u hu
  have hMomentInt : IntegrableOn
      (fun z : Vec d × ℝ =>
        (PDE.Parabolic.Cauchy.Weights.nashPositiveTimeShift σ (z.2 - s)) ^ p *
          u.toFun z ^ 2) Q := by
    simpa [p] using hMoment.1
  have hexpMoment : κ - 1 = p := by dsimp [κ, p]; ring
  have hMomentInt' : IntegrableOn
      (fun z : Vec d × ℝ =>
        (PDE.Parabolic.Cauchy.Weights.nashPositiveTimeShift σ (z.2 - s)) ^ (κ - 1) *
          u.toFun z ^ 2) Q := by
    simpa only [hexpMoment] using hMomentInt
  have hMomentBound : ∫ z in Q,
      (PDE.Parabolic.Cauchy.Weights.nashPositiveTimeShift σ (z.2 - s)) ^ p *
        u.toFun z ^ 2 ≤ 2 ^ p * (1 + cauchyUnitMassNashConstant d hd) * H := by
    simpa [Q, p] using hMoment.2
  have hUend : Integrable (fun x : Vec d => u.toFun (x, s + H) ^ 2) volume :=
    PDE.Parabolic.Cauchy.Energy.cauchy_slice_square_integrable hsH ha f hf2 u hu
      ⟨le_of_lt hsH, le_rfl⟩
  have hI : 0 ≤ I := by
    dsimp [I]
    exact integral_nonneg_of_ae (ae_of_all _ fun x => sq_nonneg (f x))
  have hA : Lam < 2 * Lam := by
    have hLamPos : 0 < Lam := lt_of_lt_of_le (by norm_num) hLam
    linarith
  have hApos : 0 < 2 * Lam := by linarith [hA]
  have hHσ : 0 < H + σ := by positivity
  have hσH' : H + σ ≤ (3 / 2 : ℝ) * H := by linarith [hσH]
  have hDmoment : ∫ z in Q,
      (PDE.Parabolic.Cauchy.Weights.nashPositiveTimeShift σ (z.2 - s)) ^ (κ - 1) *
        u.toFun z ^ 2 ≤ 2 ^ p * (1 + cauchyUnitMassNashConstant d hd) * H := by
    simpa only [hexpMoment] using hMomentBound
  have hEndpoint (n : ℕ) :
      ∫ x : Vec d,
        Real.exp (PDE.Parabolic.Cauchy.Weights.truncatedEuclideanSetDistance
          K (n : ℝ) x ^ 2 / (4 * Lam * (H + σ))) * u.toFun (x, s + H) ^ 2 ≤
      E * H ^ (-p) := by
    have htruncRaw := PDE.Parabolic.Cauchy.Weights.nashTruncatedDistance_weightedEndpoint_bound
      (d := d) (H := H) (Lam := Lam) (K := K) hK (R := n) (A := 2 * Lam)
      (σ := σ) (s := s) hH hLam (by positivity) hA hσ ha f hf1 hf2 hfsuppK u hu
      hMomentInt' hDmoment
    have hIntegralEq :
        ∫ x : Vec d,
          Real.exp (PDE.Parabolic.Cauchy.Weights.truncatedEuclideanSetDistance
            K (n : ℝ) x ^ 2 / (4 * Lam * (H + σ))) * u.toFun (x, s + H) ^ 2 =
        ∫ x : Vec d,
          Real.exp (PDE.Parabolic.Cauchy.Weights.truncatedEuclideanSetDistance
            K (n : ℝ) x ^ 2 / (2 * (2 * Lam) * (H + σ))) * u.toFun (x, s + H) ^ 2 := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        rw [show 4 * Lam * (H + σ) = 2 * (2 * Lam) * (H + σ) by ring]
    have hexpCoeff :
        κ * Real.exp (2 * κ) = ((d : ℝ) + 2) / 2 *
          Real.exp (2 * ((((d : ℝ) + 2) / 2) /
            (2 * (1 - Lam / (2 * Lam))))) := by
      have hLamNe : Lam ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hLam)
      have hden : 2 * (1 - Lam / (2 * Lam)) = 1 := by
        field_simp [hLamNe]
        ring
      have hexpArg : 2 * κ = 2 * ((((d : ℝ) + 2) / 2) /
          (2 * (1 - Lam / (2 * Lam)))) := by
        rw [hden]
        dsimp [κ]
        ring
      calc
        κ * Real.exp (2 * κ) = κ * Real.exp
            (2 * ((((d : ℝ) + 2) / 2) /
              (2 * (1 - Lam / (2 * Lam))))) := by rw [hexpArg]
        _ = ((d : ℝ) + 2) / 2 * Real.exp
            (2 * ((((d : ℝ) + 2) / 2) /
              (2 * (1 - Lam / (2 * Lam))))) := by rfl
    have htrunc : (H + σ) ^ κ *
        ∫ x : Vec d,
          Real.exp (PDE.Parabolic.Cauchy.Weights.truncatedEuclideanSetDistance
            K (n : ℝ) x ^ 2 / (4 * Lam * (H + σ))) * u.toFun (x, s + H) ^ 2 ≤
        σ ^ κ * I + κ * Real.exp (2 * κ) *
          (2 ^ p * (1 + cauchyUnitMassNashConstant d hd) * H) := by
      have htmp := htruncRaw
      rw [← hIntegralEq, ← hexpCoeff] at htmp
      simpa [κ, I] using htmp
    have hsource : σ ^ κ * I ≤ H := hσData'
    have hcoeff : κ * Real.exp (2 * κ) *
        (2 ^ p * (1 + cauchyUnitMassNashConstant d hd) * H) ≤
      (E - 1) * H := by
      apply le_of_eq
      unfold E nashWeightedSquareConstant
      have hExp : Real.exp (2 * κ) = Real.exp (2 + (d : ℝ)) := by
        congr 1
        dsimp [κ]
        ring
      rw [hExp, show κ = ((d : ℝ) + 2) / 2 by rfl,
        show p = (d : ℝ) / 2 by rfl]
      ring_nf
    have hsum : σ ^ κ * I + κ * Real.exp (2 * κ) *
        (2 ^ p * (1 + cauchyUnitMassNashConstant d hd) * H) ≤ E * H := by
      calc
        _ ≤ H + (E - 1) * H := add_le_add hsource hcoeff
        _ = E * H := by ring
    have hbound : (H + σ) ^ κ *
        ∫ x : Vec d,
          Real.exp (PDE.Parabolic.Cauchy.Weights.truncatedEuclideanSetDistance
            K (n : ℝ) x ^ 2 / (4 * Lam * (H + σ))) * u.toFun (x, s + H) ^ 2 ≤ E * H :=
      htrunc.trans hsum
    have hIntNonneg : 0 ≤ ∫ x : Vec d,
        Real.exp (PDE.Parabolic.Cauchy.Weights.truncatedEuclideanSetDistance
          K (n : ℝ) x ^ 2 / (4 * Lam * (H + σ))) * u.toFun (x, s + H) ^ 2 := by
      apply integral_nonneg_of_ae
      exact ae_of_all _ fun x => mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)
    have hHκ : 0 < H ^ κ := Real.rpow_pos_of_pos hH κ
    have hκnonneg : 0 ≤ κ := by dsimp [κ]; positivity
    have hHle : H ^ κ ≤ (H + σ) ^ κ :=
      Real.rpow_le_rpow hH.le (by linarith) hκnonneg
    have hbase : H ^ κ *
        ∫ x : Vec d,
          Real.exp (PDE.Parabolic.Cauchy.Weights.truncatedEuclideanSetDistance
            K (n : ℝ) x ^ 2 / (4 * Lam * (H + σ))) * u.toFun (x, s + H) ^ 2 ≤ E * H :=
      (mul_le_mul_of_nonneg_right hHle hIntNonneg).trans hbound
    have hpow : H ^ κ = H ^ p * H := by
      rw [hκ, Real.rpow_add hH, Real.rpow_one]
    have hcancel : H ^ p * H ^ (-p) = 1 := by
      rw [← Real.rpow_add hH, add_neg_cancel, Real.rpow_zero]
    have hfactor : H ^ κ * (E * H ^ (-p)) = E * H := by
      rw [hpow]
      calc
        (H ^ p * H) * (E * H ^ (-p)) = E * (H ^ p * H ^ (-p)) * H := by ring
        _ = E * H := by rw [hcancel]; ring
    have hmul : H ^ κ * ∫ x : Vec d,
          Real.exp (PDE.Parabolic.Cauchy.Weights.truncatedEuclideanSetDistance
            K (n : ℝ) x ^ 2 / (4 * Lam * (H + σ))) * u.toFun (x, s + H) ^ 2 ≤
        H ^ κ * (E * H ^ (-p)) := by
      rw [hfactor]
      exact hbase
    exact (mul_le_mul_iff_of_pos_left hHκ).mp hmul

  let capWeight : ℕ → Vec d → ℝ := fun n x =>
    Real.exp (PDE.Parabolic.Cauchy.Weights.truncatedEuclideanSetDistance
      K (n : ℝ) x ^ 2 / (6 * Lam * H))
  let capIntegrand : ℕ → Vec d → ℝ := fun n x => capWeight n x * u.toFun (x, s + H) ^ 2
  let distanceWeight : Vec d → ℝ := fun x =>
    Real.exp (PDE.Parabolic.Cauchy.Weights.euclideanSetDistance K x ^ 2 / (6 * Lam * H))
  let fullIntegrand : Vec d → ℝ := fun x => distanceWeight x * u.toFun (x, s + H) ^ 2
  have hcapInt (n : ℕ) : Integrable (capIntegrand n) volume := by
    have hcapCont : Continuous (capWeight n) := by
      dsimp [capWeight]
      have hdistLip := PDE.Parabolic.Cauchy.Weights.truncatedEuclideanSetDistance_eucLip
        hK (R := (n : ℝ))
      exact Real.continuous_exp.comp
        ((continuous_id.div_const (6 * Lam * H)).comp
          ((hdistLip.continuous (by norm_num : (0 : ℝ) ≤ 1)).pow 2))
    have hbound : ∀ᵐ x ∂volume, ‖capWeight n x‖ ≤ Real.exp
        ((n : ℝ) ^ 2 / (6 * Lam * H)) := by
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have hdist := PDE.Parabolic.Cauchy.Weights.truncatedEuclideanSetDistance_le
        (K := K) (R := (n : ℝ)) x
      have hdistNonneg := PDE.Parabolic.Cauchy.Weights.truncatedEuclideanSetDistance_nonneg
        hK (show 0 ≤ (n : ℝ) by positivity) x
      have hden : 0 < 6 * Lam * H := by positivity
      apply (div_le_div_iff_of_pos_right hden).2
      exact pow_le_pow_left₀ hdistNonneg hdist 2
    have h := hUend.mul_bdd (c := Real.exp ((n : ℝ)^2 / (6 * Lam * H)))
      hcapCont.aestronglyMeasurable hbound
    exact h.congr (ae_of_all _ fun x => by dsimp [capIntegrand, capWeight]; ring)
  have hcapBound (n : ℕ) : ∫ x : Vec d, capIntegrand n x ≤ E * H ^ (-p) := by
    have hdenom :
        1 / (6 * Lam * H) ≤ 1 / (4 * Lam * (H + σ)) := by
      have hpos₁ : 0 < 6 * Lam * H := by positivity
      have hpos₂ : 0 < 4 * Lam * (H + σ) := by positivity
      apply (div_le_div_iff₀ hpos₁ hpos₂).2
      have := mul_le_mul_of_nonneg_left hσH' (by linarith : 0 ≤ 4 * Lam)
      linarith
    have hpoint : ∀ x : Vec d,
        capIntegrand n x ≤ Real.exp
          (PDE.Parabolic.Cauchy.Weights.truncatedEuclideanSetDistance
            K (n : ℝ) x ^ 2 / (4 * Lam * (H + σ))) * u.toFun (x, s + H) ^ 2 := by
      intro x
      dsimp [capIntegrand, capWeight]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply Real.exp_le_exp.mpr
      have hq := sq_nonneg
        (PDE.Parabolic.Cauchy.Weights.truncatedEuclideanSetDistance K (n : ℝ) x)
      have hcoeff : (6 * Lam * H)⁻¹ ≤ (4 * Lam * (H + σ))⁻¹ := by
        simpa [one_div] using hdenom
      have harg :
          PDE.Parabolic.Cauchy.Weights.truncatedEuclideanSetDistance K (n : ℝ) x ^ 2 /
              (6 * Lam * H) ≤
            PDE.Parabolic.Cauchy.Weights.truncatedEuclideanSetDistance K (n : ℝ) x ^ 2 /
              (4 * Lam * (H + σ)) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hcoeff hq
      exact harg
    calc
      ∫ x : Vec d, capIntegrand n x ≤ ∫ x : Vec d,
          Real.exp (PDE.Parabolic.Cauchy.Weights.truncatedEuclideanSetDistance
            K (n : ℝ) x ^ 2 / (4 * Lam * (H + σ))) * u.toFun (x, s + H) ^ 2 :=
        integral_mono_ae (hcapInt n) (by
          have hStrongCont : Continuous (fun x : Vec d => Real.exp
              (PDE.Parabolic.Cauchy.Weights.truncatedEuclideanSetDistance
                K (n : ℝ) x ^ 2 / (4 * Lam * (H + σ)))) := by
            have hdistLip := PDE.Parabolic.Cauchy.Weights.truncatedEuclideanSetDistance_eucLip
              hK (R := (n : ℝ))
            exact Real.continuous_exp.comp
              ((continuous_id.div_const (4 * Lam * (H + σ))).comp
                ((hdistLip.continuous (by norm_num : (0 : ℝ) ≤ 1)).pow 2))
          have hStrongBound : ∀ᵐ x ∂volume, ‖Real.exp
              (PDE.Parabolic.Cauchy.Weights.truncatedEuclideanSetDistance
                K (n : ℝ) x ^ 2 / (4 * Lam * (H + σ)))‖ ≤
                Real.exp ((n : ℝ)^2 / (4 * Lam * (H + σ))) := by
            filter_upwards [] with x
            rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
            apply Real.exp_le_exp.mpr
            have hdist := PDE.Parabolic.Cauchy.Weights.truncatedEuclideanSetDistance_le
              (K := K) (R := (n : ℝ)) x
            have hdistNonneg := PDE.Parabolic.Cauchy.Weights.truncatedEuclideanSetDistance_nonneg
              hK (show 0 ≤ (n : ℝ) by positivity) x
            have hden : 0 < 4 * Lam * (H + σ) := by positivity
            apply (div_le_div_iff_of_pos_right hden).2
            exact pow_le_pow_left₀ hdistNonneg hdist 2
          exact hUend.bdd_mul
            (c := Real.exp ((n : ℝ)^2 / (4 * Lam * (H + σ))))
            hStrongCont.aestronglyMeasurable hStrongBound)
        (ae_of_all _ hpoint)
      _ ≤ E * H ^ (-p) := hEndpoint n
  have hcapTendsto (x : Vec d) : Tendsto
      (fun n : ℕ => PDE.Parabolic.Cauchy.Weights.truncatedEuclideanSetDistance
        K (n : ℝ) x) atTop
      (𝓝 (PDE.Parabolic.Cauchy.Weights.euclideanSetDistance K x)) := by
    let D := PDE.Parabolic.Cauchy.Weights.euclideanSetDistance K x
    have hD : 0 ≤ D := PDE.Parabolic.Cauchy.Weights.euclideanSetDistance_nonneg hK x
    have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have heventually : (fun n : ℕ => min (n : ℝ) D) =ᶠ[atTop] fun _ => D := by
      filter_upwards [hn.eventually_ge_atTop D] with n hnD
      simp [min_eq_right hnD]
    have h := tendsto_const_nhds.congr' heventually.symm
    simpa [PDE.Parabolic.Cauchy.Weights.truncatedEuclideanSetDistance, D] using h
  have hcapAEMeas (n : ℕ) : AEMeasurable (fun x : Vec d =>
      ENNReal.ofReal (capIntegrand n x)) volume := by
    exact ENNReal.continuous_ofReal.measurable.comp_aemeasurable
      (hcapInt n).aestronglyMeasurable.aemeasurable
  have hcapLintegralBound (n : ℕ) : ∫⁻ x : Vec d,
      ENNReal.ofReal (capIntegrand n x) ≤ ENNReal.ofReal (E * H ^ (-p)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hcapInt n)
      (ae_of_all _ fun x => mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))]
    exact ENNReal.ofReal_le_ofReal (hcapBound n)
  have hpointTendsto (x : Vec d) : Tendsto (fun n : ℕ =>
      ENNReal.ofReal (capIntegrand n x)) atTop
      (𝓝 (ENNReal.ofReal (fullIntegrand x))) := by
    have harg := (hcapTendsto x).pow 2
    have hscale := harg.div_const (6 * Lam * H)
    have hexp := (Real.continuous_exp.tendsto
      (PDE.Parabolic.Cauchy.Weights.euclideanSetDistance K x ^ 2 / (6 * Lam * H))).comp hscale
    have hreal := hexp.mul_const (u.toFun (x, s + H) ^ 2)
    have hfinal := (ENNReal.continuous_ofReal.tendsto
      (fullIntegrand x)).comp hreal
    exact hfinal.congr' (Filter.Eventually.of_forall fun n => by
      rfl)
  have hFatou : ∫⁻ x : Vec d, ENNReal.ofReal (fullIntegrand x) ≤
      ENNReal.ofReal (E * H ^ (-p)) := by
    calc
      _ = ∫⁻ x : Vec d, liminf (fun n : ℕ => ENNReal.ofReal (capIntegrand n x)) atTop := by
        apply lintegral_congr
        intro x
        exact (hpointTendsto x).liminf_eq.symm
      _ ≤ liminf (fun n : ℕ => ∫⁻ x : Vec d, ENNReal.ofReal (capIntegrand n x)) atTop :=
        lintegral_liminf_le' hcapAEMeas
      _ ≤ ENNReal.ofReal (E * H ^ (-p)) :=
        liminf_le_of_frequently_le' (Frequently.of_forall hcapLintegralBound)
  simpa [fullIntegrand, distanceWeight, K, p, E,
    show (-(d : ℝ) / 2) = -p by dsimp [p]; ring] using hFatou

end PDE.Parabolic.Cauchy.OnDiag
