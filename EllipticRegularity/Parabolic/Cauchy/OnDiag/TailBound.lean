module

public import EllipticRegularity.Parabolic.Cauchy.OnDiag.WeightedEndpoint
public import EllipticRegularity.Parabolic.Cauchy.OnDiag.Concentration
public import EllipticRegularity.Parabolic.Cauchy.Weights.Nash
public import PDEFoundation.Measure.AffineVolume
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Tactic.NormNum.RealSqrt

/-!
# Gaussian tail control for the on-diagonal estimate

The weighted square estimate controls the L² mass outside a large ball.  A
Gaussian tail estimate and Cauchy--Schwarz turn this into an L¹ tail bound.
-/

@[expose] public section

namespace PDE.Parabolic.Cauchy.OnDiag

open MeasureTheory Set

/-- The dimensional radius constant used in the mass concentration conclusion. -/
noncomputable def nashOnDiagRadiusConstant (d : ℕ) (hd : 0 < d) : ℝ :=
  Real.sqrt (48 * (((d : ℝ) / 2) +
    Real.log (4 * nashWeightedSquareConstant d hd *
      (48 * Real.pi) ^ ((d : ℝ) / 2))))

/-- The radius constant is larger than two. -/
theorem nashOnDiagRadiusConstant_gt_two (d : ℕ) (hd : 0 < d) :
    2 < nashOnDiagRadiusConstant d hd := by
  have hd' : (1 : ℝ) / 2 ≤ (d : ℝ) / 2 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hE : 1 ≤ nashWeightedSquareConstant d hd := by
    unfold nashWeightedSquareConstant
    have hN := cauchyUnitMassNashConstant_pos d hd
    have hp : 0 ≤ (d : ℝ) / 2 := by positivity
    have hκ : 0 < ((d : ℝ) + 2) / 2 := by positivity
    have hterm : 0 ≤ (((d : ℝ) + 2) / 2) *
        Real.exp (2 * (((d : ℝ) + 2) / 2)) *
          2 ^ ((d : ℝ) / 2) * (1 + cauchyUnitMassNashConstant d hd) := by
      positivity
    linarith
  have h48π : 1 ≤ 48 * Real.pi := by
    have hπ := Real.pi_gt_three
    linarith
  have hbase : 1 ≤ 4 * nashWeightedSquareConstant d hd *
      (48 * Real.pi) ^ ((d : ℝ) / 2) := by
    have hp : 1 ≤ (48 * Real.pi) ^ ((d : ℝ) / 2) :=
      Real.one_le_rpow h48π (by positivity)
    have := mul_le_mul hE hp zero_le_one (by linarith)
    linarith
  have hlog : 0 ≤ Real.log
      (4 * nashWeightedSquareConstant d hd * (48 * Real.pi) ^ ((d : ℝ) / 2)) :=
    Real.log_nonneg hbase
  have hinside : 4 < 48 * (((d : ℝ) / 2) +
      Real.log (4 * nashWeightedSquareConstant d hd *
        (48 * Real.pi) ^ ((d : ℝ) / 2))) := by
    linarith
  have hsqrt : 2 < Real.sqrt
      (48 * (((d : ℝ) / 2) +
        Real.log (4 * nashWeightedSquareConstant d hd *
          (48 * Real.pi) ^ ((d : ℝ) / 2)))) := by
    have hs := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 4) hinside
    norm_num at hs ⊢
    exact hs
  simpa [nashOnDiagRadiusConstant] using hsqrt

private theorem euclideanSetDistance_centerBall_lower_tail {d : ℕ} {y : Vec d}
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

/-- A Gaussian weighted square bound implies a dimensionally uniform L¹ tail
bound outside the Nash radius. -/
theorem nash_weighted_square_tail_mass_bound {d : ℕ} (hd : 0 < d)
    {Lam H ε R : ℝ} (hLam : 1 ≤ Lam) (hH : 0 < H)
    (hR : 0 < R) (hRε : 2 * |ε| ≤ R)
    (hRformula : R = nashOnDiagRadiusConstant d hd *
      Real.sqrt (Lam * H * Real.log (Real.exp 1 * Lam)))
    (y : Vec d) (v : Vec d → ℝ)
    (hv1 : Integrable v volume)
    (hvnonneg : 0 ≤ᵐ[volume] v)
    (hweighted : ∫⁻ x : Vec d, ENNReal.ofReal
      (Real.exp (PDE.Parabolic.Cauchy.Weights.euclideanSetDistance
        (euclideanClosedBall y |ε|) x ^ 2 / (6 * Lam * H)) * v x ^ 2) ≤
      ENNReal.ofReal
        (nashWeightedSquareConstant d hd * H ^ (-(d : ℝ) / 2))) :
    ∫ x in {x : Vec d | R ^ 2 ≤ vecNormSq (x - y)}, v x ≤ 1 / 2 := by
  let p : ℝ := (d : ℝ) / 2
  let K : Set (Vec d) := euclideanClosedBall y |ε|
  let tail : Set (Vec d) := {x : Vec d | R ^ 2 ≤ vecNormSq (x - y)}
  let fullWeight : Vec d → ℝ := fun x =>
    Real.exp (PDE.Parabolic.Cauchy.Weights.euclideanSetDistance K x ^ 2 /
      (6 * Lam * H))
  let full : Vec d → ℝ := fun x => fullWeight x * v x ^ 2
  let f : Vec d → ℝ := fun x =>
    Real.exp (-vecNormSq (x - y) / (48 * Lam * H))
  let g : Vec d → ℝ := fun x =>
    Real.exp (vecNormSq (x - y) / (48 * Lam * H)) * v x
  have hLamPos : 0 < Lam := lt_of_lt_of_le (by norm_num) hLam
  have hK : K.Nonempty := by
    refine ⟨y, ?_⟩
    change y ∈ euclideanClosedBall y |ε|
    rw [mem_euclideanClosedBall_iff_vecEuclideanNorm_le (abs_nonneg ε)]
    simp [vecEuclideanNorm, vecNormSq, vecDot]
  have htailMeas : MeasurableSet tail := by
    have hcont : Continuous (fun x : Vec d => vecNormSq (x - y)) := by
      rw [show (fun x : Vec d => vecNormSq (x - y)) =
          fun x => ∑ i, (x i - y i) ^ 2 from by
            funext x
            exact vecNormSq_eq_sum_sq (x - y)]
      fun_prop
    exact (isClosed_le continuous_const hcont).measurableSet
  have hdistCont : Continuous
      (PDE.Parabolic.Cauchy.Weights.euclideanSetDistance K) :=
    (PDE.Parabolic.Cauchy.Weights.euclideanSetDistance_eucLip hK).continuous
      (by norm_num)
  have hfullCont : Continuous fullWeight := by
    dsimp [fullWeight]
    exact Real.continuous_exp.comp
      ((continuous_id.div_const (6 * Lam * H)).comp (hdistCont.pow 2))
  have hfullAesm : AEStronglyMeasurable full volume := by
    dsimp [full]
    exact hfullCont.aestronglyMeasurable.mul (hv1.aestronglyMeasurable.pow 2)
  have hfullNonneg : 0 ≤ᵐ[volume] full := by
    filter_upwards [] with x
    dsimp [full, fullWeight]
    positivity
  have hweighted' : ∫⁻ x : Vec d, ENNReal.ofReal (full x) ≤
      ENNReal.ofReal (nashWeightedSquareConstant d hd * H ^ (-p)) := by
    simpa [full, fullWeight, K, p, show (-(d : ℝ) / 2) = -p by dsimp [p]; ring]
      using hweighted
  have hfullFinite : ∫⁻ x : Vec d, ENNReal.ofReal (full x) ≠ ⊤ := by
    apply ne_of_lt
    exact hweighted'.trans_lt ENNReal.ofReal_lt_top
  have hfullInt : Integrable full volume :=
    (lintegral_ofReal_ne_top_iff_integrable hfullAesm hfullNonneg).mp
      hfullFinite
  have hfullBound : ∫ x : Vec d, full x ≤
      nashWeightedSquareConstant d hd * H ^ (-p) := by
    have h := hweighted'
    rw [← ofReal_integral_eq_lintegral_ofReal hfullInt hfullNonneg] at h
    have hboundNonneg : 0 ≤ nashWeightedSquareConstant d hd * H ^ (-p) := by
      exact mul_nonneg (nashWeightedSquareConstant_pos d hd).le
        (Real.rpow_pos_of_pos hH _).le
    exact (ENNReal.ofReal_le_ofReal_iff
      hboundNonneg).mp h
  have hfCont : Continuous f := by
    dsimp [f]
    have hnormSq : Continuous (fun x : Vec d => vecNormSq (x - y)) := by
      rw [show (fun x : Vec d => vecNormSq (x - y)) =
          fun x => ∑ i, (x i - y i) ^ 2 from by
            funext x
            exact vecNormSq_eq_sum_sq (x - y)]
      fun_prop
    exact Real.continuous_exp.comp
      ((continuous_neg.comp hnormSq).div_const (48 * Lam * H))
  have hGaussianBase : Integrable
      (fun z : Vec d => Real.exp (-vecNormSq z / (24 * Lam * H))) := by
    have hbase := PDE.GaussianPoincare.integrable_exp_neg_mul_vecNormSq
      (d := d) (b := (24 * Lam * H)⁻¹) (by positivity)
    apply hbase.congr
    filter_upwards [] with z
    congr 1
    field_simp
  have hfSqInt : Integrable (fun x : Vec d => f x ^ 2) volume := by
    have hmp := measurePreserving_add_right (volume : Measure (Vec d)) (-y)
    have htrans := hmp.integrable_comp_of_integrable hGaussianBase
    have htrans' : Integrable
        (fun x : Vec d => Real.exp (-vecNormSq (x - y) / (24 * Lam * H))) volume := by
      change Integrable (fun x : Vec d =>
        Real.exp (-vecNormSq (x + -y) / (24 * Lam * H))) volume at htrans
      simpa only [sub_eq_add_neg] using htrans
    apply htrans'.congr
    filter_upwards [] with x
    rw [show f x ^ 2 = Real.exp (-vecNormSq (x - y) / (24 * Lam * H)) by
      dsimp [f]
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring]
  have hfMem : MemLp f 2 volume :=
    (memLp_two_iff_integrable_sq hfCont.aestronglyMeasurable).2 hfSqInt
  have hgsqMeas : AEStronglyMeasurable (fun x : Vec d => g x ^ 2)
      (volume.restrict tail) := by
    have hgContFactor : Continuous (fun x : Vec d =>
        Real.exp (vecNormSq (x - y) / (48 * Lam * H))) := by
      exact Real.continuous_exp.comp
        ((continuous_vecNormSq.comp (continuous_id.sub continuous_const)).div_const
          (48 * Lam * H))
    have hgAesm : AEStronglyMeasurable g volume := by
      exact hgContFactor.aestronglyMeasurable.mul hv1.aestronglyMeasurable
    exact (hgAesm.pow 2).mono_measure Measure.restrict_le_self
  have hpointWeight : ∀ x ∈ tail, g x ^ 2 ≤ full x := by
    intro x hx
    have hnormSq : R ^ 2 ≤ vecNormSq (x - y) := hx
    have hnorm : R ≤ vecEuclideanNorm (x - y) := by
      rw [vecEuclideanNorm]
      exact (Real.le_sqrt' hR).mpr hnormSq
    have hdist := euclideanSetDistance_centerBall_lower_tail
      (y := y) (S := |ε|) (abs_nonneg ε) x
    have hdistNonneg := PDE.Parabolic.Cauchy.Weights.euclideanSetDistance_nonneg hK x
    have hdistLower : vecEuclideanNorm (x - y) / 2 ≤
        PDE.Parabolic.Cauchy.Weights.euclideanSetDistance K x := by
      dsimp [K]
      linarith [hRε]
    have hdistSq : vecNormSq (x - y) ≤
        4 * PDE.Parabolic.Cauchy.Weights.euclideanSetDistance K x ^ 2 := by
      have hnormSq' : vecEuclideanNorm (x - y) ^ 2 = vecNormSq (x - y) := by
        rw [vecEuclideanNorm]
        exact Real.sq_sqrt (vecNormSq_nonneg _)
      have hn0 : 0 ≤ vecEuclideanNorm (x - y) := by
        rw [vecEuclideanNorm]; exact Real.sqrt_nonneg _
      have := pow_le_pow_left₀ hn0
        (by linarith : vecEuclideanNorm (x - y) ≤
          2 * PDE.Parabolic.Cauchy.Weights.euclideanSetDistance K x) 2
      linarith
    have hden : 0 < 24 * Lam * H := by positivity
    have hratioDen :
        PDE.Parabolic.Cauchy.Weights.euclideanSetDistance K x ^ 2 /
            (6 * Lam * H) =
          (4 * PDE.Parabolic.Cauchy.Weights.euclideanSetDistance K x ^ 2) /
            (24 * Lam * H) := by
      field_simp [ne_of_gt hLamPos, ne_of_gt hH]
      ring
    have harg : vecNormSq (x - y) / (24 * Lam * H) ≤
        PDE.Parabolic.Cauchy.Weights.euclideanSetDistance K x ^ 2 /
          (6 * Lam * H) := by
      rw [hratioDen]
      apply (div_le_div_iff_of_pos_right hden).2
      linarith [hdistSq]
    have hexp := Real.exp_le_exp.mpr harg
    have huSq : 0 ≤ v x ^ 2 := sq_nonneg _
    calc
      g x ^ 2 = Real.exp (vecNormSq (x - y) / (24 * Lam * H)) * v x ^ 2 := by
        dsimp [g]
        rw [pow_two]
        calc
          Real.exp (vecNormSq (x - y) / (48 * Lam * H)) * v x *
              (Real.exp (vecNormSq (x - y) / (48 * Lam * H)) * v x) =
            (Real.exp (vecNormSq (x - y) / (48 * Lam * H)) ^ 2) * v x ^ 2 := by ring
          _ = Real.exp (2 * (vecNormSq (x - y) / (48 * Lam * H))) * v x ^ 2 := by
            rw [pow_two, ← Real.exp_add]
            congr 1
            ring_nf
          _ = Real.exp (vecNormSq (x - y) / (24 * Lam * H)) * v x ^ 2 := by
            congr 1
            field_simp
            ring_nf
      _ ≤ full x := by
        dsimp [full, fullWeight]
        exact mul_le_mul_of_nonneg_right hexp huSq
  have hgsqInt : Integrable (fun x : Vec d => g x ^ 2)
      (volume.restrict tail) := by
    apply (hfullInt.mono_measure Measure.restrict_le_self).mono' hgsqMeas
    filter_upwards [ae_restrict_mem htailMeas] with x hx
    rw [Real.norm_of_nonneg (sq_nonneg (g x))]
    exact hpointWeight x hx
  have hGMem : MemLp g 2 (volume.restrict tail) :=
    (memLp_two_iff_integrable_sq
      ((by
        have hgaesm : AEStronglyMeasurable g volume := by
          have hgContFactor : Continuous (fun x : Vec d =>
              Real.exp (vecNormSq (x - y) / (48 * Lam * H))) := by
            exact Real.continuous_exp.comp
              ((continuous_vecNormSq.comp (continuous_id.sub continuous_const)).div_const
                (48 * Lam * H))
          dsimp [g]
          exact hgContFactor.aestronglyMeasurable.mul hv1.aestronglyMeasurable
        exact hgaesm.mono_measure Measure.restrict_le_self))).2 hgsqInt
  have hFMemTail : MemLp f 2 (volume.restrict tail) :=
    hfMem.mono_measure Measure.restrict_le_self
  have hFNonneg : 0 ≤ᵐ[volume.restrict tail] f := by
    exact ae_of_all _ fun x => by dsimp [f]; positivity
  have hGNonneg : 0 ≤ᵐ[volume.restrict tail] g := by
    filter_upwards [ae_restrict_of_ae hvnonneg] with x hx
    dsimp [g]
    exact mul_nonneg (Real.exp_nonneg _) hx
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict tail) (p := 2) (q := 2)
    Real.HolderConjugate.two_two hFNonneg hGNonneg
      (by simpa using hFMemTail) (by simpa using hGMem)
  have hProdEq : ∫ x in tail, v x = ∫ x in tail, f x * g x := by
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [f, g]
    have hexp : Real.exp (-vecNormSq (x - y) / (48 * Lam * H)) *
        Real.exp (vecNormSq (x - y) / (48 * Lam * H)) = 1 := by
      rw [← Real.exp_add]
      have hsum : -vecNormSq (x - y) / (48 * Lam * H) +
          vecNormSq (x - y) / (48 * Lam * H) = 0 := by ring
      rw [hsum, Real.exp_zero]
    rw [← mul_assoc, hexp]
    ring
  have hFtail : ∫ x in tail, f x ^ 2 ≤
      Real.exp (-R ^ 2 / (48 * Lam * H)) *
        (48 * Real.pi * Lam * H) ^ p := by
    let centered : Set (Vec d) := {z | R ^ 2 ≤ vecNormSq z}
    have hset : tail = translateSet y centered := by
      ext x
      simp [tail, centered, mem_translateSet_iff_sub_mem]
    have hfSqEq (x : Vec d) : f x ^ 2 =
        Real.exp (-vecNormSq (x - y) / (24 * Lam * H)) := by
      dsimp [f]
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    calc
      ∫ x in tail, f x ^ 2 = ∫ x in tail,
          Real.exp (-vecNormSq (x - y) / (24 * Lam * H)) := by
        apply setIntegral_congr_fun htailMeas
        intro x hx
        exact hfSqEq x
      _ = ∫ x in centered,
          Real.exp (-vecNormSq ((x + y) - y) / (24 * Lam * H)) := by
        rw [hset]
        symm
        exact PDE.setIntegral_comp_addRight_translateSet y centered
          (fun x : Vec d => Real.exp (-vecNormSq (x - y) / (24 * Lam * H)))
      _ = ∫ x in centered, Real.exp (-vecNormSq x / (24 * Lam * H)) := by
        apply setIntegral_congr_fun
        · have hcont : Continuous (fun x : Vec d => vecNormSq x) := by
            rw [show (fun x : Vec d => vecNormSq x) = fun x => ∑ i, x i ^ 2 from
              funext vecNormSq_eq_sum_sq]
            fun_prop
          exact (isClosed_le continuous_const hcont).measurableSet
        · intro x hx
          simp
      _ ≤ Real.exp (-R ^ 2 / (48 * Lam * H)) *
          (48 * Real.pi * Lam * H) ^ p := by
        have hgauss := PDE.Parabolic.Cauchy.Weights.gaussian_tail_integral_le
          (d := d) (a := 24 * Lam * H) (R := R) (by positivity)
        convert hgauss using 1
        congr 1
        ring_nf
        all_goals
          rw [show p = (d : ℝ) / 2 by rfl]
          congr 1
          ring_nf
  have hGtail : ∫ x in tail, g x ^ 2 ≤
      nashWeightedSquareConstant d hd * H ^ (-p) := by
    have hfullTailInt : Integrable full (volume.restrict tail) :=
      hfullInt.mono_measure Measure.restrict_le_self
    calc
      ∫ x in tail, g x ^ 2 ≤ ∫ x in tail, full x :=
        integral_mono_ae hgsqInt hfullTailInt
          (ae_restrict_iff' htailMeas |>.2 <| Filter.Eventually.of_forall fun x hx =>
            hpointWeight x hx)
      _ ≤ ∫ x, full x := setIntegral_le_integral hfullInt
          hfullNonneg
      _ ≤ nashWeightedSquareConstant d hd * H ^ (-p) := hfullBound
  have hgaussNonneg : 0 ≤ Real.exp (-R ^ 2 / (48 * Lam * H)) *
      (48 * Real.pi * Lam * H) ^ p := by
    exact mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg (by positivity) p)
  have hEpos : 0 < nashWeightedSquareConstant d hd :=
    nashWeightedSquareConstant_pos d hd
  have hGnonneg : 0 ≤ nashWeightedSquareConstant d hd * H ^ (-p) :=
    mul_nonneg hEpos.le (Real.rpow_pos_of_pos hH _).le
  have hconst : (Real.exp (-R ^ 2 / (48 * Lam * H)) *
        (48 * Real.pi * Lam * H) ^ p) *
        (nashWeightedSquareConstant d hd * H ^ (-p)) ≤ 1 / 4 := by
    let q : ℝ := p + Real.log (4 * nashWeightedSquareConstant d hd *
      (48 * Real.pi) ^ p)
    let Y : ℝ := 4 * nashWeightedSquareConstant d hd *
      (48 * Real.pi) ^ p
    have hp : 0 ≤ p := by dsimp [p]; positivity
    have hY : 0 < Y := by
      dsimp [Y]
      exact mul_pos (mul_pos (by norm_num) hEpos) (Real.rpow_pos_of_pos
        (by linarith [Real.pi_gt_three]) p)
    have hYone : 1 ≤ Y := by
      have hBpow : 1 ≤ (48 * Real.pi) ^ p :=
        Real.one_le_rpow (by linarith [Real.pi_gt_three]) hp
      have hE : 1 ≤ nashWeightedSquareConstant d hd := by
        unfold nashWeightedSquareConstant
        have hN := cauchyUnitMassNashConstant_pos d hd
        have hp' : 0 ≤ (d : ℝ) / 2 := by positivity
        have hκ' : 0 < ((d : ℝ) + 2) / 2 := by positivity
        have hterm : 0 ≤ (((d : ℝ) + 2) / 2) *
            Real.exp (2 * (((d : ℝ) + 2) / 2)) *
              2 ^ ((d : ℝ) / 2) * (1 + cauchyUnitMassNashConstant d hd) := by
          positivity
        linarith
      dsimp [Y]
      calc
        (1 : ℝ) ≤ 4 := by norm_num
        _ ≤ 4 * nashWeightedSquareConstant d hd := by linarith [hE]
        _ ≤ 4 * nashWeightedSquareConstant d hd * (48 * Real.pi) ^ p :=
          calc
            4 * nashWeightedSquareConstant d hd =
                (4 * nashWeightedSquareConstant d hd) * 1 := by ring
            _ ≤ (4 * nashWeightedSquareConstant d hd) * (48 * Real.pi) ^ p :=
              mul_le_mul_of_nonneg_left hBpow (by positivity)
    have hlogY : 0 ≤ Real.log Y := Real.log_nonneg hYone
    have hq : p ≤ q := by dsimp [q]; linarith [hlogY]
    have hqnonneg : 0 ≤ q := le_trans hp hq
    have hlogLam : 0 ≤ Real.log Lam := Real.log_nonneg hLam
    have hlogScale : 1 ≤ Real.log (Real.exp 1 * Lam) :=
      nashLogFactor_ge_one hLam
    have hlogScaleNonneg : 0 ≤ Real.log (Real.exp 1 * Lam) :=
      le_trans (by norm_num) hlogScale
    have hLogSplit : Real.log (Real.exp 1 * Lam) = 1 + Real.log Lam := by
      rw [Real.log_mul (ne_of_gt (Real.exp_pos 1)) hLamPos.ne', Real.log_exp]
    have hR2 : R ^ 2 = 48 * q *
        (Lam * H * Real.log (Real.exp 1 * Lam)) := by
      rw [hRformula]
      have hRad : 0 ≤ 48 * q := mul_nonneg (by norm_num) hqnonneg
      have hScale : 0 ≤ Lam * H * Real.log (Real.exp 1 * Lam) := by
        exact mul_nonneg (mul_nonneg hLamPos.le hH.le) hlogScaleNonneg
      have hC : nashOnDiagRadiusConstant d hd = Real.sqrt (48 * q) := by
        change Real.sqrt (48 * (((d : ℝ) / 2) +
            Real.log (4 * nashWeightedSquareConstant d hd *
              (48 * Real.pi) ^ ((d : ℝ) / 2)))) = Real.sqrt (48 * q)
        congr 1
      rw [hC, mul_pow, Real.sq_sqrt hRad, Real.sq_sqrt hScale]
    have hRexp : R ^ 2 / (48 * Lam * H) =
        q * Real.log (Real.exp 1 * Lam) := by
      rw [hR2]
      field_simp [ne_of_gt hLamPos, ne_of_gt hH]
    have htailExp :
        Real.exp (-q * Real.log (Real.exp 1 * Lam)) * Lam ^ p ≤
          Real.exp (-q) := by
      rw [hLogSplit, Real.rpow_def_of_pos hLamPos]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hcoef : p - q ≤ 0 := sub_nonpos.mpr hq
      linarith [mul_nonpos_of_nonpos_of_nonneg hcoef hlogLam]
    have hcancel : (48 * Real.pi * Lam * H) ^ p * H ^ (-p) =
        (48 * Real.pi) ^ p * Lam ^ p := by
      have hfirst : 48 * Real.pi * Lam * H =
          (48 * Real.pi * Lam) * H := by ring
      rw [hfirst, Real.mul_rpow (by positivity) hH.le, Real.rpow_neg hH.le]
      have hHpow : H ^ p ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hH p)
      have hsecond : (48 * Real.pi * Lam) ^ p =
          (48 * Real.pi) ^ p * Lam ^ p := by
        rw [show 48 * Real.pi * Lam = (48 * Real.pi) * Lam by ring,
          Real.mul_rpow (by positivity) hLamPos.le]
      rw [hsecond]
      field_simp [hHpow]
    have hRrecast :
        Real.exp (-R ^ 2 / (48 * Lam * H)) =
          Real.exp (-q * Real.log (Real.exp 1 * Lam)) := by
      congr 1
      rw [neg_div, hRexp]
      ring
    have hExpCancel :
        nashWeightedSquareConstant d hd * (48 * Real.pi) ^ p * Real.exp (-q) =
          Real.exp (-p) / 4 := by
      rw [show q = p + Real.log Y by rfl]
      rw [show -((p + Real.log Y)) = -p - Real.log Y by ring, Real.exp_sub,
        Real.exp_log hY]
      dsimp [Y]
      field_simp [ne_of_gt hEpos]
    calc
      _ = nashWeightedSquareConstant d hd * (48 * Real.pi) ^ p *
          (Real.exp (-q * Real.log (Real.exp 1 * Lam)) * Lam ^ p) := by
            rw [hRrecast]
            calc
              Real.exp (-q * Real.log (Real.exp 1 * Lam)) *
                  (48 * Real.pi * Lam * H) ^ p *
                  (nashWeightedSquareConstant d hd * H ^ (-p)) =
                nashWeightedSquareConstant d hd *
                  Real.exp (-q * Real.log (Real.exp 1 * Lam)) *
                    ((48 * Real.pi * Lam * H) ^ p * H ^ (-p)) := by ring
              _ = nashWeightedSquareConstant d hd *
                  Real.exp (-q * Real.log (Real.exp 1 * Lam)) *
                    ((48 * Real.pi) ^ p * Lam ^ p) := by rw [hcancel]
              _ = nashWeightedSquareConstant d hd * (48 * Real.pi) ^ p *
                  (Real.exp (-q * Real.log (Real.exp 1 * Lam)) * Lam ^ p) := by ring
      _ ≤ nashWeightedSquareConstant d hd * (48 * Real.pi) ^ p * Real.exp (-q) :=
        mul_le_mul_of_nonneg_left htailExp (by positivity)
      _ = Real.exp (-p) / 4 := hExpCancel
      _ ≤ 1 / 4 := by
        exact (div_le_div_of_nonneg_right
          (Real.exp_le_one_iff.mpr (by linarith [hp])) (by norm_num))
  have hFpow : (∫ x in tail, f x ^ 2) ^ (1 / (2 : ℝ)) ≤
      (Real.exp (-R ^ 2 / (48 * Lam * H)) *
        (48 * Real.pi * Lam * H) ^ p) ^ (1 / (2 : ℝ)) :=
    Real.rpow_le_rpow (integral_nonneg_of_ae (ae_of_all _ fun x => sq_nonneg (f x)))
      hFtail (by norm_num)
  have hGpow : (∫ x in tail, g x ^ 2) ^ (1 / (2 : ℝ)) ≤
      (nashWeightedSquareConstant d hd * H ^ (-p)) ^ (1 / (2 : ℝ)) :=
    Real.rpow_le_rpow (integral_nonneg_of_ae (ae_restrict_of_ae
      (ae_of_all _ fun x => sq_nonneg (g x)))) hGtail (by norm_num)
  have hHolder' : ∫ x in tail, v x ≤
      (∫ x in tail, f x ^ 2) ^ (1 / (2 : ℝ)) *
        (∫ x in tail, g x ^ 2) ^ (1 / (2 : ℝ)) := by
    rw [hProdEq]
    simpa using hHolder
  have hrootProd :
      (Real.exp (-R ^ 2 / (48 * Lam * H)) *
        (48 * Real.pi * Lam * H) ^ p) ^ (1 / (2 : ℝ)) *
      (nashWeightedSquareConstant d hd * H ^ (-p)) ^ (1 / (2 : ℝ)) ≤ 1 / 2 := by
    rw [← Real.mul_rpow hgaussNonneg hGnonneg]
    calc
      _ ≤ (1 / 4 : ℝ) ^ (1 / (2 : ℝ)) :=
        Real.rpow_le_rpow (mul_nonneg hgaussNonneg hGnonneg) hconst (by norm_num)
      _ = 1 / 2 := by norm_num [Real.sqrt_eq_rpow]
  calc
    ∫ x in tail, v x ≤
        (∫ x in tail, f x ^ 2) ^ (1 / (2 : ℝ)) *
          (∫ x in tail, g x ^ 2) ^ (1 / (2 : ℝ)) := hHolder'
    _ ≤ 1 / 2 := by
      exact (mul_le_mul hFpow hGpow
        (Real.rpow_nonneg (integral_nonneg_of_ae
          (ae_restrict_of_ae (ae_of_all _ fun x => sq_nonneg (g x)))) _)
        (Real.rpow_nonneg hgaussNonneg _)).trans hrootProd

end PDE.Parabolic.Cauchy.OnDiag
