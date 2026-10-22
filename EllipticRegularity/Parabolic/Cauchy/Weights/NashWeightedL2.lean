module

public import EllipticRegularity.Parabolic.Cauchy.Weights.NashMoment
public import EllipticRegularity.Parabolic.Cauchy.Weights.TruncatedDistance
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Truncated Gaussian weighted `L²` estimate

This combines the time moment with the smooth weighted energy inequality,
removes the time shift by dominated convergence, and keeps the spatial
truncation fixed.
-/

@[expose] public section

namespace PDE.Parabolic.Cauchy.Weights

open MeasureTheory Set Filter Topology

variable {d : ℕ}

/-- The dimension-only factor in the limiting weighted `L²` estimate. -/
noncomputable def nashWeightedL2Constant (d : ℕ) : ℝ :=
  (((d : ℝ) + 2) / 2) * 2 ^ ((d : ℝ) / 2) * nashDiagonalSmoothingConstant d

theorem nashWeightedL2Constant_pos {d : ℕ} (hd : 0 < d) :
    0 < nashWeightedL2Constant d := by
  unfold nashWeightedL2Constant
  positivity [nashDiagonalSmoothingConstant_pos hd]

private theorem nash_truncated_weightedEndpoint_shift_bound {Lam s H A σ B : ℝ}
    {K : Set (Vec d)} (hK : K.Nonempty) (hd : 0 < d) (hH : 0 < H)
    (hLam : 1 ≤ Lam) (hA : Lam < A) (hσ : 0 < σ) (hσH : σ < H)
    {a : ParCoeffField d} {f : Vec d → ℝ}
    (ha : IsParabolicCoeff 1 Lam a univ (Icc s (s + H)))
    (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume)
    (hB : 0 < B) (hBf : ∫ x : Vec d, |f x| ≤ B)
    (hfsupp : ∀ᵐ x : Vec d ∂volume, x ∉ K → f x = 0)
    {u : ParH1Function (univ : Set (Vec d)) (Icc s (s + H))}
    (hu : IsCauchySolution a s (s + H) f u) {R : ℝ} (hR : 0 ≤ R) :
    ∫ x : Vec d,
      Real.exp (truncatedEuclideanSetDistance K R x ^ 2 / (2 * A * (H + σ))) *
        u.toFun (x, s + H) ^ 2 ≤
      (σ ^ (((d : ℝ) + 2) / 2) * (∫ x : Vec d, f x ^ 2) +
        (((d : ℝ) + 2) / 2) *
          Real.exp ((((d : ℝ) + 2) / 2) / (1 - Lam / A)) *
            ((2 * σ) ^ ((d : ℝ) / 2) * (∫ x : Vec d, f x ^ 2) * σ +
              2 ^ ((d : ℝ) / 2) * nashDiagonalSmoothingConstant d * B ^ 2 * (H - σ))) /
        H ^ (((d : ℝ) + 2) / 2) := by
  let κ : ℝ := ((d : ℝ) + 2) / 2
  let p : ℝ := (d : ℝ) / 2
  have hκp : κ - 1 = p := by dsimp [κ, p]; ring
  have hMoment := cauchy_nash_timeMoment_bound (d := d) s hd hH hσ hσH
    hLam hB ha hf1 hf2 hBf hu
  have hMomentInt : IntegrableOn
      (fun z : Vec d × ℝ =>
        (nashPositiveTimeShift σ (z.2 - s)) ^ (κ - 1) * u.toFun z ^ 2)
      ((univ : Set (Vec d)) ×ˢ Ioc s (s + H)) := by
    simpa [κ, p, hκp] using hMoment.1
  have hMomentBound : ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s (s + H),
      (nashPositiveTimeShift σ (z.2 - s)) ^ (κ - 1) * u.toFun z ^ 2 ≤
      (2 * σ) ^ p * (∫ x : Vec d, f x ^ 2) * σ +
        2 ^ p * nashDiagonalSmoothingConstant d * B ^ 2 * (H - σ) := by
    simpa [κ, p, hκp, mul_assoc] using hMoment.2
  have hendpoint := nashTruncatedDistance_weightedEndpoint_bound
    (d := d) hK hH hLam hR hA hσ ha f hf1 hf2 hfsupp u hu hMomentInt hMomentBound
  have hδ : 0 < 1 - Lam / A := by
    have hratio : Lam / A < 1 := (div_lt_one₀ (by linarith)).2 hA
    linarith
  have hexp : 2 * (κ / (2 * (1 - Lam / A))) = κ / (1 - Lam / A) := by
    field_simp [ne_of_gt hδ]
  have hendpoint' : (H + σ) ^ κ *
      ∫ x : Vec d,
        Real.exp (truncatedEuclideanSetDistance K R x ^ 2 / (2 * A * (H + σ))) *
          u.toFun (x, s + H) ^ 2 ≤
      σ ^ κ * (∫ x : Vec d, f x ^ 2) +
        κ * Real.exp (κ / (1 - Lam / A)) *
          ((2 * σ) ^ p * (∫ x : Vec d, f x ^ 2) * σ +
            2 ^ p * nashDiagonalSmoothingConstant d * B ^ 2 * (H - σ)) := by
    rw [show (H + σ) ^ κ = (H + σ) ^ (((d : ℝ) + 2) / 2) by rfl,
      show κ = ((d : ℝ) + 2) / 2 by rfl]
    rw [show 2 * ((((d : ℝ) + 2) / 2) /
        (2 * (1 - Lam / A))) =
        (((d : ℝ) + 2) / 2) / (1 - Lam / A) by
          field_simp [ne_of_gt hδ]] at hendpoint
    simpa [κ, p, mul_assoc] using hendpoint
  have hI0 : 0 ≤ ∫ x : Vec d,
      Real.exp (truncatedEuclideanSetDistance K R x ^ 2 / (2 * A * (H + σ))) *
        u.toFun (x, s + H) ^ 2 := by
    apply integral_nonneg_of_ae
    exact ae_of_all _ fun x => mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)
  have hpowmono : H ^ κ ≤ (H + σ) ^ κ := by
    apply Real.rpow_le_rpow (by linarith) (by linarith) (by dsimp [κ]; positivity)
  have hmul := mul_le_mul_of_nonneg_right hpowmono hI0
  have hscaled : H ^ κ *
      ∫ x : Vec d,
        Real.exp (truncatedEuclideanSetDistance K R x ^ 2 / (2 * A * (H + σ))) *
          u.toFun (x, s + H) ^ 2 ≤
      σ ^ κ * (∫ x : Vec d, f x ^ 2) +
        κ * Real.exp (κ / (1 - Lam / A)) *
          ((2 * σ) ^ p * (∫ x : Vec d, f x ^ 2) * σ +
            2 ^ p * nashDiagonalSmoothingConstant d * B ^ 2 * (H - σ)) :=
    hmul.trans hendpoint'
  have hHpow : 0 < H ^ κ := Real.rpow_pos_of_pos hH κ
  apply (le_div_iff₀ hHpow).2
  simpa only [mul_comm] using hscaled

/-- Gaussian weighted `L²` estimate for distance to the initial support.
The prefactor depends only on the dimension; the coefficient dependence is
entirely in the exponential loss. -/
theorem cauchy_nash_truncated_weighted_l2 {Lam s H A B : ℝ}
    {K : Set (Vec d)} (hK : K.Nonempty) (hd : 0 < d) (hH : 0 < H)
    (hLam : 1 ≤ Lam) (hA : Lam < A) (hB : 0 < B)
    {a : ParCoeffField d} {f : Vec d → ℝ}
    (ha : IsParabolicCoeff 1 Lam a univ (Icc s (s + H)))
    (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume)
    (hBf : ∫ x : Vec d, |f x| ≤ B)
    (hfsupp : ∀ᵐ x : Vec d ∂volume, x ∉ K → f x = 0)
    {u : ParH1Function (univ : Set (Vec d)) (Icc s (s + H))}
    (hu : IsCauchySolution a s (s + H) f u) {R : ℝ} (hR : 0 ≤ R) :
    ∫ x : Vec d,
      Real.exp (truncatedEuclideanSetDistance K R x ^ 2 / (2 * A * H)) *
        u.toFun (x, s + H) ^ 2 ≤
      nashWeightedL2Constant d *
        Real.exp ((((d : ℝ) + 2) / 2) / (1 - Lam / A)) *
          H ^ (-(d : ℝ) / 2) * B ^ 2 := by
  let κ : ℝ := ((d : ℝ) + 2) / 2
  let p : ℝ := (d : ℝ) / 2
  let σseq : ℕ → ℝ := fun n => H / ((n : ℝ) + 2)
  let F : ℕ → Vec d → ℝ := fun n x =>
    Real.exp (truncatedEuclideanSetDistance K R x ^ 2 /
      (2 * A * (H + σseq n))) * u.toFun (x, s + H) ^ 2
  let G : Vec d → ℝ := fun x =>
    Real.exp (truncatedEuclideanSetDistance K R x ^ 2 / (2 * A * H)) *
      u.toFun (x, s + H) ^ 2
  let weightBound : ℝ := Real.exp (R ^ 2 / (2 * A * H))
  let rhs : ℝ → ℝ := fun q =>
    (q ^ κ * (∫ x : Vec d, f x ^ 2) +
      κ * Real.exp (κ / (1 - Lam / A)) *
        ((2 * q) ^ p * (∫ x : Vec d, f x ^ 2) * q +
          2 ^ p * nashDiagonalSmoothingConstant d * B ^ 2 * (H - q))) / H ^ κ
  have hApos : 0 < A := by linarith [hLam]
  have hden : 0 < 2 * A * H := by positivity
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hp : 0 < p := by dsimp [p]; linarith
  have hσseq : Tendsto σseq atTop (𝓝 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat H).comp
      (tendsto_add_atTop_nat 2)
    have h' : Tendsto (fun n : ℕ => H / ((n + 2 : ℕ) : ℝ)) atTop (𝓝 0) := by
      change Tendsto ((fun n : ℕ => H / (n : ℝ)) ∘ (fun n => n + 2))
        atTop (𝓝 0)
      exact h
    have heq : σseq = fun n : ℕ => H / ((n + 2 : ℕ) : ℝ) := by
      funext n
      simp [σseq]
    rw [heq]
    exact h'
  have hσbounds (n : ℕ) : 0 < σseq n ∧ σseq n < H := by
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hn : 1 < (n : ℝ) + 2 := by linarith
    constructor
    · dsimp [σseq]
      exact div_pos hH (by positivity)
    · dsimp [σseq]
      exact (div_lt_iff₀ (by linarith)).2 (by nlinarith [hH, hn])
  have hUend : Integrable (fun x : Vec d => u.toFun (x, s + H) ^ 2) volume :=
    PDE.Parabolic.Cauchy.Energy.cauchy_slice_square_integrable
      (by linarith [hH]) ha f hf2 u hu ⟨by linarith [hH], le_rfl⟩
  have hρcont : Continuous (truncatedEuclideanSetDistance K R) :=
    (truncatedEuclideanSetDistance_eucLip hK).continuous (by norm_num)
  have hFmeas : ∀ n, AEStronglyMeasurable (F n) volume := by
    intro n
    have hweight : Continuous (fun x : Vec d =>
        Real.exp (truncatedEuclideanSetDistance K R x ^ 2 /
          (2 * A * (H + σseq n)))) := by
      fun_prop
    exact hweight.aestronglyMeasurable.mul hUend.aestronglyMeasurable
  have hdomInt : Integrable
      (fun x : Vec d => weightBound * u.toFun (x, s + H) ^ 2) volume := by
    exact hUend.const_mul weightBound
  have hFbound : ∀ n, ∀ᵐ x ∂volume, ‖F n x‖ ≤
      weightBound * u.toFun (x, s + H) ^ 2 := by
    intro n
    filter_upwards [] with x
    have hρ0 := truncatedEuclideanSetDistance_nonneg hK hR x
    have hρR := truncatedEuclideanSetDistance_le (K := K) (R := R) x
    have hρsq : truncatedEuclideanSetDistance K R x ^ 2 ≤ R ^ 2 := by
      nlinarith [sq_nonneg (truncatedEuclideanSetDistance K R x - R)]
    have hσ := hσbounds n
    have hdenle : 2 * A * H ≤ 2 * A * (H + σseq n) := by
      nlinarith [hApos, hH, hσ.1]
    have hquot : truncatedEuclideanSetDistance K R x ^ 2 /
        (2 * A * (H + σseq n)) ≤ R ^ 2 / (2 * A * H) := by
      calc
        _ ≤ R ^ 2 / (2 * A * (H + σseq n)) :=
          div_le_div_of_nonneg_right hρsq (by positivity)
        _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg R) hden hdenle
    have hexp : Real.exp (truncatedEuclideanSetDistance K R x ^ 2 /
        (2 * A * (H + σseq n))) ≤ weightBound := by
      dsimp [weightBound]
      exact Real.exp_le_exp.mpr hquot
    have hweightNonneg := Real.exp_nonneg
      (truncatedEuclideanSetDistance K R x ^ 2 / (2 * A * (H + σseq n)))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hweightNonneg,
      abs_of_nonneg (sq_nonneg (u.toFun (x, s + H)))]
    exact mul_le_mul_of_nonneg_right hexp (sq_nonneg _)
  have hFlim : ∀ᵐ x ∂volume, Tendsto (fun n => F n x) atTop (𝓝 (G x)) := by
    filter_upwards [] with x
    have hdenCont : ContinuousAt (fun q : ℝ => 2 * A * (H + q)) 0 := by fun_prop
    have hden0 : 2 * A * (H + 0) ≠ 0 := by simpa using ne_of_gt hden
    have hargCont : ContinuousAt (fun q : ℝ =>
        truncatedEuclideanSetDistance K R x ^ 2 / (2 * A * (H + q))) 0 :=
      continuousAt_const.div hdenCont hden0
    have hexpCont : ContinuousAt (fun q : ℝ =>
        Real.exp (truncatedEuclideanSetDistance K R x ^ 2 / (2 * A * (H + q)))) 0 :=
      Real.continuous_exp.continuousAt.comp hargCont
    have hlim := hexpCont.tendsto.comp hσseq
    have hlim' : Tendsto (fun n : ℕ =>
        Real.exp (truncatedEuclideanSetDistance K R x ^ 2 /
          (2 * A * (H + σseq n)))) atTop
        (𝓝 (Real.exp (truncatedEuclideanSetDistance K R x ^ 2 / (2 * A * H)))) := by
      change Tendsto ((fun q : ℝ =>
        Real.exp (truncatedEuclideanSetDistance K R x ^ 2 / (2 * A * (H + q)))) ∘
          σseq) atTop _
      simpa using hlim
    exact hlim'.mul_const (u.toFun (x, s + H) ^ 2)
  have hIntLim : Tendsto (fun n => ∫ x : Vec d, F n x) atTop
      (𝓝 (∫ x : Vec d, G x)) :=
    tendsto_integral_of_dominated_convergence
      (fun x : Vec d => weightBound * u.toFun (x, s + H) ^ 2)
      hFmeas hdomInt hFbound hFlim
  have hpowκ : Continuous (fun q : ℝ => q ^ κ) :=
    Real.continuous_rpow_const hκ.le
  have hpowp : Continuous (fun q : ℝ => (2 * q) ^ p) :=
    (Real.continuous_rpow_const hp.le).comp (continuous_const.mul continuous_id)
  have hinner : Continuous (fun q : ℝ =>
      (2 * q) ^ p * (∫ x : Vec d, f x ^ 2) * q +
        2 ^ p * nashDiagonalSmoothingConstant d * B ^ 2 * (H - q)) := by
    exact ((hpowp.mul continuous_const).mul continuous_id).add
      (continuous_const.mul (continuous_const.sub continuous_id))
  have hnum : Continuous (fun q : ℝ =>
      q ^ κ * (∫ x : Vec d, f x ^ 2) +
        κ * Real.exp (κ / (1 - Lam / A)) *
          ((2 * q) ^ p * (∫ x : Vec d, f x ^ 2) * q +
            2 ^ p * nashDiagonalSmoothingConstant d * B ^ 2 * (H - q))) := by
    exact (hpowκ.mul continuous_const).add
      (continuous_const.mul hinner)
  have hrhsCont : Continuous rhs := by
    change Continuous (fun q : ℝ =>
      (q ^ κ * (∫ x : Vec d, f x ^ 2) +
        κ * Real.exp (κ / (1 - Lam / A)) *
          ((2 * q) ^ p * (∫ x : Vec d, f x ^ 2) * q +
            2 ^ p * nashDiagonalSmoothingConstant d * B ^ 2 * (H - q))) *
          (H ^ κ)⁻¹)
    exact hnum.mul continuous_const
  have hrhsLim : Tendsto (fun n => rhs (σseq n)) atTop (𝓝 (rhs 0)) :=
    hrhsCont.continuousAt.tendsto.comp hσseq
  have hseqBound : ∀ n, (∫ x : Vec d, F n x) ≤ rhs (σseq n) := by
    intro n
    exact nash_truncated_weightedEndpoint_shift_bound hK hd hH hLam hA
      (hσbounds n).1 (hσbounds n).2 ha hf1 hf2 hB hBf hfsupp hu hR
  have hlimBound := le_of_tendsto_of_tendsto hIntLim hrhsLim
    (Eventually.of_forall hseqBound)
  have hκpos : 0 < κ := hκ
  have hppos : 0 < p := hp
  have hratio : H / H ^ κ = H ^ (-(d : ℝ) / 2) := by
    calc
      H / H ^ κ = H ^ (1 : ℝ) / H ^ κ := by rw [Real.rpow_one]
      _ = H ^ (1 : ℝ) * H ^ (-κ) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hH) κ]
      _ = H ^ (1 + -κ) := by rw [← Real.rpow_add hH]
      _ = H ^ (-(d : ℝ) / 2) := by congr 1; dsimp [κ]; ring
  have hrhs0 : rhs 0 = nashWeightedL2Constant d *
      Real.exp ((((d : ℝ) + 2) / 2) / (1 - Lam / A)) *
        H ^ (-(d : ℝ) / 2) * B ^ 2 := by
    have hnum0 : rhs 0 =
        (κ * Real.exp (κ / (1 - Lam / A)) *
          (2 ^ p * nashDiagonalSmoothingConstant d * B ^ 2 * H)) / H ^ κ := by
      simp [rhs, Real.zero_rpow hκpos.ne', Real.zero_rpow hppos.ne']
    have hratio' : H * (H ^ κ)⁻¹ = H ^ (-(d : ℝ) / 2) := by
      rw [← div_eq_mul_inv]
      exact hratio
    rw [hnum0, div_eq_mul_inv]
    calc
      κ * Real.exp (κ / (1 - Lam / A)) *
          (2 ^ p * nashDiagonalSmoothingConstant d * B ^ 2 * H) * (H ^ κ)⁻¹ =
        κ * 2 ^ p * nashDiagonalSmoothingConstant d *
          Real.exp (κ / (1 - Lam / A)) * B ^ 2 *
            (H * (H ^ κ)⁻¹) := by ring
      _ = nashWeightedL2Constant d *
          Real.exp ((((d : ℝ) + 2) / 2) / (1 - Lam / A)) *
            H ^ (-(d : ℝ) / 2) * B ^ 2 := by
        rw [hratio']
        dsimp [nashWeightedL2Constant, κ, p]
        ring
  have hgoal : (∫ x : Vec d, G x) ≤
      nashWeightedL2Constant d *
        Real.exp ((((d : ℝ) + 2) / 2) / (1 - Lam / A)) *
          H ^ (-(d : ℝ) / 2) * B ^ 2 := by
    rw [← hrhs0]
    exact hlimBound
  simpa [G] using hgoal

end PDE.Parabolic.Cauchy.Weights
