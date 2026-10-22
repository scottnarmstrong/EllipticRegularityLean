module

public import EllipticRegularity.Parabolic.Cauchy.Energy.GlobalIdentity
public import EllipticRegularity.Parabolic.Cauchy.Energy.InitialTrace
public import EllipticRegularity.Parabolic.Energy.Bridge
public import EllipticRegularity.Parabolic.Caccioppoli.Assembly
public import EllipticRegularity.Parabolic.Chain.ScaleLimit
public import EllipticRegularity.Parabolic.Chain.H1Solution
public import PDEFoundation.Sobolev.W1p.Truncation
public import EllipticRegularity.Ch4.GreenDecay.Helpers
public import Mathlib.Analysis.Calculus.MeanValue

/-! # Smooth negative-energy profile for Cauchy positivity -/

@[expose] public section

namespace PDE.Parabolic.Cauchy.Energy

open MeasureTheory Set Filter Topology intervalIntegral

noncomputable def cauchyNegativeSource (ε : ℝ) (x : ℝ) : ℝ :=
  PDE.smoothPositivePartStep (-3 * ε / 2) (ε / 8) x *
    (1 - PDE.smoothPositivePartStep (-ε) (ε / 8) x)

theorem cauchyNegativeSource_contDiff (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (cauchyNegativeSource ε) := by
  unfold cauchyNegativeSource
  have hδ : ε / 8 ≠ 0 := ne_of_gt (by positivity)
  exact (PDE.smoothPositivePartStep_contDiff _ _).mul
    (contDiff_const.sub (PDE.smoothPositivePartStep_contDiff _ _))

noncomputable def cauchyNegativeFirstIntegral (ε : ℝ) (x : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..x, cauchyNegativeSource ε r

noncomputable def cauchyNegativeEnergy (ε : ℝ) (x : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..x, cauchyNegativeFirstIntegral ε r

theorem cauchyNegativeFirstIntegral_hasDerivAt (ε : ℝ) (hε : 0 < ε)
    (x : ℝ) : HasDerivAt (cauchyNegativeFirstIntegral ε)
      (cauchyNegativeSource ε x) x := by
  unfold cauchyNegativeFirstIntegral
  exact intervalIntegral.integral_hasDerivAt_right
    ((cauchyNegativeSource_contDiff ε hε).continuous.intervalIntegrable 0 x)
    ((cauchyNegativeSource_contDiff ε hε).continuous.stronglyMeasurableAtFilter volume (nhds x))
    ((cauchyNegativeSource_contDiff ε hε).continuous.continuousAt)

theorem cauchyNegativeFirstIntegral_deriv (ε : ℝ) (hε : 0 < ε) :
    deriv (cauchyNegativeFirstIntegral ε) = cauchyNegativeSource ε := by
  funext x
  exact (cauchyNegativeFirstIntegral_hasDerivAt ε hε x).deriv

theorem cauchyNegativeFirstIntegral_contDiff (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (cauchyNegativeFirstIntegral ε) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨differentiable_integral_of_continuous
      (cauchyNegativeSource_contDiff ε hε).continuous, ?_⟩
  rw [cauchyNegativeFirstIntegral_deriv ε hε]
  exact cauchyNegativeSource_contDiff ε hε

theorem cauchyNegativeEnergy_hasDerivAt (ε : ℝ) (hε : 0 < ε)
    (x : ℝ) : HasDerivAt (cauchyNegativeEnergy ε)
      (cauchyNegativeFirstIntegral ε x) x := by
  unfold cauchyNegativeEnergy
  exact intervalIntegral.integral_hasDerivAt_right
    ((cauchyNegativeFirstIntegral_contDiff ε hε).continuous.intervalIntegrable 0 x)
    ((cauchyNegativeFirstIntegral_contDiff ε hε).continuous.stronglyMeasurableAtFilter volume
      (nhds x))
    ((cauchyNegativeFirstIntegral_contDiff ε hε).continuous.continuousAt)

theorem cauchyNegativeEnergy_deriv (ε : ℝ) (hε : 0 < ε) :
    deriv (cauchyNegativeEnergy ε) = cauchyNegativeFirstIntegral ε := by
  funext x
  exact (cauchyNegativeEnergy_hasDerivAt ε hε x).deriv

theorem cauchyNegativeEnergy_contDiff (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (cauchyNegativeEnergy ε) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨differentiable_integral_of_continuous
      (cauchyNegativeFirstIntegral_contDiff ε hε).continuous, ?_⟩
  rw [cauchyNegativeEnergy_deriv ε hε]
  exact cauchyNegativeFirstIntegral_contDiff ε hε

theorem cauchyNegativeSource_nonneg (ε : ℝ) (_hε : 0 < ε) (x : ℝ) :
    0 ≤ cauchyNegativeSource ε x := by
  unfold cauchyNegativeSource
  apply mul_nonneg
  · exact PDE.smoothPositivePartStep_nonneg _ _ _
  · linarith [PDE.smoothPositivePartStep_le_one (-ε) (ε / 8) x]

theorem cauchyNegativeSource_le_one (ε : ℝ) (_hε : 0 < ε) (x : ℝ) :
    cauchyNegativeSource ε x ≤ 1 := by
  unfold cauchyNegativeSource
  have h₁ := PDE.smoothPositivePartStep_nonneg (-ε) (ε / 8) x
  have h₂ := PDE.smoothPositivePartStep_le_one (-ε) (ε / 8) x
  have h₃ := PDE.smoothPositivePartStep_le_one (-3 * ε / 2) (ε / 8) x
  have h₄ := PDE.smoothPositivePartStep_nonneg (-3 * ε / 2) (ε / 8) x
  nlinarith [mul_le_mul_of_nonneg_right h₃ (show 0 ≤ 1 -
    PDE.smoothPositivePartStep (-ε) (ε / 8) x by linarith)]

theorem cauchyNegativeSource_zero_of_le (ε : ℝ) (hε : 0 < ε)
    {x : ℝ} (hx : x ≤ -2 * ε) : cauchyNegativeSource ε x = 0 := by
  unfold cauchyNegativeSource
  rw [PDE.smoothPositivePartStep_eq_zero (by positivity) (by nlinarith)]
  simp

theorem cauchyNegativeSource_zero_of_nonneg (ε : ℝ) (hε : 0 < ε)
    {x : ℝ} (hx : 0 ≤ x) : cauchyNegativeSource ε x = 0 := by
  unfold cauchyNegativeSource
  have hone : PDE.smoothPositivePartStep (-ε) (ε / 8) x = 1 :=
    PDE.smoothPositivePartStep_eq_one (c := -ε) (δ := ε / 8) (t := x)
      (by positivity) (by nlinarith)
  simp [hone]

theorem cauchyNegativeSource_eq_one (ε : ℝ) (hε : 0 < ε)
    {x : ℝ} (hx₁ : -5 * ε / 4 ≤ x) (hx₂ : x ≤ -7 * ε / 8) :
    cauchyNegativeSource ε x = 1 := by
  unfold cauchyNegativeSource
  rw [PDE.smoothPositivePartStep_eq_one (c := -3 * ε / 2) (δ := ε / 8) (t := x)
      (by positivity) (by nlinarith),
    PDE.smoothPositivePartStep_eq_zero (c := -ε) (δ := ε / 8) (t := x)
      (by positivity) (by nlinarith)]
  norm_num

theorem cauchyNegativeFirstIntegral_eq_zero_of_nonneg (ε : ℝ) (hε : 0 < ε)
    {x : ℝ} (hx : 0 ≤ x) : cauchyNegativeFirstIntegral ε x = 0 := by
  unfold cauchyNegativeFirstIntegral
  rw [intervalIntegral.integral_congr]
  · exact intervalIntegral.integral_zero
  · intro y hy
    have hy' : y ∈ Icc (0 : ℝ) x := by simpa [uIcc_of_le hx] using hy
    have hy0 : 0 ≤ y := hy'.1
    exact cauchyNegativeSource_zero_of_nonneg ε hε hy0

theorem cauchyNegativeFirstIntegral_nonpos (ε : ℝ) (hε : 0 < ε)
    {x : ℝ} (hx : x ≤ 0) : cauchyNegativeFirstIntegral ε x ≤ 0 := by
  rw [cauchyNegativeFirstIntegral, intervalIntegral.integral_symm]
  have hnonneg : 0 ≤ ∫ r in x..0, cauchyNegativeSource ε r :=
    intervalIntegral.integral_nonneg hx (fun r hr => cauchyNegativeSource_nonneg ε hε r)
  exact neg_nonpos.mpr hnonneg

theorem cauchyNegativeEnergy_nonneg (ε : ℝ) (hε : 0 < ε) (x : ℝ) :
    0 ≤ cauchyNegativeEnergy ε x := by
  by_cases hx : x ≤ 0
  · rw [cauchyNegativeEnergy, intervalIntegral.integral_symm]
    have hnonneg : 0 ≤ ∫ r in x..0, -cauchyNegativeFirstIntegral ε r :=
      intervalIntegral.integral_nonneg hx (fun r hr =>
      neg_nonneg.mpr (cauchyNegativeFirstIntegral_nonpos ε hε hr.2))
    simpa only [intervalIntegral.integral_neg] using hnonneg
  · have hx' : 0 ≤ x := le_of_not_ge hx
    rw [cauchyNegativeEnergy]
    rw [intervalIntegral.integral_congr]
    · rw [intervalIntegral.integral_zero]
    · intro r hr
      have hr' : r ∈ Icc (0 : ℝ) x := by simpa [uIcc_of_le hx'] using hr
      have hr0 : 0 ≤ r := hr'.1
      exact cauchyNegativeFirstIntegral_eq_zero_of_nonneg ε hε hr0

theorem cauchyNegativeEnergy_zero_of_nonneg (ε : ℝ) (hε : 0 < ε)
    {x : ℝ} (hx : 0 ≤ x) : cauchyNegativeEnergy ε x = 0 := by
  rw [cauchyNegativeEnergy]
  rw [intervalIntegral.integral_congr]
  · exact intervalIntegral.integral_zero
  · intro r hr
    have hr' : r ∈ Icc (0 : ℝ) x := by simpa [uIcc_of_le hx] using hr
    have hr0 : 0 ≤ r := hr'.1
    exact cauchyNegativeFirstIntegral_eq_zero_of_nonneg ε hε hr0

theorem cauchyNegativeFirstIntegral_neg (ε : ℝ) (hε : 0 < ε) :
    cauchyNegativeFirstIntegral ε (-3 * ε / 2) < 0 := by
  rw [cauchyNegativeFirstIntegral, intervalIntegral.integral_symm]
  have hpos : 0 < ∫ r in (-3 * ε / 2)..0, cauchyNegativeSource ε r := by
    apply intervalIntegral.integral_pos (by nlinarith [hε])
      (cauchyNegativeSource_contDiff ε hε).continuous.continuousOn
    · intro r hr
      exact cauchyNegativeSource_nonneg ε hε r
    · refine ⟨-ε, ?_, ?_⟩
      · constructor <;> nlinarith [hε]
      · have hval : cauchyNegativeSource ε (-ε) = 1 := by
          apply cauchyNegativeSource_eq_one ε hε <;> nlinarith [hε]
        rw [hval]
        norm_num
  linarith

theorem cauchyNegativeEnergy_pos_of_le (ε : ℝ) (hε : 0 < ε)
    {x : ℝ} (hx : x ≤ -2 * ε) : 0 < cauchyNegativeEnergy ε x := by
  rw [cauchyNegativeEnergy, intervalIntegral.integral_symm]
  have hpos : 0 < ∫ r in x..0, -cauchyNegativeFirstIntegral ε r := by
    apply intervalIntegral.integral_pos (by linarith [hx, hε])
      ((cauchyNegativeFirstIntegral_contDiff ε hε).continuous.neg.continuousOn)
    · intro r hr
      exact neg_nonneg.mpr (cauchyNegativeFirstIntegral_nonpos ε hε hr.2)
    · refine ⟨-3 * ε / 2, ⟨by linarith [hx, hε], by linarith [hε]⟩, ?_⟩
      simpa using neg_pos.mpr (cauchyNegativeFirstIntegral_neg ε hε)
  simpa only [intervalIntegral.integral_neg] using hpos

theorem cauchyNegativeFirstIntegral_lipschitz (ε : ℝ) (hε : 0 < ε) :
    LipschitzWith 1 (cauchyNegativeFirstIntegral ε) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    ((cauchyNegativeFirstIntegral_contDiff ε hε).differentiable (by norm_num))
  intro x
  rw [cauchyNegativeFirstIntegral_deriv ε hε]
  have habs : |cauchyNegativeSource ε x| ≤ 1 := by
    rw [abs_of_nonneg (cauchyNegativeSource_nonneg ε hε x)]
    exact cauchyNegativeSource_le_one ε hε x
  exact_mod_cast habs

theorem cauchyNegativeFirstIntegral_abs_le_abs (ε : ℝ) (hε : 0 < ε)
    (x : ℝ) : |cauchyNegativeFirstIntegral ε x| ≤ |x| := by
  have h := (cauchyNegativeFirstIntegral_lipschitz ε hε).dist_le_mul x 0
  simpa [dist_eq_norm, Real.norm_eq_abs,
    cauchyNegativeFirstIntegral_eq_zero_of_nonneg ε hε (le_rfl)] using h

theorem cauchyNegativeFirstIntegral_eq_of_le (ε : ℝ) (hε : 0 < ε)
    {x : ℝ} (hx : x ≤ -2 * ε) :
    cauchyNegativeFirstIntegral ε x = cauchyNegativeFirstIntegral ε (-2 * ε) := by
  have hBcont : Continuous (cauchyNegativeSource ε) :=
    (cauchyNegativeSource_contDiff ε hε).continuous
  have h01 : IntervalIntegrable (cauchyNegativeSource ε) volume 0 (-2 * ε) :=
    hBcont.intervalIntegrable 0 (-2 * ε)
  have h12 : IntervalIntegrable (cauchyNegativeSource ε) volume (-2 * ε) x :=
    hBcont.intervalIntegrable (-2 * ε) x
  have hzero : ∫ r in (-2 * ε)..x, cauchyNegativeSource ε r = 0 := by
    rw [intervalIntegral.integral_congr]
    · exact intervalIntegral.integral_zero
    · intro r hr
      rw [uIcc_of_ge hx] at hr
      exact cauchyNegativeSource_zero_of_le ε hε hr.2
  have hadd := intervalIntegral.integral_add_adjacent_intervals h01 h12
  unfold cauchyNegativeFirstIntegral
  calc
    (∫ r in (0 : ℝ)..x, cauchyNegativeSource ε r) =
        (∫ r in (0 : ℝ)..(-2 * ε), cauchyNegativeSource ε r) +
          ∫ r in (-2 * ε)..x, cauchyNegativeSource ε r := hadd.symm
    _ = ∫ r in (0 : ℝ)..(-2 * ε), cauchyNegativeSource ε r := by rw [hzero, add_zero]

theorem cauchyNegativeFirstIntegral_abs_le_two_mul (ε : ℝ) (hε : 0 < ε)
    (x : ℝ) : |cauchyNegativeFirstIntegral ε x| ≤ 2 * ε := by
  by_cases hx₀ : 0 ≤ x
  · rw [cauchyNegativeFirstIntegral_eq_zero_of_nonneg ε hε hx₀]
    rw [abs_zero]
    exact mul_nonneg (by norm_num) hε.le
  · have hx₀' : x < 0 := lt_of_not_ge hx₀
    by_cases hx₂ : x ≤ -2 * ε
    · rw [cauchyNegativeFirstIntegral_eq_of_le ε hε hx₂]
      have h := cauchyNegativeFirstIntegral_abs_le_abs ε hε (-2 * ε)
      have habs : |(-2 : ℝ) * ε| = 2 * ε := by
        rw [abs_of_neg (by nlinarith [hε])]
        ring_nf
      rw [habs] at h
      exact h
    · have hx₂' : -2 * ε < x := lt_of_not_ge hx₂
      have h := cauchyNegativeFirstIntegral_abs_le_abs ε hε x
      rw [abs_of_neg hx₀'] at h
      linarith

theorem cauchyNegativeEnergy_secondDeriv (ε : ℝ) (hε : 0 < ε) :
    deriv (deriv (cauchyNegativeEnergy ε)) = cauchyNegativeSource ε := by
  rw [cauchyNegativeEnergy_deriv ε hε, cauchyNegativeFirstIntegral_deriv ε hε]

theorem cauchyNegativeEnergy_lipschitz (ε : ℝ) (hε : 0 < ε) :
    ∃ C : NNReal, LipschitzWith C (cauchyNegativeEnergy ε) := by
  refine ⟨⟨2 * ε, by positivity⟩, ?_⟩
  apply lipschitzWith_of_nnnorm_deriv_le
    ((cauchyNegativeEnergy_contDiff ε hε).differentiable (by norm_num))
  intro x
  rw [cauchyNegativeEnergy_deriv ε hε]
  have habs : |cauchyNegativeFirstIntegral ε x| ≤ 2 * ε :=
    cauchyNegativeFirstIntegral_abs_le_two_mul ε hε x
  exact_mod_cast habs

theorem cauchyNegativeEnergy_deriv_abs_le (ε : ℝ) (hε : 0 < ε)
    (x : ℝ) : |deriv (cauchyNegativeEnergy ε) x| ≤ 2 * ε := by
  rw [cauchyNegativeEnergy_deriv ε hε]
  exact cauchyNegativeFirstIntegral_abs_le_two_mul ε hε x

theorem cauchyNegativeEnergy_secondDeriv_abs_le (ε : ℝ) (hε : 0 < ε)
    (x : ℝ) : |deriv (deriv (cauchyNegativeEnergy ε)) x| ≤ 1 := by
  rw [cauchyNegativeEnergy_secondDeriv ε hε]
  rw [abs_of_nonneg (cauchyNegativeSource_nonneg ε hε x)]
  exact cauchyNegativeSource_le_one ε hε x

theorem intervalIntegral_neg_id_sq (x : ℝ) :
    ∫ r in x..0, -r = x ^ 2 / 2 := by
  have hderiv : ∀ r ∈ uIcc x 0,
      HasDerivAt (fun y : ℝ => -(y ^ 2) / 2) (-r) r := by
    intro r hr
    have h := ((hasDerivAt_id r).pow 2).const_mul (-1 / 2)
    convert h using 1 <;> simp [Function.id_def] <;> ring_nf
  have hcont : IntervalIntegrable (fun r : ℝ => -r) volume x 0 :=
    (continuous_id.neg).intervalIntegrable x 0
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont
  norm_num at h ⊢
  nlinarith [h]

theorem cauchyNegativeEnergy_sq_bound (ε : ℝ) (hε : 0 < ε)
    (x : ℝ) : cauchyNegativeEnergy ε x ≤ x ^ 2 / 2 := by
  by_cases hx : x ≤ 0
  · rw [cauchyNegativeEnergy, intervalIntegral.integral_symm,
      ← intervalIntegral.integral_neg]
    have hmono : ∫ r in x..0, -cauchyNegativeFirstIntegral ε r ≤
        ∫ r in x..0, -r := by
      apply intervalIntegral.integral_mono_on (a := x) (b := 0) hx
        ((cauchyNegativeFirstIntegral_contDiff ε hε).continuous.neg.intervalIntegrable x 0)
        (continuous_id.neg.intervalIntegrable x 0)
      intro r hr
      have hG := cauchyNegativeFirstIntegral_abs_le_abs ε hε r
      have hG0 := cauchyNegativeFirstIntegral_nonpos ε hε hr.2
      rw [abs_of_nonpos hG0, abs_of_nonpos hr.2] at hG
      exact hG
    calc
      (∫ r in x..0, -cauchyNegativeFirstIntegral ε r) ≤ ∫ r in x..0, -r := hmono
      _ = x ^ 2 / 2 := intervalIntegral_neg_id_sq x
  · have hx' : 0 ≤ x := le_of_not_ge hx
    rw [cauchyNegativeEnergy_zero_of_nonneg ε hε hx']
    positivity

theorem cauchyNegativeEnergy_sub_sq_bound (ε : ℝ) (hε : 0 < ε)
    {x y : ℝ} (hy : 0 ≤ y) :
    cauchyNegativeEnergy ε x ≤ (x - y) ^ 2 / 2 := by
  by_cases hx : 0 ≤ x
  · rw [cauchyNegativeEnergy_zero_of_nonneg ε hε hx]
    positivity
  · have hx' : x < 0 := lt_of_not_ge hx
    have hxy : x ^ 2 ≤ (x - y) ^ 2 := by
      have hprod : 0 ≤ (-x) * y := mul_nonneg (le_of_lt (neg_pos.mpr hx')) hy
      nlinarith [sq_nonneg y]
    calc
      cauchyNegativeEnergy ε x ≤ x ^ 2 / 2 := cauchyNegativeEnergy_sq_bound ε hε x
      _ ≤ (x - y) ^ 2 / 2 := by nlinarith

end PDE.Parabolic.Cauchy.Energy
