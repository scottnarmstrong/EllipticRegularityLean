module

public import EllipticRegularity.Parabolic.Cauchy.Weights.SmoothGaussianDensity
public import EllipticRegularity.Parabolic.Cauchy.Weights.SmoothEnergy
public import EllipticRegularity.Parabolic.Cauchy.Weights.TimePolynomial
public import EllipticRegularity.Parabolic.Chain.Calculus
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The Nash time power in the Gaussian weighted energy density

This module multiplies the smooth truncated-distance Gaussian by the bounded
time factor which agrees with `(t-s+σ)^((d+2)/4)` on the energy interval.
The derivative of that factor produces the exact threshold term in the
Nash--Aronson weighted-energy argument.
-/

@[expose] public section

namespace PDE.Parabolic.Cauchy.Weights

open MeasureTheory Set

variable {d : ℕ}

/-- The bounded smooth time factor as a space-time function. -/
noncomputable def nashPolynomialTimeSpacetime (H σ s : ℝ) (z : Vec d × ℝ) : ℝ :=
  nashPolynomialTimeFactor (d := d) H σ (z.2 - s)

/-- Product of the polynomial time factor and the mollified Gaussian. -/
noncomputable def nashPolynomialGaussianWeight (H : ℝ) (K : Set (Vec d))
    (R A σ s : ℝ) (n : ℕ) (z : Vec d × ℝ) : ℝ :=
  nashPolynomialTimeSpacetime (d := d) H σ s z *
    nashSmoothGaussianWeight K R A σ s n z

theorem nashPolynomialTimeSpacetime_contDiff_one {H σ s : ℝ}
    (hH : 0 < H) (hσ : 0 < σ) :
    ContDiff ℝ 1 (nashPolynomialTimeSpacetime (d := d) H σ s) := by
  change ContDiff ℝ 1
    ((nashPolynomialTimeFactor (d := d) H σ) ∘ fun z : Vec d × ℝ => z.2 - s)
  exact (nashPolynomialTimeFactor_contDiff_one (d := d) hH hσ).comp
    (contDiff_snd.sub contDiff_const)

theorem parTimeDeriv_nashPolynomialTimeSpacetime {H σ s : ℝ}
    (hH : 0 < H) (hσ : 0 < σ) {z : Vec d × ℝ}
    (hz₀ : s ≤ z.2) (hzH : z.2 ≤ s + H) :
    parTimeDeriv (nashPolynomialTimeSpacetime (d := d) H σ s) z =
      (((d : ℝ) + 2) / 4) *
        nashPositiveTimeShift σ (z.2 - s) ^ ((((d : ℝ) + 2) / 4) - 1) := by
  let w : Vec d × ℝ → ℝ := fun y => y.2 - s
  have hw : ContDiff ℝ 1 w := by
    dsimp [w]
    exact contDiff_snd.sub (contDiff_const : ContDiff ℝ 1 (fun _ : Vec d × ℝ => s))
  have hderivW : HasFDerivAt w (ContinuousLinearMap.snd ℝ (Vec d) ℝ) z := by
    dsimp [w]
    exact hasFDerivAt_snd.sub_const s
  have htime := PDE.Parabolic.Chain.parTimeDeriv_comp
    (nashPolynomialTimeFactor_contDiff_one (d := d) hH hσ) hw z
  change parTimeDeriv (nashPolynomialTimeFactor (d := d) H σ ∘ w) z = _ at htime
  change parTimeDeriv (nashPolynomialTimeFactor (d := d) H σ ∘ w) z = _
  rw [htime]
  simp only [w]
  have harg : 0 ≤ z.2 - s := sub_nonneg.mpr hz₀
  have hargH : z.2 - s ≤ H := by linarith
  have htimew : parTimeDeriv w z = 1 := by
    rw [parTimeDeriv, hderivW.fderiv]
    simp
  rw [deriv_nashPolynomialTimeFactor_eq_rpow hH hσ harg hargH]
  rw [htimew]
  ring

theorem parSpaceGrad_nashPolynomialTimeSpacetime {H σ s : ℝ}
    (hH : 0 < H) (hσ : 0 < σ) (z : Vec d × ℝ) :
    parSpaceGrad (nashPolynomialTimeSpacetime (d := d) H σ s) z = 0 := by
  let w : Vec d × ℝ → ℝ := fun y => y.2 - s
  have hw : ContDiff ℝ 1 w := by
    dsimp [w]
    exact contDiff_snd.sub (contDiff_const : ContDiff ℝ 1 (fun _ : Vec d × ℝ => s))
  have hderivW : HasFDerivAt w (ContinuousLinearMap.snd ℝ (Vec d) ℝ) z := by
    dsimp [w]
    exact hasFDerivAt_snd.sub_const s
  have hgradw : parSpaceGrad w z = 0 := by
    ext i
    rw [parSpaceGrad, hderivW.fderiv]
    simp
  change parSpaceGrad (nashPolynomialTimeFactor (d := d) H σ ∘ w) z = 0
  rw [PDE.Parabolic.Chain.parSpaceGrad_comp
    (nashPolynomialTimeFactor_contDiff_one (d := d) hH hσ) hw z, hgradw]
  simp

theorem nashPolynomialGaussianWeight_contDiff_one {H σ s : ℝ}
    (hH : 0 < H) (hσ : 0 < σ) {K : Set (Vec d)} (hK : K.Nonempty)
    {R A : ℝ} (hR : 0 ≤ R) (hA : 0 < A) (n : ℕ) :
    ContDiff ℝ 1 (nashPolynomialGaussianWeight (d := d) H K R A σ s n) := by
  unfold nashPolynomialGaussianWeight
  exact (nashPolynomialTimeSpacetime_contDiff_one (d := d) hH hσ).mul
    (nashSmoothGaussianWeight_contDiff_one hK hR hA hσ n)

/-- Weighted density inequality after adding the sharp Nash time power. -/
theorem nashPolynomialGaussian_weightedDensity_pointwise {H : ℝ}
    {K : Set (Vec d)} (hK : K.Nonempty) {R Lam A σ s : ℝ}
    (hH : 0 < H) (hR : 0 ≤ R) (hLam : 0 ≤ Lam) (hA : Lam < A)
    (hσ : 0 < σ) (n : ℕ) (z : Vec d × ℝ)
    (hz₀ : s ≤ z.2) (hzH : z.2 ≤ s + H)
    {M : Mat d} (hM : IsEllipticMatrix 1 Lam M) (u : ℝ) (v : Vec d) :
    let ξ := nashPolynomialGaussianWeight (d := d) H K R A σ s n
    let τ := nashPositiveTimeShift σ (z.2 - s)
    let q := truncatedDistanceMollify K R n z.1 ^ 2
    let α := ((d : ℝ) + 2) / 4
    let ψ := q / (4 * A * τ)
    u ^ 2 * ξ z * parTimeDeriv ξ z ≤
      ξ z ^ 2 * vecDot v (matVecMul M v) +
        2 * ξ z * u * vecDot (matVecMul M v) (parSpaceGrad ξ z) -
          (ξ z ^ 2 * u ^ 2 * ( (1 - Lam / A) * ψ - α) / τ) := by
  dsimp only
  let θ := nashPolynomialTimeSpacetime (d := d) H σ s
  let W := nashSmoothGaussianWeight K R A σ s n
  let ξ := nashPolynomialGaussianWeight (d := d) H K R A σ s n
  let τ := nashPositiveTimeShift σ (z.2 - s)
  let q := truncatedDistanceMollify K R n z.1 ^ 2
  let α : ℝ := ((d : ℝ) + 2) / 4
  let ψ := q / (4 * A * τ)
  have hApos : 0 < A := lt_of_le_of_lt hLam hA
  have hθderiv := parTimeDeriv_nashPolynomialTimeSpacetime
    (d := d) hH hσ hz₀ (by linarith)
  have hWderiv := parTimeDeriv_nashSmoothGaussianWeight
    (s := s) hK hR hApos hσ n z
  have hθgrad := parSpaceGrad_nashPolynomialTimeSpacetime
    (d := d) (s := s) hH hσ z
  have hWgrad := parSpaceGrad_nashSmoothGaussianWeight_eq
    (s := s) hK hR hApos hσ n z
  have hξtime : parTimeDeriv ξ z =
      parTimeDeriv θ z * W z + θ z * parTimeDeriv W z := by
    exact PDE.Parabolic.Chain.parTimeDeriv_mul
      (nashPolynomialTimeSpacetime_contDiff_one (d := d) hH hσ)
      (nashSmoothGaussianWeight_contDiff_one hK hR hApos hσ n) z
  have hξgrad : parSpaceGrad ξ z = θ z • parSpaceGrad W z := by
    change parSpaceGrad (fun y => θ y * W y) z = _
    rw [PDE.Parabolic.Chain.parSpaceGrad_mul
        (nashPolynomialTimeSpacetime_contDiff_one (d := d) hH hσ)
        (nashSmoothGaussianWeight_contDiff_one hK hR hApos hσ n) z]
    rw [hθgrad]
    simp only [smul_zero, zero_add]
    rfl
  have hbase := nashSmoothGaussian_weightedDensity_pointwise
    (s := s) hK hR hLam hA hσ n z hz₀ hM u v
  have hscaled := mul_le_mul_of_nonneg_left hbase (sq_nonneg (θ z))
  rw [hξtime, hξgrad, PDE.DGNM.vecDot_smul_right]
  have hshift : nashPositiveTimeShift σ (z.2 - s) = z.2 - s + σ := by
    exact nashPositiveTimeShift_eq_add hσ (sub_nonneg.mpr hz₀)
  have hτpos : 0 < z.2 - s + σ := by linarith
  have hτne : z.2 - s + σ ≠ 0 := ne_of_gt hτpos
  have hα : α = ((d : ℝ) + 2) / 4 := rfl
  have hθvalue : θ z = (z.2 - s + σ) ^ α := by
    dsimp [θ, nashPolynomialTimeSpacetime]
    rw [nashPolynomialTimeFactor_eq_rpow hH hσ
      (sub_nonneg.mpr hz₀) (by linarith), hshift]
  have hθrate : parTimeDeriv θ z = α * θ z / (z.2 - s + σ) := by
    rw [hθderiv, hshift, hα, hθvalue, Real.rpow_sub_one hτne]
    ring
  have hloss :
      θ z ^ 2 * ((1 - Lam / A) * q * W z ^ 2 * u ^ 2 /
        (4 * A * (z.2 - s + σ) ^ 2)) -
        θ z * parTimeDeriv θ z * W z ^ 2 * u ^ 2 =
      (θ z * W z) ^ 2 * u ^ 2 *
        ((1 - Lam / A) * (q / (4 * A * (z.2 - s + σ))) - α) /
          (z.2 - s + σ) := by
    rw [hθrate]
    field_simp [ne_of_gt hApos, hτne]
  rw [hshift] at hscaled ⊢
  rw [hθrate]
  change u ^ 2 * (θ z * W z) *
      (α * θ z / (z.2 - s + σ) * W z + θ z * parTimeDeriv W z) ≤
    (θ z * W z) ^ 2 * vecDot v (matVecMul M v) +
      2 * (θ z * W z) * u *
        (θ z * vecDot (matVecMul M v) (parSpaceGrad W z)) -
      (θ z * W z) ^ 2 * u ^ 2 *
        ((1 - Lam / A) * (q / (4 * A * (z.2 - s + σ))) - α) /
          (z.2 - s + σ)
  rw [← hloss]
  rw [hθrate]
  linear_combination hscaled -
    (u ^ 2 * θ z ^ 2 * W z ^ 2 / (z.2 - s + σ)) * hα

/-- The product weight is positive and globally bounded. -/
theorem nashPolynomialGaussianWeight_value_bounds {H : ℝ}
    {K : Set (Vec d)} (hK : K.Nonempty) {R A σ s : ℝ}
    (hH : 0 < H) (hR : 0 ≤ R) (hA : 0 < A) (hσ : 0 < σ)
    (n : ℕ) (z : Vec d × ℝ) :
    0 ≤ nashPolynomialGaussianWeight (d := d) H K R A σ s n z ∧
      |nashPolynomialGaussianWeight (d := d) H K R A σ s n z| ≤
        (H + 2 * σ) ^ (((d : ℝ) + 2) / 4) *
          Real.exp (R ^ 2 / (2 * A * σ)) := by
  let θ := nashPolynomialTimeSpacetime (d := d) H σ s
  let W := nashSmoothGaussianWeight K R A σ s n
  have hθ := nashPolynomialTimeFactor_bounds (d := d) (H := H) (σ := σ)
    (x := z.2 - s) hH hσ
  have hW := nashSmoothGaussianWeight_bounds (s := s) hK hR hA hσ n z
  have hTnonneg : 0 ≤ (H + 2 * σ) ^ (((d : ℝ) + 2) / 4) := by positivity
  have hθpos : 0 < θ z := by
    simpa [θ, nashPolynomialTimeSpacetime] using hθ.1
  have hθabs : |θ z| ≤ (H + 2 * σ) ^ (((d : ℝ) + 2) / 4) := by
    rw [abs_of_nonneg hθpos.le]
    simpa [θ, nashPolynomialTimeSpacetime] using hθ.2
  have hWnonneg : 0 ≤ W z := by linarith
  have hWabs : |W z| ≤ Real.exp (R ^ 2 / (2 * A * σ)) := by
    rw [abs_of_nonneg hWnonneg]
    exact hW.2
  have hxiNonneg : 0 ≤ θ z * W z := mul_nonneg hθ.1.le hWnonneg
  have hproduct : |θ z * W z| ≤
      (H + 2 * σ) ^ (((d : ℝ) + 2) / 4) *
        Real.exp (R ^ 2 / (2 * A * σ)) := by
    rw [abs_of_nonneg hxiNonneg]
    calc
      θ z * W z ≤ (H + 2 * σ) ^ (((d : ℝ) + 2) / 4) * W z :=
        mul_le_mul_of_nonneg_right hθ.2 hWnonneg
      _ ≤ (H + 2 * σ) ^ (((d : ℝ) + 2) / 4) *
          Real.exp (R ^ 2 / (2 * A * σ)) :=
        mul_le_mul_of_nonneg_left hW.2 hTnonneg
  constructor
  · simpa [nashPolynomialGaussianWeight, θ, W] using hxiNonneg
  · simpa [nashPolynomialGaussianWeight, θ, W] using hproduct

/-- Uniform global bound for the time derivative of the capped time factor. -/
theorem parTimeDeriv_nashPolynomialTimeSpacetime_abs_le {H σ s : ℝ}
    (hH : 0 < H) (hσ : 0 < σ) (z : Vec d × ℝ) :
    |parTimeDeriv (nashPolynomialTimeSpacetime (d := d) H σ s) z| ≤
      (((d : ℝ) + 2) / 4) *
        ((σ / 2) ^ ((((d : ℝ) + 2) / 4) - 1) +
          (H + 2 * σ) ^ ((((d : ℝ) + 2) / 4) - 1)) := by
  let F := nashPolynomialTimeFactor (d := d) H σ
  let w : Vec d × ℝ → ℝ := fun y => y.2 - s
  have hF : ContDiff ℝ 1 F := nashPolynomialTimeFactor_contDiff_one (d := d) hH hσ
  have hw : ContDiff ℝ 1 w := by
    dsimp [w]
    exact contDiff_snd.sub (contDiff_const : ContDiff ℝ 1 (fun _ : Vec d × ℝ => s))
  have hderivW : HasFDerivAt w (ContinuousLinearMap.snd ℝ (Vec d) ℝ) z := by
    dsimp [w]
    exact hasFDerivAt_snd.sub_const s
  have hcomp := PDE.Parabolic.Chain.parTimeDeriv_comp hF hw z
  change parTimeDeriv (F ∘ w) z = deriv F (w z) * parTimeDeriv w z at hcomp
  have htimew : parTimeDeriv w z = 1 := by
    rw [parTimeDeriv, hderivW.fderiv]
    simp
  have hidentity :
      parTimeDeriv (nashPolynomialTimeSpacetime (d := d) H σ s) z =
        deriv (nashPolynomialTimeFactor (d := d) H σ) (z.2 - s) := by
    change parTimeDeriv (F ∘ w) z = _
    rw [hcomp, htimew]
    simp [F, w]
  rw [hidentity]
  simpa [F] using nashPolynomialTimeFactor_deriv_bound (d := d) (H := H)
    (σ := σ) (x := z.2 - s) hH hσ

/-- Global bounds for the product weight and its first derivatives. These are
the hypotheses needed to apply the whole-space weighted energy identity. -/
theorem nashPolynomialGaussianWeight_global_bounds {H : ℝ}
    {K : Set (Vec d)} (hK : K.Nonempty) {R A σ s : ℝ}
    (hH : 0 < H) (hR : 0 ≤ R) (hA : 0 < A) (hσ : 0 < σ) (n : ℕ) :
    ∃ B Bt Bg : ℝ, 0 ≤ B ∧ 0 ≤ Bt ∧ 0 ≤ Bg ∧
      (∀ z, |nashPolynomialGaussianWeight (d := d) H K R A σ s n z| ≤ B) ∧
      (∀ z, |parTimeDeriv (nashPolynomialGaussianWeight (d := d) H K R A σ s n) z| ≤ Bt) ∧
      (∀ z, vecEuclideanNorm
        (parSpaceGrad (nashPolynomialGaussianWeight (d := d) H K R A σ s n) z) ≤ Bg) := by
  let Bθ : ℝ := (H + 2 * σ) ^ (((d : ℝ) + 2) / 4)
  let E : ℝ := Real.exp (R ^ 2 / (2 * A * σ))
  let Dθ : ℝ := (((d : ℝ) + 2) / 4) *
        ((σ / 2) ^ ((((d : ℝ) + 2) / 4) - 1) +
          (H + 2 * σ) ^ ((((d : ℝ) + 2) / 4) - 1))
  let Dt : ℝ := E * R ^ 2 / (A * σ ^ 2)
  let Dg : ℝ := E * R / (A * σ)
  let B : ℝ := Bθ * E
  let Bt : ℝ := Dθ * E + Bθ * Dt
  let Bg : ℝ := Bθ * Dg
  have hBθ : 0 ≤ Bθ := by dsimp [Bθ]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hDθ : 0 ≤ Dθ := by dsimp [Dθ]; positivity
  have hDt : 0 ≤ Dt := by dsimp [Dt]; positivity
  have hDg : 0 ≤ Dg := by dsimp [Dg]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hBt : 0 ≤ Bt := by dsimp [Bt]; positivity
  have hBg : 0 ≤ Bg := by dsimp [Bg]; positivity
  refine ⟨B, Bt, Bg, hB, hBt, hBg, ?_, ?_, ?_⟩
  · intro z
    simpa [B, Bθ, E] using
      (nashPolynomialGaussianWeight_value_bounds (d := d) hK hH hR hA hσ n z).2
  · intro z
    let θ := nashPolynomialTimeSpacetime (d := d) H σ s
    let W := nashSmoothGaussianWeight K R A σ s n
    have hθval := nashPolynomialTimeFactor_bounds (d := d) (H := H) (σ := σ)
      (x := z.2 - s) hH hσ
    have hWval := nashSmoothGaussianWeight_bounds (s := s) hK hR hA hσ n z
    have hθderiv := parTimeDeriv_nashPolynomialTimeSpacetime_abs_le
      (d := d) (s := s) hH hσ z
    have hWderiv := nashSmoothGaussianWeight_timeDeriv_bound
      (s := s) hK hR hA hσ n z
    have hproduct := PDE.Parabolic.Chain.parTimeDeriv_mul
      (nashPolynomialTimeSpacetime_contDiff_one (d := d) (s := s) hH hσ)
      (nashSmoothGaussianWeight_contDiff_one (s := s) hK hR hA hσ n) z
    change |parTimeDeriv (fun y => θ y * W y) z| ≤ Bt
    rw [hproduct]
    have hθpos : 0 < θ z := by
      simpa [θ, nashPolynomialTimeSpacetime] using hθval.1
    have hθabs : |θ z| ≤ Bθ := by
      rw [abs_of_nonneg hθpos.le]
      simpa [θ, nashPolynomialTimeSpacetime, Bθ] using hθval.2
    have hWnonneg : 0 ≤ W z := by linarith
    have hWabs : |W z| ≤ E := by
      rw [abs_of_nonneg hWnonneg]
      simpa [E] using hWval.2
    have hθderiv' : |parTimeDeriv θ z| ≤ Dθ := by simpa [Dθ, θ] using hθderiv
    have hWderiv' : |parTimeDeriv W z| ≤ Dt := by simpa [Dt, E, W] using hWderiv
    calc
      |parTimeDeriv θ z * W z + θ z * parTimeDeriv W z| ≤
          |parTimeDeriv θ z * W z| + |θ z * parTimeDeriv W z| := abs_add_le _ _
      _ = |parTimeDeriv θ z| * |W z| + |θ z| * |parTimeDeriv W z| := by
        rw [abs_mul, abs_mul]
      _ ≤ Dθ * E + Bθ * Dt := by
        apply add_le_add
        · calc
            |parTimeDeriv θ z| * |W z| ≤ Dθ * |W z| :=
              mul_le_mul_of_nonneg_right hθderiv' (abs_nonneg _)
            _ ≤ Dθ * E := mul_le_mul_of_nonneg_left hWabs hDθ
        · calc
            |θ z| * |parTimeDeriv W z| ≤ Bθ * |parTimeDeriv W z| :=
              mul_le_mul_of_nonneg_right hθabs (abs_nonneg _)
            _ ≤ Bθ * Dt := mul_le_mul_of_nonneg_left hWderiv' hBθ
      _ = Bt := rfl
  · intro z
    let θ := nashPolynomialTimeSpacetime (d := d) H σ s
    let W := nashSmoothGaussianWeight K R A σ s n
    have hθval := nashPolynomialTimeFactor_bounds (d := d) (H := H) (σ := σ)
      (x := z.2 - s) hH hσ
    have hθgrad : parSpaceGrad θ z = 0 :=
      parSpaceGrad_nashPolynomialTimeSpacetime (d := d) (s := s) hH hσ z
    have hWgrad := nashSmoothGaussianWeight_spatialGrad_bound
      (s := s) (t := z.2) hK hR hA hσ n z.1
    have hproduct := PDE.Parabolic.Chain.parSpaceGrad_mul
      (nashPolynomialTimeSpacetime_contDiff_one (d := d) (s := s) hH hσ)
      (nashSmoothGaussianWeight_contDiff_one (s := s) hK hR hA hσ n) z
    change vecEuclideanNorm (parSpaceGrad (fun y => θ y * W y) z) ≤ Bg
    rw [hproduct, hθgrad]
    simp only [smul_zero, zero_add]
    have hθpos : 0 < θ z := by
      simpa [θ, nashPolynomialTimeSpacetime] using hθval.1
    have hθabs : |θ z| ≤ Bθ := by
      rw [abs_of_nonneg hθpos.le]
      simpa [θ, nashPolynomialTimeSpacetime, Bθ] using hθval.2
    rw [vecEuclideanNorm_smul]
    calc
      |θ z| * vecEuclideanNorm (parSpaceGrad W z) ≤ Bθ * Dg :=
        mul_le_mul hθabs (by simpa [Dg, E, W] using hWgrad)
          (vecEuclideanNorm_nonneg _) hBθ
      _ = Bg := rfl

/-- Almost everywhere form of the polynomial Gaussian density inequality on a
Cauchy slab. -/
theorem nashPolynomialGaussian_weightedDensity_ae {H Lam A σ s : ℝ}
    (hH : 0 < H) (hLam : 1 ≤ Lam) (hA : Lam < A) (hσ : 0 < σ)
    {a : ParCoeffField d}
    (ha : IsParabolicCoeff 1 Lam a univ (Icc s (s + H)))
    (K : Set (Vec d)) (hK : K.Nonempty) {R : ℝ} (hR : 0 ≤ R) (n : ℕ)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s (s + H))) :
    ∀ᵐ z ∂(volume.restrict
      ((univ : Set (Vec d)) ×ˢ Ioc s (s + H))),
      let ξ := nashPolynomialGaussianWeight (d := d) H K R A σ s n
      let τ := nashPositiveTimeShift σ (z.2 - s)
      let q := truncatedDistanceMollify K R n z.1 ^ 2
      let α := ((d : ℝ) + 2) / 4
      let ψ := q / (4 * A * τ)
      u.toFun z ^ 2 * ξ z * parTimeDeriv ξ z ≤
        ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z +
          2 * ξ z * u.toFun z *
            vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad ξ z) -
          (ξ z ^ 2 * u.toFun z ^ 2 * ((1 - Lam / A) * ψ - α) / τ) := by
  let Q : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s (s + H)
  have hQsub : Q ⊆ (univ : Set (Vec d)) ×ˢ Icc s (s + H) := by
    intro z hz
    exact ⟨hz.1, ⟨hz.2.1.le, hz.2.2⟩⟩
  have hQmeasure : volume.restrict Q ≤
      volume.restrict ((univ : Set (Vec d)) ×ˢ Icc s (s + H)) :=
    Measure.restrict_mono hQsub le_rfl
  have hcoeff : ∀ᵐ z ∂(volume.restrict Q), IsEllipticMatrix 1 Lam (a z) :=
    ha.elliptic.filter_mono (ae_mono hQmeasure)
  have hQmem : ∀ᵐ z ∂(volume.restrict Q), z ∈ Q :=
    ae_restrict_mem (MeasurableSet.prod MeasurableSet.univ measurableSet_Ioc)
  filter_upwards [hcoeff, hQmem] with z hMz hz
  have hz₀ : s ≤ z.2 := le_of_lt hz.2.1
  have hzH : z.2 ≤ s + H := hz.2.2
  simpa [PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity] using
    nashPolynomialGaussian_weightedDensity_pointwise
    (d := d) (H := H) hK hH hR (by linarith) hA hσ n z hz₀ hzH
    hMz (u.toFun z) (u.grad z)

/-- Scalar coefficient of `u²` in the retained loss term. -/
noncomputable def nashPolynomialGaussianLossCoefficient (H : ℝ)
    (K : Set (Vec d)) (R Lam A σ s : ℝ) (n : ℕ) (z : Vec d × ℝ) : ℝ :=
  nashPolynomialGaussianWeight (d := d) H K R A σ s n z ^ 2 *
    (((1 - Lam / A) *
      (truncatedDistanceMollify K R n z.1 ^ 2 /
        (4 * A * nashPositiveTimeShift σ (z.2 - s))) -
      ((d : ℝ) + 2) / 4) /
      nashPositiveTimeShift σ (z.2 - s))

theorem nashPolynomialGaussianLossCoefficient_contDiff_one {H : ℝ}
    {K : Set (Vec d)} (hK : K.Nonempty) {R Lam A σ s : ℝ}
    (hH : 0 < H) (hR : 0 ≤ R) (hA : 0 < A) (hσ : 0 < σ) (n : ℕ) :
    ContDiff ℝ 1 (nashPolynomialGaussianLossCoefficient (d := d) H K R Lam A σ s n) := by
  have hρ : ContDiff ℝ 1 (truncatedDistanceMollify K R n) := by
    exact (truncatedDistanceMollify_properties hK hR n).1.of_le (by simp)
  have hρst : ContDiff ℝ 1
      (fun z : Vec d × ℝ => truncatedDistanceMollify K R n z.1) := hρ.comp contDiff_fst
  have hq : ContDiff ℝ 1
      (fun z : Vec d × ℝ => truncatedDistanceMollify K R n z.1 ^ 2) := hρst.pow 2
  have htime : ContDiff ℝ 1
      (fun z : Vec d × ℝ => nashPositiveTimeShift σ (z.2 - s)) :=
    nashPositiveTimeShift_contDiff_one.comp
      (contDiff_snd.sub (contDiff_const : ContDiff ℝ 1 (fun _ : Vec d × ℝ => s)))
  have hden : ContDiff ℝ 1
      (fun z : Vec d × ℝ => 4 * A * nashPositiveTimeShift σ (z.2 - s)) :=
    contDiff_const.mul htime
  have hdenne : ∀ z : Vec d × ℝ,
      4 * A * nashPositiveTimeShift σ (z.2 - s) ≠ 0 := by
    intro z
    have hτ := nashPositiveTimeShift_lower (t := z.2 - s) hσ
    have hτpos : 0 < nashPositiveTimeShift σ (z.2 - s) := by
      linarith [show 0 < σ / 2 by positivity]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hA.ne') hτpos.ne'
  have hψ : ContDiff ℝ 1 (fun z : Vec d × ℝ =>
      truncatedDistanceMollify K R n z.1 ^ 2 /
        (4 * A * nashPositiveTimeShift σ (z.2 - s))) := hq.div hden hdenne
  have hfactor : ContDiff ℝ 1 (fun z : Vec d × ℝ =>
      (1 - Lam / A) *
        (truncatedDistanceMollify K R n z.1 ^ 2 /
          (4 * A * nashPositiveTimeShift σ (z.2 - s))) - ((d : ℝ) + 2) / 4) :=
    (contDiff_const.mul hψ).sub contDiff_const
  have hden2 : ContDiff ℝ 1
      (fun z : Vec d × ℝ => nashPositiveTimeShift σ (z.2 - s)) := htime
  have hden2ne : ∀ z : Vec d × ℝ,
      nashPositiveTimeShift σ (z.2 - s) ≠ 0 := by
    intro z
    have hτ := nashPositiveTimeShift_lower (t := z.2 - s) hσ
    exact ne_of_gt (lt_of_lt_of_le (by positivity) hτ)
  have hfrac := hfactor.div hden2 hden2ne
  have hweight := nashPolynomialGaussianWeight_contDiff_one
    (d := d) (s := s) hH hσ hK hR hA n
  change ContDiff ℝ 1 (fun z =>
    nashPolynomialGaussianWeight (d := d) H K R A σ s n z ^ 2 *
      (((1 - Lam / A) *
        (truncatedDistanceMollify K R n z.1 ^ 2 /
          (4 * A * nashPositiveTimeShift σ (z.2 - s))) -
        ((d : ℝ) + 2) / 4) /
          nashPositiveTimeShift σ (z.2 - s)))
  exact (hweight.pow 2).mul hfrac

theorem nashPolynomialGaussianLossCoefficient_abs_le {H Lam : ℝ}
    {K : Set (Vec d)} (hK : K.Nonempty) {R A σ s : ℝ}
    (hH : 0 < H) (hLam : 1 ≤ Lam) (hR : 0 ≤ R)
    (hA : Lam < A) (hσ : 0 < σ) (n : ℕ) (z : Vec d × ℝ) :
    |nashPolynomialGaussianLossCoefficient (d := d) H K R Lam A σ s n z| ≤
      ((H + 2 * σ) ^ (((d : ℝ) + 2) / 4) *
        Real.exp (R ^ 2 / (2 * A * σ))) ^ 2 *
        (R ^ 2 / (2 * A * σ) + ((d : ℝ) + 2) / 4) * (2 / σ) := by
  let ξ := nashPolynomialGaussianWeight (d := d) H K R A σ s n
  let τ := nashPositiveTimeShift σ (z.2 - s)
  let ρ := truncatedDistanceMollify K R n z.1
  let α : ℝ := ((d : ℝ) + 2) / 4
  have hξ := nashPolynomialGaussianWeight_value_bounds (d := d) (s := s) hK hH hR
    (lt_of_le_of_lt (by linarith) hA) hσ n z
  have hτlower := nashPositiveTimeShift_lower (t := z.2 - s) hσ
  have hτpos : 0 < τ := lt_of_lt_of_le (by positivity) hτlower
  have hτpos' : 0 < nashPositiveTimeShift σ (z.2 - s) := by simpa [τ] using hτpos
  have hApos : 0 < A := lt_of_le_of_lt (by linarith) hA
  have hρ := (truncatedDistanceMollify_properties hK hR n).2.1 z.1
  have hqnonneg : 0 ≤ ρ ^ 2 := sq_nonneg _
  have hqbound : ρ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hρ.1 hρ.2 2
  have hc : 0 < 1 - Lam / A := by
    have hApos : 0 < A := lt_of_le_of_lt (by linarith) hA
    rw [sub_pos]
    exact (div_lt_one hApos).2 hA
  have hcupper : 1 - Lam / A ≤ 1 := by
    have hLamA : 0 ≤ Lam / A := div_nonneg (by linarith) (le_of_lt (lt_of_le_of_lt (by linarith) hA))
    linarith
  have hden : 2 * A * σ ≤ 4 * A * τ := by
    nlinarith [mul_le_mul_of_nonneg_left hτlower (show 0 ≤ 4 * A by positivity)]
  have hdenpos : 0 < 4 * A * τ := by positivity
  have hpsi : 0 ≤ ρ ^ 2 / (4 * A * τ) := div_nonneg hqnonneg hdenpos.le
  have hψbound : ρ ^ 2 / (4 * A * τ) ≤ R ^ 2 / (2 * A * σ) := by
    calc
      ρ ^ 2 / (4 * A * τ) ≤ R ^ 2 / (4 * A * τ) :=
        div_le_div_of_nonneg_right hqbound hdenpos.le
      _ ≤ R ^ 2 / (2 * A * σ) :=
        div_le_div_of_nonneg_left (sq_nonneg R) (by positivity) hden
  have hαpos : 0 ≤ α := by dsimp [α]; positivity
  have hfactor : |(1 - Lam / A) * (ρ ^ 2 / (4 * A * τ)) - α| ≤
      R ^ 2 / (2 * A * σ) + α := by
    calc
      |(1 - Lam / A) * (ρ ^ 2 / (4 * A * τ)) - α| ≤
          |(1 - Lam / A) * (ρ ^ 2 / (4 * A * τ))| + |α| := by
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le
          ((1 - Lam / A) * (ρ ^ 2 / (4 * A * τ))) 0 α
      _ = (1 - Lam / A) * (ρ ^ 2 / (4 * A * τ)) + α := by
        rw [abs_of_nonneg (mul_nonneg hc.le hpsi), abs_of_nonneg hαpos]
      _ ≤ R ^ 2 / (2 * A * σ) + α := by
        calc
          (1 - Lam / A) * (ρ ^ 2 / (4 * A * τ)) + α ≤
              1 * (ρ ^ 2 / (4 * A * τ)) + α := by gcongr
          _ = ρ ^ 2 / (4 * A * τ) + α := by ring
          _ ≤ R ^ 2 / (2 * A * σ) + α := add_le_add hψbound le_rfl
  have hInvτ : 1 / τ ≤ 2 / σ := by
    calc
      1 / τ ≤ 1 / (σ / 2) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hτlower
      _ = 2 / σ := by field_simp [ne_of_gt hσ]
  have hξabs : |ξ z| ≤
      (H + 2 * σ) ^ (((d : ℝ) + 2) / 4) *
        Real.exp (R ^ 2 / (2 * A * σ)) := by simpa [ξ] using hξ.2
  have hξSq : ξ z ^ 2 ≤
      ((H + 2 * σ) ^ (((d : ℝ) + 2) / 4) *
        Real.exp (R ^ 2 / (2 * A * σ))) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hξabs 2
  have hcoefpos : 0 ≤ ξ z ^ 2 := sq_nonneg _
  have hbound : |ξ z ^ 2 *
      (((1 - Lam / A) * (ρ ^ 2 / (4 * A * τ)) - α) / τ)| ≤
      ((H + 2 * σ) ^ (((d : ℝ) + 2) / 4) *
        Real.exp (R ^ 2 / (2 * A * σ))) ^ 2 *
        (R ^ 2 / (2 * A * σ) + α) * (2 / σ) := by
    rw [abs_mul, abs_div, abs_of_nonneg hcoefpos, abs_of_pos hτpos']
    calc
      ξ z ^ 2 *
          (|(1 - Lam / A) * (ρ ^ 2 / (4 * A * τ)) - α| / τ) =
          ξ z ^ 2 *
            |(1 - Lam / A) * (ρ ^ 2 / (4 * A * τ)) - α| / τ := by ring
      _ ≤
        ξ z ^ 2 * (R ^ 2 / (2 * A * σ) + α) / τ := by gcongr
      _ ≤ ξ z ^ 2 * (R ^ 2 / (2 * A * σ) + α) * (2 / σ) := by
        calc
          ξ z ^ 2 * (R ^ 2 / (2 * A * σ) + α) / τ =
              (ξ z ^ 2 * (R ^ 2 / (2 * A * σ) + α)) * (1 / τ) := by ring
          _ ≤ (ξ z ^ 2 * (R ^ 2 / (2 * A * σ) + α)) * (2 / σ) :=
            mul_le_mul_of_nonneg_left hInvτ
              (mul_nonneg hcoefpos (by positivity))
          _ = _ := by ring
      _ ≤ ((H + 2 * σ) ^ (((d : ℝ) + 2) / 4) *
          Real.exp (R ^ 2 / (2 * A * σ))) ^ 2 *
            (R ^ 2 / (2 * A * σ) + α) * (2 / σ) := by gcongr
  simpa [nashPolynomialGaussianLossCoefficient, ξ, τ, ρ, α] using hbound

/-- Integrability of the signed loss coefficient against the square of a
space-time `L²` Cauchy solution. -/
theorem nashPolynomialGaussianLoss_integrableOn {H Lam : ℝ}
    {K : Set (Vec d)} (hK : K.Nonempty) {R A σ s : ℝ}
    (hH : 0 < H) (hLam : 1 ≤ Lam) (hR : 0 ≤ R)
    (hA : Lam < A) (hσ : 0 < σ) (n : ℕ)
    {u : ParH1Function (univ : Set (Vec d)) (Icc s (s + H))} :
    IntegrableOn (fun z =>
      nashPolynomialGaussianLossCoefficient (d := d) H K R Lam A σ s n z *
        u.toFun z ^ 2)
      ((univ : Set (Vec d)) ×ˢ Ioc s (s + H)) := by
  let Q : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s (s + H)
  let C : ℝ :=
    ((H + 2 * σ) ^ (((d : ℝ) + 2) / 4) *
      Real.exp (R ^ 2 / (2 * A * σ))) ^ 2 *
      (R ^ 2 / (2 * A * σ) + ((d : ℝ) + 2) / 4) * (2 / σ)
  let c := nashPolynomialGaussianLossCoefficient (d := d) H K R Lam A σ s n
  have hQsub : Q ⊆ (univ : Set (Vec d)) ×ˢ Icc s (s + H) := by
    intro z hz
    exact ⟨hz.1, ⟨hz.2.1.le, hz.2.2⟩⟩
  have hQmeasure : volume.restrict Q ≤
      volume.restrict ((univ : Set (Vec d)) ×ˢ Icc s (s + H)) :=
    Measure.restrict_mono hQsub le_rfl
  have huSq : Integrable (fun z : Vec d × ℝ => u.toFun z ^ 2)
      (volume.restrict Q) := u.memL2.integrable_sq |>.mono_measure hQmeasure
  have hcCont : Continuous c := by
    dsimp [c]
    exact (nashPolynomialGaussianLossCoefficient_contDiff_one (d := d)
      (s := s) hK hH hR (lt_of_le_of_lt (by linarith) hA) hσ n).continuous
  have hcMeas : AEStronglyMeasurable c (volume.restrict Q) :=
    hcCont.aestronglyMeasurable
  have hApos : 0 < A := lt_of_le_of_lt (by linarith) hA
  have hCnonneg : 0 ≤ C := by dsimp [C]; positivity
  have hcBound : ∀ᵐ z ∂(volume.restrict Q), ‖c z‖ ≤ C := by
    filter_upwards [] with z
    rw [Real.norm_eq_abs]
    simpa [C, c] using nashPolynomialGaussianLossCoefficient_abs_le
      (d := d) (s := s) hK hH hLam hR hA hσ n z
  have hmul := huSq.mul_bdd hcMeas (c := C) hcBound
  simpa only [IntegrableOn, Q, c, mul_comm] using hmul

/-- The whole-space weighted energy inequality with the Nash time power and
its explicit signed loss term. -/
theorem nashPolynomialGaussian_energy_dissipation {H Lam : ℝ}
    {K : Set (Vec d)} (hK : K.Nonempty) {R A σ s : ℝ}
    (hH : 0 < H) (hLam : 1 ≤ Lam) (hR : 0 ≤ R)
    (hA : Lam < A) (hσ : 0 < σ) (n : ℕ)
    {a : ParCoeffField d}
    (ha : IsParabolicCoeff 1 Lam a univ (Icc s (s + H)))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s (s + H)))
    (hu : IsCauchySolution a s (s + H) f u) :
    (∫ x : Vec d,
      nashPolynomialGaussianWeight (d := d) H K R A σ s n (x, s + H) ^ 2 *
        u.toFun (x, s + H) ^ 2) +
      2 * ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s (s + H),
        nashPolynomialGaussianLossCoefficient (d := d) H K R Lam A σ s n z *
          u.toFun z ^ 2 ≤
    ∫ x : Vec d,
      nashPolynomialGaussianWeight (d := d) H K R A σ s n (x, s) ^ 2 * f x ^ 2 := by
  let ξ := nashPolynomialGaussianWeight (d := d) H K R A σ s n
  have hsT : s < s + H := by linarith
  have hweight := nashPolynomialGaussianWeight_contDiff_one
    (d := d) (s := s) hH hσ hK hR (lt_of_le_of_lt (by linarith) hA) n
  obtain ⟨B, Bt, Bg, hB, hBt, hBg, hξbound, hξtbound, hgradbound⟩ :=
    nashPolynomialGaussianWeight_global_bounds
      (d := d) (s := s) hK hH hR (lt_of_le_of_lt (by linarith) hA) hσ n
  have hloss := nashPolynomialGaussianLoss_integrableOn
    (d := d) (s := s) hK hH hLam hR hA hσ n (u := u)
  have hpoly := nashPolynomialGaussian_weightedDensity_ae
    (d := d) (s := s) hH hLam hA hσ ha K hK hR n u
  have hdensity : ∀ᵐ z ∂(volume.restrict
      ((univ : Set (Vec d)) ×ˢ Ioc s (s + H))),
      u.toFun z ^ 2 * ξ z * parTimeDeriv ξ z ≤
        ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z +
          2 * ξ z * u.toFun z *
            vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad ξ z) -
          nashPolynomialGaussianLossCoefficient (d := d) H K R Lam A σ s n z *
            u.toFun z ^ 2 := by
    filter_upwards [hpoly] with z hz
    convert hz using 1; dsimp [nashPolynomialGaussianLossCoefficient, ξ]; ring
  have hresult := cauchySmoothWeighted_energy_dissipation
    (hsT := hsT) (t := s + H) ha f hf u hu ξ hweight B Bt Bg hB hBt hBg
    hξbound hξtbound hgradbound ⟨hsT.le, le_rfl⟩ hsT
    (fun z => nashPolynomialGaussianLossCoefficient (d := d) H K R Lam A σ s n z *
      u.toFun z ^ 2) hloss hdensity
  simpa only [ξ] using hresult

end PDE.Parabolic.Cauchy.Weights
