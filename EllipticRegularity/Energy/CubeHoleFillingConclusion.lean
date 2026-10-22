module

public import EllipticRegularity.Energy.CubeHoleFillingEnergyBound

/-! # General-dimensional hole-filling conclusion on round balls -/

@[expose] public section

namespace PDE

open MeasureTheory

/-- A dimension-only constant that absorbs the ball energy coefficient and
sets an exponent no larger than half the cube energy-decay exponent. -/
noncomputable def cubeHoleFillingConst (d : ℕ) : ℝ :=
  (cubeHoleFillingBallEnergyConst d * cubeHoleFillingFactor d) ^ 2

/-- The explicit conclusion constant is positive in dimension at least two. -/
theorem cubeHoleFillingConst_pos {d : ℕ} (hd : 2 ≤ d) :
    0 < cubeHoleFillingConst d := by
  have hD : 0 < cubeHoleFillingBallEnergyConst d := by
    unfold cubeHoleFillingBallEnergyConst
    have hdreal : (0 : ℝ) ≤ d := by positivity
    positivity
  have hF : 0 < cubeHoleFillingFactor d :=
    lt_of_lt_of_le (by norm_num) (cubeHoleFillingFactor_ge_one d)
  unfold cubeHoleFillingConst
  positivity

/-- The explicit exponent `(C(d) Λ)^(-1/2)` is at most half the cube
hole-filling exponent. -/
theorem cubeHoleFilling_alpha_le_half_exponent
    {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn 1 Λ (euclideanBall (0 : Vec d) 1) a) :
    (cubeHoleFillingConst d * Λ) ^ (-(1 / 2 : ℝ)) ≤
      holeFillingDyadicExponent (cubeHoleFillingK d Λ) / 2 := by
  let D := cubeHoleFillingBallEnergyConst d
  let F := cubeHoleFillingFactor d
  let B := D * F
  let C := cubeHoleFillingConst d
  have hD : 4 ≤ D := by
    dsimp [D, cubeHoleFillingBallEnergyConst]
    have hdreal : (0 : ℝ) ≤ d := by positivity
    linarith only [hdreal]
  have hF : 1 ≤ F := cubeHoleFillingFactor_ge_one d
  have hB : 0 < B := by dsimp [B]; positivity
  have hB4F : 4 * F ≤ B := by
    dsimp [B]
    exact mul_le_mul_of_nonneg_right hD (by linarith only [hF])
  have hC : 0 < C := cubeHoleFillingConst_pos hd
  have hCroot : Real.sqrt C = B := by
    dsimp [C, cubeHoleFillingConst, B, D, F]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hB]
  have hΛ : 0 < Λ :=
    (hEll.elliptic (center_mem_euclideanBall (0 : Vec d)
      (by norm_num : (0 : ℝ) < 1))).Lam_pos
  have hsqrtΛ : 0 < Real.sqrt Λ := Real.sqrt_pos.2 hΛ
  have hαEq : (C * Λ) ^ (-(1 / 2 : ℝ)) =
      1 / (B * Real.sqrt Λ) := by
    rw [Real.rpow_neg (mul_nonneg hC.le hΛ.le),
      ← Real.sqrt_eq_rpow, Real.sqrt_mul hC.le Λ, hCroot]
    ring
  have hαBound : 1 / (B * Real.sqrt Λ) ≤
      1 / (4 * F * Real.sqrt Λ) := by
    have hden : 4 * F * Real.sqrt Λ ≤ B * Real.sqrt Λ :=
      mul_le_mul_of_nonneg_right hB4F hsqrtΛ.le
    exact div_le_div_of_nonneg_left (by norm_num)
      (mul_pos (by positivity : 0 < 4 * F) hsqrtΛ) hden
  have hβ := cube_hole_filling_exponent_lowerBound hEll
    (center_mem_euclideanBall (0 : Vec d)
      (by norm_num : (0 : ℝ) < 1))
  have hβ' : 1 / (2 * F * Real.sqrt Λ) ≤
      holeFillingDyadicExponent (cubeHoleFillingK d Λ) := by
    have hpow : Λ ^ (-(1 / 2 : ℝ)) = (Real.sqrt Λ)⁻¹ := by
      rw [Real.rpow_neg hΛ.le, Real.sqrt_eq_rpow]
    dsimp [F] at hβ ⊢
    rw [hpow] at hβ
    convert hβ using 1
    field_simp [hF, hsqrtΛ.ne']
  calc
    (cubeHoleFillingConst d * Λ) ^ (-(1 / 2 : ℝ)) =
        1 / (B * Real.sqrt Λ) := hαEq
    _ ≤ 1 / (4 * F * Real.sqrt Λ) := hαBound
    _ ≤ holeFillingDyadicExponent (cubeHoleFillingK d Λ) / 2 := by
      have heq : 1 / (4 * F * Real.sqrt Λ) =
          (1 / (2 * F * Real.sqrt Λ)) / 2 := by ring
      rw [heq]
      exact div_le_div_of_nonneg_right hβ' (by norm_num)

/-- Quantitative hole filling for a homogeneous weak solution on the unit
round ball in dimension at least two. The constant depends only on `d`. -/
theorem holeFilling_of_isEllipticFieldOn
    {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} {a : CoeffField d}
    {u : H1Function (euclideanBall (0 : Vec d) 1)}
    (hEll : IsEllipticFieldOn 1 Λ (euclideanBall (0 : Vec d) 1) a)
    (hsol : IsWeakDivergenceFormHarmonicOn a
      (euclideanBall (0 : Vec d) 1) u)
    {r : ℝ} (hr : 0 < r) (hrhalf : r ≤ 1 / 2) :
    Real.sqrt (∫ x in euclideanBall (0 : Vec d) r,
      vecNormSq (u.grad x)) ≤
      cubeHoleFillingConst d * Real.sqrt Λ *
        r ^ ((cubeHoleFillingConst d * Λ) ^ (-(1 / 2 : ℝ))) *
        Real.sqrt (∫ x in euclideanBall (0 : Vec d) 1, u x ^ 2) := by
  let C := cubeHoleFillingConst d
  let D := cubeHoleFillingBallEnergyConst d
  let F := cubeHoleFillingFactor d
  let β := holeFillingDyadicExponent (cubeHoleFillingK d Λ)
  let α := (C * Λ) ^ (-(1 / 2 : ℝ))
  let I : ℝ := ∫ x in euclideanBall (0 : Vec d) 1, u x ^ 2
  let G : ℝ := ∫ x in euclideanBall (0 : Vec d) r, vecNormSq (u.grad x)
  have hΛ : 0 < Λ :=
    (hEll.elliptic (center_mem_euclideanBall (0 : Vec d)
      (by norm_num : (0 : ℝ) < 1))).Lam_pos
  have hI : 0 ≤ I := integral_nonneg_of_ae
    (Filter.Eventually.of_forall fun x => sq_nonneg (u x))
  have hC : 0 < C := cubeHoleFillingConst_pos hd
  have hD : 0 ≤ D := by
    dsimp [D, cubeHoleFillingBallEnergyConst]
    positivity
  have hF : 1 ≤ F := cubeHoleFillingFactor_ge_one d
  have hDge : 1 ≤ D := by
    dsimp [D, cubeHoleFillingBallEnergyConst]
    have hdreal : (0 : ℝ) ≤ d := by positivity
    linarith only [hdreal]
  have hCD : D ≤ C ^ 2 := by
    have hB : D ≤ D * F := by
      nlinarith only [hDge, hF]
    have hBge : 1 ≤ D * F := by nlinarith only [hDge, hF]
    have hB2 : D * F ≤ (D * F) ^ 2 := by nlinarith only [hBge]
    dsimp [C, cubeHoleFillingConst]
    nlinarith only [hB, hB2, hBge]
  have hα : α ≤ β / 2 :=
    cubeHoleFilling_alpha_le_half_exponent hd hEll
  have hrone : r ≤ 1 := by linarith only [hrhalf]
  have hpow : r ^ β ≤ r ^ (2 * α) :=
    Real.rpow_le_rpow_of_exponent_ge hr hrone (by linarith only [hα])
  have hBrU : euclideanBall (0 : Vec d) r ⊆
      euclideanBall (0 : Vec d) 1 :=
    euclideanBall_mono hr.le hrone
  have hgradEnergy := setIntegral_vecNormSq_le_coefficientEnergy_div
    hEll u.gradMemL2 (measurableSet_euclideanBall (0 : Vec d) r)
      hBrU (by norm_num : (0 : ℝ) < 1)
  have hBallEnergy := coefficientEnergy_ball_decay hd hEll hsol hr hrhalf
  have hraw : G ≤ D * Λ * r ^ β * I := by
    calc
      G ≤ ∫ x in euclideanBall (0 : Vec d) r,
          vecDot (u.grad x) (matVecMul (a x) (u.grad x)) := by
        simpa only [G, div_one] using hgradEnergy
      _ ≤ D * Λ * r ^ β * I := by
        simpa only [D, β, I] using hBallEnergy
  have hraw2 : G ≤ C ^ 2 * Λ * r ^ (2 * α) * I := by
    calc
      G ≤ D * Λ * r ^ β * I := hraw
      _ ≤ C ^ 2 * Λ * r ^ β * I := by gcongr
      _ ≤ C ^ 2 * Λ * r ^ (2 * α) * I := by gcongr
  have hpowSq : (r ^ α) ^ 2 = r ^ (2 * α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    congr 1
    ring
  have hRhsSq :
      (C * Real.sqrt Λ * r ^ α * Real.sqrt I) ^ 2 =
        C ^ 2 * Λ * r ^ (2 * α) * I := by
    rw [mul_pow, mul_pow, mul_pow,
      Real.sq_sqrt hΛ.le, Real.sq_sqrt hI, hpowSq]
  have hRhsNonneg : 0 ≤ C * Real.sqrt Λ * r ^ α * Real.sqrt I := by
    positivity
  change Real.sqrt G ≤ C * Real.sqrt Λ * r ^ α * Real.sqrt I
  rw [← hRhsSq] at hraw2
  exact (Real.sqrt_le_sqrt hraw2).trans_eq (Real.sqrt_sq hRhsNonneg)

end PDE
