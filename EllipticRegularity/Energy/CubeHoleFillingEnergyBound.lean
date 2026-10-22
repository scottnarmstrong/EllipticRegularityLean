module

public import EllipticRegularity.Energy.CubeHoleFillingBall

/-! # Coefficient-energy decay on round balls from cube hole filling -/

@[expose] public section

namespace PDE

open MeasureTheory

/-- The explicit dimension-only factor for energy decay on round balls. -/
def cubeHoleFillingBallEnergyConst (d : ℕ) : ℝ :=
  65536 * ((d : ℝ) + 1)

/-- On the unit ball, coefficient energy decays with the cube hole-filling
exponent and a single factor of `Λ`. -/
theorem coefficientEnergy_ball_decay
    {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} {a : CoeffField d}
    {u : H1Function (euclideanBall (0 : Vec d) 1)}
    (hEll : IsEllipticFieldOn 1 Λ (euclideanBall (0 : Vec d) 1) a)
    (hsol : IsWeakDivergenceFormHarmonicOn a
      (euclideanBall (0 : Vec d) 1) u)
    {r : ℝ} (hr : 0 < r) (hrhalf : r ≤ 1 / 2) :
    (∫ x in euclideanBall (0 : Vec d) r,
      vecDot (u.grad x) (matVecMul (a x) (u.grad x))) ≤
      cubeHoleFillingBallEnergyConst d * Λ *
        r ^ (holeFillingDyadicExponent (cubeHoleFillingK d Λ)) *
        (∫ x in euclideanBall (0 : Vec d) 1, u x ^ 2) := by
  let R₀ := cubeHoleFillingRootRadius d
  let β := holeFillingDyadicExponent (cubeHoleFillingK d Λ)
  let E : Set (Vec d) → ℝ := fun S =>
    ∫ x in S, vecDot (u.grad x) (matVecMul (a x) (u.grad x))
  let I : ℝ := ∫ x in euclideanBall (0 : Vec d) 1, u x ^ 2
  have hR₀ : 0 < R₀ := cubeHoleFillingRootRadius_pos hd
  have hR₀half : R₀ ≤ 1 / 2 := cubeHoleFillingRootRadius_le_half hd
  have hBallHalfU : euclideanBall (0 : Vec d) (1 / 2) ⊆
      euclideanBall (0 : Vec d) 1 :=
    euclideanBall_mono (by norm_num) (by norm_num)
  have hrootHalf := rootCube_subset_halfBall hd
  have hrootU : centeredAxisCube (0 : Vec d) R₀ ⊆
      euclideanBall (0 : Vec d) 1 := hrootHalf.trans hBallHalfU
  have hΛ : 0 < Λ :=
    (hEll.elliptic (center_mem_euclideanBall (0 : Vec d)
      (by norm_num : (0 : ℝ) < 1))).Lam_pos
  have hI : 0 ≤ I := integral_nonneg_of_ae
    (Filter.Eventually.of_forall fun x => sq_nonneg (u x))
  have hβ : 0 < β :=
    holeFillingDyadicExponent_pos (cubeHoleFillingK_nonneg d Λ)
  have hβone : β ≤ 1 :=
    holeFillingDyadicExponent_le_one (cubeHoleFillingK_nonneg d Λ)
  have hsqrtd : 0 < Real.sqrt d := by
    exact Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < d))
  have hsqrtLE : Real.sqrt d ≤ (d : ℝ) + 1 := by
    have hdnonneg : (0 : ℝ) ≤ d := by positivity
    have hsq := Real.sq_sqrt hdnonneg
    nlinarith [sq_nonneg (Real.sqrt d - 1)]
  have hR₀ratio : (r / R₀) = 2 * Real.sqrt d * r := by
    dsimp [R₀, cubeHoleFillingRootRadius]
    field_simp [hsqrtd.ne']
  have hrootEnergy : E (centeredAxisCube (0 : Vec d) R₀) ≤
      E (euclideanBall (0 : Vec d) (1 / 2)) :=
    setIntegral_coefficientEnergy_mono hEll hrootHalf hBallHalfU
      (measurableSet_euclideanBall (0 : Vec d) (1 / 2))
  have hhalfEnergy : E (euclideanBall (0 : Vec d) (1 / 2)) ≤
      16384 * Λ * I :=
    coefficientEnergy_halfBall_le_unit_value_sq hEll hsol
  have hbase : 1 ≤ 2 * Real.sqrt d := by
    have hdone : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    have hsqrtone : 1 ≤ Real.sqrt d := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hdone
    nlinarith only [hsqrtone]
  have hbasePow : (2 * Real.sqrt d) ^ β ≤ 2 * Real.sqrt d := by
    calc
      (2 * Real.sqrt d) ^ β ≤ (2 * Real.sqrt d) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hbase hβone
      _ = 2 * Real.sqrt d := Real.rpow_one _
  have hrpow : 0 ≤ r ^ β := Real.rpow_nonneg hr.le _
  have hD : 0 ≤ cubeHoleFillingBallEnergyConst d := by
    unfold cubeHoleFillingBallEnergyConst
    positivity
  by_cases hsmall : r ≤ R₀
  · have hcubeU : centeredAxisCube (0 : Vec d) r ⊆
        euclideanBall (0 : Vec d) 1 :=
      (centeredAxisCube_mono 0 hsmall).trans hrootU
    have hBcube : euclideanBall (0 : Vec d) r ⊆
        centeredAxisCube (0 : Vec d) r :=
      euclideanBall_subset_centeredAxisCube 0 hr
    have hBr : E (euclideanBall (0 : Vec d) r) ≤
        E (centeredAxisCube (0 : Vec d) r) :=
      setIntegral_coefficientEnergy_mono hEll hBcube hcubeU
        (isOpen_centeredAxisCube 0 r).measurableSet
    have hdecay := cube_hole_filling_decay hd
      (isOpenBoundedConvexDomain_euclideanBall (0 : Vec d)
        (by norm_num : (0 : ℝ) < 1))
      (0 : Vec d) hR₀ hr hsmall hrootU hEll hsol
    have hscale : 2 * (r / R₀) ^ β ≤
        4 * Real.sqrt d * r ^ β := by
      rw [hR₀ratio, Real.mul_rpow (by positivity : 0 ≤ 2 * Real.sqrt d) hr.le]
      calc
        2 * ((2 * Real.sqrt d) ^ β * r ^ β) ≤
            2 * ((2 * Real.sqrt d) * r ^ β) := by
          gcongr
        _ = 4 * Real.sqrt d * r ^ β := by ring
    have hweight : 0 ≤ 16384 * Λ * I := by positivity
    calc
      E (euclideanBall (0 : Vec d) r) ≤
          E (centeredAxisCube (0 : Vec d) r) := hBr
      _ ≤ 2 * (r / R₀) ^ β *
          E (centeredAxisCube (0 : Vec d) R₀) := by
        simpa only [E, β] using hdecay
      _ ≤ 2 * (r / R₀) ^ β *
          E (euclideanBall (0 : Vec d) (1 / 2)) := by gcongr
      _ ≤ 2 * (r / R₀) ^ β * (16384 * Λ * I) := by gcongr
      _ ≤ (4 * Real.sqrt d * r ^ β) * (16384 * Λ * I) :=
        mul_le_mul_of_nonneg_right hscale hweight
      _ ≤ cubeHoleFillingBallEnergyConst d * Λ * r ^ β * I := by
        unfold cubeHoleFillingBallEnergyConst
        have hmul := mul_le_mul_of_nonneg_right hsqrtLE
          (mul_nonneg hΛ.le (mul_nonneg hrpow hI))
        nlinarith only [hmul]
  · have hR₀r : R₀ ≤ r := le_of_not_ge hsmall
    have hBrHalf : euclideanBall (0 : Vec d) r ⊆
        euclideanBall (0 : Vec d) (1 / 2) :=
      euclideanBall_mono hr.le hrhalf
    have hBr : E (euclideanBall (0 : Vec d) r) ≤
        E (euclideanBall (0 : Vec d) (1 / 2)) :=
      setIntegral_coefficientEnergy_mono hEll hBrHalf hBallHalfU
        (measurableSet_euclideanBall (0 : Vec d) (1 / 2))
    have hrone : r ≤ 1 := by linarith only [hrhalf]
    have hrpowge : r ≤ r ^ β := by
      simpa only [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_ge hr hrone hβone)
    have hscale : 1 ≤ 4 * ((d : ℝ) + 1) * r ^ β := by
      have hroot : 1 ≤ 4 * ((d : ℝ) + 1) * R₀ := by
        dsimp [R₀, cubeHoleFillingRootRadius]
        rw [show 4 * ((d : ℝ) + 1) * (1 / (2 * Real.sqrt d)) =
          (4 * ((d : ℝ) + 1)) / (2 * Real.sqrt d) by ring]
        apply (le_div_iff₀ (by positivity : 0 < 2 * Real.sqrt d)).2
        nlinarith only [hsqrtLE, hsqrtd]
      calc
        1 ≤ 4 * ((d : ℝ) + 1) * R₀ := hroot
        _ ≤ 4 * ((d : ℝ) + 1) * r := by gcongr
        _ ≤ 4 * ((d : ℝ) + 1) * r ^ β := by gcongr
    have hweight : 0 ≤ 16384 * Λ * I := by positivity
    calc
      E (euclideanBall (0 : Vec d) r) ≤
          E (euclideanBall (0 : Vec d) (1 / 2)) := hBr
      _ ≤ 16384 * Λ * I := hhalfEnergy
      _ ≤ (4 * ((d : ℝ) + 1) * r ^ β) *
          (16384 * Λ * I) := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hscale hweight
      _ = cubeHoleFillingBallEnergyConst d * Λ * r ^ β * I := by
        unfold cubeHoleFillingBallEnergyConst
        ring

end PDE
