module

public import EllipticRegularity.Energy.CubeHoleFilling
public import PDEFoundation.Analysis.DyadicOscillationWeights

/-! # Dyadic and arbitrary-radius coefficient-energy decay on cubes -/

@[expose] public section

namespace PDE

open MeasureTheory

private theorem cubeHoleFillingK_ge_one
    {d : ℕ} {Λ : ℝ} {U : Set (Vec d)} {a : CoeffField d}
    (hEll : IsEllipticFieldOn 1 Λ U a) {x : Vec d} (hx : x ∈ U) :
    1 ≤ cubeHoleFillingK d Λ := by
  have hΛ : (1 : ℝ) ≤ Λ := (hEll.elliptic hx).lam_le_Lam
  have hsqrt : 1 ≤ Real.sqrt Λ := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hΛ
  have hF := cubeHoleFillingFactor_ge_one d
  calc
    (1 : ℝ) = 1 * 1 := by ring
    _ ≤ cubeHoleFillingFactor d * Real.sqrt Λ :=
      mul_le_mul hF hsqrt (by norm_num) (by linarith only [hF])
    _ = cubeHoleFillingK d Λ := rfl

private theorem dyadic_factor_eq_radius_ratio_cube
    {R : ℝ} (hR : 0 < R) (β : ℝ) (n : ℕ) :
    (2 : ℝ) ^ (-β * (n : ℝ)) =
      (dyadicRadius R n / R) ^ β := by
  have hRn : 0 ≤ dyadicRadius R n := (dyadicRadius_pos hR n).le
  have hRβ : 0 < R ^ β := Real.rpow_pos_of_pos hR _
  have hpow := dyadicRadius_rpow_eq hR β n
  rw [Real.div_rpow hRn hR.le, hpow]
  have hpow2 : ((2 : ℝ) ^ (-β)) ^ n =
      (2 : ℝ) ^ (-β * (n : ℝ)) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hpow2]
  field_simp

/-- Exact iterated contraction of coefficient energy on dyadic open cubes. -/
theorem cube_hole_filling_iterate
    {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} {U : Set (Vec d)}
    {a : CoeffField d} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U) (x₀ : Vec d) {R : ℝ}
    (hR : 0 < R) (houter : centeredAxisCube x₀ R ⊆ U)
    (hEll : IsEllipticFieldOn 1 Λ U a)
    (hsol : IsWeakDivergenceFormHarmonicOn a U u) (n : ℕ) :
    (∫ x in centeredAxisCube x₀ (dyadicRadius R n),
      vecDot (u.grad x) (matVecMul (a x) (u.grad x))) ≤
      holeFillingRatio (cubeHoleFillingK d Λ) ^ n *
        (∫ x in centeredAxisCube x₀ R,
          vecDot (u.grad x) (matVecMul (a x) (u.grad x))) := by
  let energy : Vec d → ℝ :=
    fun x => vecDot (u.grad x) (matVecMul (a x) (u.grad x))
  let E : ℕ → ℝ := fun m =>
    ∫ x in centeredAxisCube x₀ (dyadicRadius R m), energy x
  have hstep : ∀ m, E (m + 1) ≤
      holeFillingRatio (cubeHoleFillingK d Λ) * E m := by
    intro m
    have hrm : 0 < dyadicRadius R (m + 1) := dyadicRadius_pos hR _
    have hmR : dyadicRadius R m ≤ R := dyadicRadius_le hR.le _
    have heq : 2 * dyadicRadius R (m + 1) = dyadicRadius R m := by
      rw [dyadicRadius_succ]
      ring
    have houterm : centeredAxisCube x₀
        (2 * dyadicRadius R (m + 1)) ⊆ U := by
      rw [heq]
      exact (centeredAxisCube_mono x₀ hmR).trans houter
    have hone := cube_hole_filling_contraction hd hU x₀ hrm
      houterm hEll hsol
    have hboundary :
        (∫ x in centeredAxisCube x₀ (dyadicRadius R (m + 1)), energy x) =
          ∫ x in closedCenteredAxisCube x₀ (dyadicRadius R (m + 1)),
            energy x :=
      setIntegral_congr_set
        (centeredAxisCube_ae_eq_closedCenteredAxisCube x₀ _)
    dsimp only [E]
    rw [hboundary]
    simpa only [energy, heq] using hone
  have hiter := iterate_contraction
    (holeFillingRatio_nonneg (cubeHoleFillingK_nonneg d Λ)) hstep n
  simpa only [E, energy, dyadicRadius_zero] using hiter

/-- Dyadic power-law decay of coefficient energy with exponent
`β = 1/(K+1)`. -/
theorem cube_hole_filling_dyadic_decay
    {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} {U : Set (Vec d)}
    {a : CoeffField d} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U) (x₀ : Vec d) {R : ℝ}
    (hR : 0 < R) (houter : centeredAxisCube x₀ R ⊆ U)
    (hEll : IsEllipticFieldOn 1 Λ U a)
    (hsol : IsWeakDivergenceFormHarmonicOn a U u) (n : ℕ) :
    (∫ x in centeredAxisCube x₀ (dyadicRadius R n),
      vecDot (u.grad x) (matVecMul (a x) (u.grad x))) ≤
      (2 : ℝ) ^
          (-holeFillingDyadicExponent (cubeHoleFillingK d Λ) * (n : ℝ)) *
        (∫ x in centeredAxisCube x₀ R,
          vecDot (u.grad x) (matVecMul (a x) (u.grad x))) := by
  have hE0 : 0 ≤ (∫ x in centeredAxisCube x₀ R,
      vecDot (u.grad x) (matVecMul (a x) (u.grad x))) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem
      (isOpen_centeredAxisCube x₀ R).measurableSet] with x hx
    exact (vecNormSq_nonneg (u.grad x)).trans
      (by simpa only [one_mul] using
        ((hEll.elliptic (houter hx)).coercive (u.grad x)))
  calc
    _ ≤ holeFillingRatio (cubeHoleFillingK d Λ) ^ n *
        (∫ x in centeredAxisCube x₀ R,
          vecDot (u.grad x) (matVecMul (a x) (u.grad x))) :=
      cube_hole_filling_iterate hd hU x₀ hR houter hEll hsol n
    _ ≤ (2 : ℝ) ^
          (-holeFillingDyadicExponent (cubeHoleFillingK d Λ) * (n : ℝ)) *
        (∫ x in centeredAxisCube x₀ R,
          vecDot (u.grad x) (matVecMul (a x) (u.grad x))) :=
      mul_le_mul_of_nonneg_right
        (holeFillingRatio_pow_le_dyadicPower
          (cubeHoleFillingK_nonneg d Λ) n) hE0

/-- Coefficient energy decays on every concentric cube radius with an
explicit factor `2` and the named dyadic exponent. -/
theorem cube_hole_filling_decay
    {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} {U : Set (Vec d)}
    {a : CoeffField d} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U) (x₀ : Vec d) {R ρ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hρR : ρ ≤ R)
    (houter : centeredAxisCube x₀ R ⊆ U)
    (hEll : IsEllipticFieldOn 1 Λ U a)
    (hsol : IsWeakDivergenceFormHarmonicOn a U u) :
    (∫ x in centeredAxisCube x₀ ρ,
      vecDot (u.grad x) (matVecMul (a x) (u.grad x))) ≤
      2 * (ρ / R) ^
          (holeFillingDyadicExponent (cubeHoleFillingK d Λ)) *
        (∫ x in centeredAxisCube x₀ R,
          vecDot (u.grad x) (matVecMul (a x) (u.grad x))) := by
  let β := holeFillingDyadicExponent (cubeHoleFillingK d Λ)
  let energy : Vec d → ℝ :=
    fun x => vecDot (u.grad x) (matVecMul (a x) (u.grad x))
  obtain ⟨n, hnlow, hnhigh⟩ := exists_dyadicRadius_bracket hR hρ hρR
  let t := dyadicRadius R n
  have ht : 0 < t := dyadicRadius_pos hR n
  have htR : t ≤ R := dyadicRadius_le hR.le n
  have hρt : ρ ≤ t := hnhigh
  have ht2ρ : t < 2 * ρ := by
    have hh := hnlow
    rw [dyadicRadius_succ] at hh
    dsimp only [t]
    linarith only [hh]
  have htU : centeredAxisCube x₀ t ⊆ U :=
    (centeredAxisCube_mono x₀ htR).trans houter
  have henergy : IntegrableOn energy (centeredAxisCube x₀ t) :=
    (integrableOn_coefficientEnergy_of_isEllipticFieldOn hEll u.gradMemL2).mono_set
      htU
  have hnonneg : 0 ≤ᵐ[volume.restrict (centeredAxisCube x₀ t)] energy := by
    filter_upwards [ae_restrict_mem
      (isOpen_centeredAxisCube x₀ t).measurableSet] with x hx
    exact (vecNormSq_nonneg (u.grad x)).trans
      (by simpa only [one_mul] using
        ((hEll.elliptic (htU hx)).coercive (u.grad x)))
  have hmono : (∫ x in centeredAxisCube x₀ ρ, energy x) ≤
      ∫ x in centeredAxisCube x₀ t, energy x :=
    setIntegral_mono_set henergy hnonneg
      (Filter.Eventually.of_forall (centeredAxisCube_mono x₀ hρt))
  have hβ : 0 < β := holeFillingDyadicExponent_pos
    (cubeHoleFillingK_nonneg d Λ)
  have hβone : β ≤ 1 := holeFillingDyadicExponent_le_one
    (cubeHoleFillingK_nonneg d Λ)
  have hdyadic := cube_hole_filling_dyadic_decay
    hd hU x₀ hR houter hEll hsol n
  have hE0 : 0 ≤ (∫ x in centeredAxisCube x₀ R, energy x) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem
      (isOpen_centeredAxisCube x₀ R).measurableSet] with x hx
    exact (vecNormSq_nonneg (u.grad x)).trans
      (by simpa only [one_mul] using
        ((hEll.elliptic (houter hx)).coercive (u.grad x)))
  have hscale : (2 : ℝ) ^ (-β * (n : ℝ)) ≤
      2 * (ρ / R) ^ β := by
    rw [dyadic_factor_eq_radius_ratio_cube hR β n]
    have hratio : t / R ≤ 2 * (ρ / R) := by
      apply (div_le_iff₀ hR).2
      calc
        t ≤ 2 * ρ := ht2ρ.le
        _ = 2 * (ρ / R) * R := by field_simp [hR.ne']
    calc
      (t / R) ^ β ≤ (2 * (ρ / R)) ^ β :=
        Real.rpow_le_rpow (div_nonneg ht.le hR.le) hratio hβ.le
      _ = (2 : ℝ) ^ β * (ρ / R) ^ β := by
        rw [Real.mul_rpow (by norm_num) (div_nonneg hρ.le hR.le)]
      _ ≤ 2 * (ρ / R) ^ β := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (div_nonneg hρ.le hR.le) _)
        calc
          (2 : ℝ) ^ β ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hβone
          _ = 2 := by norm_num
  calc
    (∫ x in centeredAxisCube x₀ ρ, energy x) ≤
        ∫ x in centeredAxisCube x₀ t, energy x := hmono
    _ ≤ (2 : ℝ) ^ (-β * (n : ℝ)) *
        (∫ x in centeredAxisCube x₀ R, energy x) := by
      simpa only [energy, t, β] using hdyadic
    _ ≤ 2 * (ρ / R) ^ β *
        (∫ x in centeredAxisCube x₀ R, energy x) :=
      mul_le_mul_of_nonneg_right hscale hE0

/-- The decay exponent has sharp-order lower bound in `Λ`, with
dimension-only constant `1/(2 cubeHoleFillingFactor d)`. -/
theorem cube_hole_filling_exponent_lowerBound
    {d : ℕ} {Λ : ℝ} {U : Set (Vec d)}
    {a : CoeffField d} (hEll : IsEllipticFieldOn 1 Λ U a)
    {x : Vec d} (hx : x ∈ U) :
    (1 / (2 * cubeHoleFillingFactor d)) * Λ ^ (-(1 / 2 : ℝ)) ≤
      holeFillingDyadicExponent (cubeHoleFillingK d Λ) := by
  have hK : 1 ≤ cubeHoleFillingK d Λ :=
    cubeHoleFillingK_ge_one hEll hx
  have hΛ : 0 < Λ := (hEll.elliptic hx).Lam_pos
  have hF : 0 < cubeHoleFillingFactor d :=
    lt_of_lt_of_le (by norm_num) (cubeHoleFillingFactor_ge_one d)
  have hBound := holeFillingDyadicExponent_mul_sqrt_lowerBound
    (C := cubeHoleFillingFactor d) (κ := Λ) hK
  have hpow : Λ ^ (-(1 / 2 : ℝ)) = (Real.sqrt Λ)⁻¹ := by
    rw [Real.rpow_neg hΛ.le, Real.sqrt_eq_rpow]
  rw [hpow]
  change (1 / (2 * cubeHoleFillingFactor d)) * (Real.sqrt Λ)⁻¹ ≤
    holeFillingDyadicExponent
      (cubeHoleFillingFactor d * Real.sqrt Λ)
  convert hBound using 1
  field_simp [hF.ne', (Real.sqrt_pos.2 hΛ).ne']

end PDE
