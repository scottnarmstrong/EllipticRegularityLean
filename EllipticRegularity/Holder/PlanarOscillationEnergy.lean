module

public import EllipticRegularity.Energy.CoefficientEnergyCaccioppoli
public import PDEFoundation.Geometry.EuclideanBall.Interior

/-! # Initial planar square energy from unit-ball L² mass -/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

/-- The fixed root square lies within the unit ball at every center in the
three-quarter ball. -/
theorem centeredAxisCube_one_thirtysecond_subset_unit
    (x : Vec 2) (hx : x ∈ euclideanBall (0 : Vec 2) (3 / 4)) :
    centeredAxisCube x (1 / 32) ⊆ euclideanBall (0 : Vec 2) 1 := by
  have hxnorm : vecEuclideanNorm (x - (0 : Vec 2)) < 3 / 4 :=
    (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).1 hx
  have hball : euclideanBall x (1 / 4) ⊆
      euclideanBall (0 : Vec 2) 1 := by
    apply euclideanBall_subset_of_center_norm_add_le
      (by norm_num) (by norm_num)
    linarith only [hxnorm]
  have hsqrt : Real.sqrt (2 : ℕ) ≤ 2 := by
    have hsq : Real.sqrt (2 : ℕ) ^ 2 = 2 := by norm_num
    nlinarith [Real.sqrt_nonneg (2 : ℕ)]
  have hrad : 2 * Real.sqrt (2 : ℕ) * (1 / 32 : ℝ) ≤ 1 / 4 := by
    calc
      _ ≤ 2 * 2 * (1 / 32 : ℝ) := by gcongr
      _ ≤ 1 / 4 := by norm_num
  exact (centeredAxisCube_subset_euclideanBall
    (by norm_num : 0 < 2) x (by norm_num : (0 : ℝ) < 1 / 32)).trans
      ((euclideanBall_mono (by positivity) hrad).trans hball)

/-- A square of half-side `1/32` centered in the three-quarter unit ball has
normalized coefficient energy at most `262144 Λ` times the unit-ball L² mass. -/
theorem coefficientEnergy_centeredAxisCube_one_thirtysecond_le
    {Lam : ℝ} {a : CoeffField 2}
    {u : H1Function (euclideanBall (0 : Vec 2) 1)}
    (x : Vec 2) (hx : x ∈ euclideanBall (0 : Vec 2) (3 / 4))
    (hEll : IsEllipticFieldOn 1 Lam
      (euclideanBall (0 : Vec 2) 1) a)
    (hsol : IsWeakDivergenceFormHarmonicOn a
      (euclideanBall (0 : Vec 2) 1) u) :
    (∫ z in centeredAxisCube x (1 / 32),
      vecDot (u.grad z) (matVecMul (a z) (u.grad z))) ≤
      262144 * Lam *
        ∫ z in euclideanBall (0 : Vec 2) 1, (u z) ^ 2 := by
  let U : Set (Vec 2) := euclideanBall (0 : Vec 2) 1
  let B : Set (Vec 2) := euclideanBall x (1 / 8)
  let D : Set (Vec 2) := euclideanBall x (1 / 4)
  let Q : Set (Vec 2) := centeredAxisCube x (1 / 32)
  let energy : Vec 2 → ℝ :=
    fun z => vecDot (u.grad z) (matVecMul (a z) (u.grad z))
  have hxnorm : vecEuclideanNorm (x - (0 : Vec 2)) < 3 / 4 :=
    (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).1 hx
  have hDU : D ⊆ U := by
    dsimp only [D, U]
    apply euclideanBall_subset_of_center_norm_add_le
      (by norm_num) (by norm_num)
    linarith only [hxnorm]
  have hQBall : Q ⊆ B := by
    intro z hz
    have hcube := centeredAxisCube_subset_euclideanBall
      (by norm_num : 0 < 2) x (by norm_num : (0 : ℝ) < 1 / 32)
      (show z ∈ centeredAxisCube x (1 / 32) from hz)
    apply (euclideanBall_mono (by positivity : (0 : ℝ) ≤
      2 * Real.sqrt (2 : ℕ) * (1 / 32)) ?_) hcube
    have hsqrt : Real.sqrt (2 : ℕ) ≤ 2 := by
      have hsq : Real.sqrt (2 : ℕ) ^ 2 = 2 := by norm_num
      nlinarith [Real.sqrt_nonneg (2 : ℕ)]
    calc
      2 * Real.sqrt (2 : ℕ) * (1 / 32 : ℝ) ≤
          2 * 2 * (1 / 32 : ℝ) := by gcongr
      _ = 1 / 8 := by norm_num
  have hBU : B ⊆ U :=
    (euclideanBall_mono (by norm_num : (0 : ℝ) ≤ 1 / 8)
      (by norm_num : (1 / 8 : ℝ) ≤ 1 / 4)).trans hDU
  have hLam : 0 ≤ Lam := by
    have hxU : x ∈ U := hDU (center_mem_euclideanBall x (by norm_num))
    exact (hEll.elliptic hxU).Lam_pos.le
  have henergyInt : IntegrableOn energy U :=
    integrableOn_coefficientEnergy_of_isEllipticFieldOn hEll u.gradMemL2
  have henergyNonneg : 0 ≤ᵐ[volume.restrict B] energy := by
    filter_upwards [ae_restrict_mem (isOpen_euclideanBall x (1 / 8)).measurableSet]
      with z hz
    have hA := hEll.elliptic (hBU hz)
    exact (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1)
      (vecNormSq_nonneg (u.grad z))).trans (hA.coercive (u.grad z))
  have hQleB : (∫ z in Q, energy z) ≤ ∫ z in B, energy z :=
    setIntegral_mono_set (henergyInt.mono_set hBU)
      henergyNonneg (Filter.Eventually.of_forall fun z hz => hQBall hz)
  have hCacc := caccioppoli_coefficient_energy_on_inner
    (isOpenBoundedConvexDomain_euclideanBall (0 : Vec 2) (by norm_num))
    (isOpen_euclideanBall x (1 / 8)).measurableSet
    (isOpen_euclideanBall x (1 / 4)).measurableSet
    hEll (by norm_num : (0 : ℝ) < 1) hLam hsol
    (quantitativeBallCutoff x (r := 1 / 8) (R := 1 / 4)
      (by norm_num) (by norm_num)) hDU (k := 0)
  have hL2Int : IntegrableOn (fun z => (u z) ^ 2) U := by
    simpa only [pow_two] using
      integrableOn_mul_of_memL2On u.memL2 u.memL2
  have hL2D : (∫ z in D, (u z) ^ 2) ≤
      ∫ z in U, (u z) ^ 2 := by
    exact setIntegral_mono_set hL2Int
      (Filter.Eventually.of_forall fun z => sq_nonneg (u z))
      (Filter.Eventually.of_forall fun z hz => hDU hz)
  have hCacc' : (∫ z in B, energy z) ≤
      262144 * Lam * ∫ z in D, (u z) ^ 2 := by
    have hK : (32 / ((1 / 4 : ℝ) - 1 / 8)) = 256 := by norm_num
    simp only [div_one, sub_zero, hK] at hCacc
    convert hCacc using 1
    norm_num [pow_two]
    ring
  calc
    (∫ z in Q, energy z) ≤ ∫ z in B, energy z := hQleB
    _ ≤ 262144 * Lam * ∫ z in D, (u z) ^ 2 := hCacc'
    _ ≤ 262144 * Lam * ∫ z in U, (u z) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hL2D (mul_nonneg (by norm_num) hLam)

end

end PDE
