module

public import PDEFoundation.Ambient.CoefficientField
public import PDEFoundation.Ambient.EuclideanNorm

/-!
# Pointwise energy bounds for the Meyers estimate

For `e · a e ≥ |e|²` and the upper ellipticity constant `Λ`, the square root
`w = (e · a e)^{1/2}` of the energy density satisfies
`|e| ≤ w`, `|a e| ≤ Λ^{1/2} w`, and `w ≤ Λ^{1/2} |e|`
(equation 4.17).
-/

@[expose] public section

namespace PDE.MeyersRH

/-- The square root of the energy density `e · A e`. -/
noncomputable def energyRoot {d : ℕ} (A : Mat d) (e : Vec d) : ℝ :=
  Real.sqrt (vecDot e (matVecMul A e))

variable {d : ℕ} {Λ : ℝ} {A : Mat d}

theorem energyRoot_nonneg (A : Mat d) (e : Vec d) : 0 ≤ energyRoot A e :=
  Real.sqrt_nonneg _

theorem energyRoot_sq (hA : IsEllipticMatrix 1 Λ A) (e : Vec d) :
    energyRoot A e ^ 2 = vecDot e (matVecMul A e) := by
  have h : 0 ≤ vecDot e (matVecMul A e) := by
    have := hA.coercive e
    linarith [vecNormSq_nonneg e]
  exact Real.sq_sqrt h

/-- `|e| ≤ w`. -/
theorem vecEuclideanNorm_le_energyRoot (hA : IsEllipticMatrix 1 Λ A) (e : Vec d) :
    vecEuclideanNorm e ≤ energyRoot A e := by
  apply le_of_sq_le_sq _ (energyRoot_nonneg A e)
  rw [vecEuclideanNorm_sq, energyRoot_sq hA]
  simpa using hA.coercive e

/-- `|A e| ≤ Λ^{1/2} w`. -/
theorem vecEuclideanNorm_matVecMul_le_energyRoot (hA : IsEllipticMatrix 1 Λ A)
    (e : Vec d) :
    vecEuclideanNorm (matVecMul A e) ≤ Real.sqrt Λ * energyRoot A e := by
  apply le_of_sq_le_sq _ (mul_nonneg (Real.sqrt_nonneg _) (energyRoot_nonneg A e))
  rw [vecEuclideanNorm_sq, mul_pow, Real.sq_sqrt hA.Lam_pos.le, energyRoot_sq hA]
  exact vecNormSq_matVecMul_le_mul_vecDot_of_isEllipticMatrix hA e

/-- `w ≤ Λ^{1/2} |e|`. -/
theorem energyRoot_le_sqrt_mul_vecEuclideanNorm (hA : IsEllipticMatrix 1 Λ A)
    (e : Vec d) :
    energyRoot A e ≤ Real.sqrt Λ * vecEuclideanNorm e := by
  have h1 := vecEuclideanNorm_matVecMul_le_energyRoot hA e
  have hcs : vecDot e (matVecMul A e) ≤
      vecEuclideanNorm e * vecEuclideanNorm (matVecMul A e) :=
    (le_abs_self _).trans (abs_vecDot_le_vecEuclideanNorm_mul e (matVecMul A e))
  have hw := energyRoot_sq hA e
  have hw0 := energyRoot_nonneg A e
  have hE := vecEuclideanNorm_nonneg e
  have hS := Real.sqrt_nonneg Λ
  apply le_of_sq_le_sq _ (mul_nonneg hS hE)
  rw [mul_pow, Real.sq_sqrt hA.Lam_pos.le, vecEuclideanNorm_sq]
  by_cases hz : energyRoot A e = 0
  · rw [hz]
    exact mul_nonneg hA.Lam_pos.le (vecNormSq_nonneg e) |>.trans_eq' (by norm_num)
  · have hpos : 0 < energyRoot A e := lt_of_le_of_ne hw0 (Ne.symm hz)
    have : energyRoot A e ^ 2 ≤ vecEuclideanNorm e * (Real.sqrt Λ * energyRoot A e) := by
      rw [hw]
      exact hcs.trans (mul_le_mul_of_nonneg_left h1 hE)
    have h2 : energyRoot A e ≤ vecEuclideanNorm e * Real.sqrt Λ := by
      nlinarith
    have h3 : energyRoot A e ^ 2 ≤ (vecEuclideanNorm e * Real.sqrt Λ) ^ 2 :=
      pow_le_pow_left₀ hw0 h2 2
    calc energyRoot A e ^ 2 ≤ (vecEuclideanNorm e * Real.sqrt Λ) ^ 2 := h3
      _ = Λ * vecNormSq e := by
        rw [mul_pow, Real.sq_sqrt hA.Lam_pos.le, vecEuclideanNorm_sq]; ring

end PDE.MeyersRH
