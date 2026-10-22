module

public import PDEFoundation.Analysis.RadialCoefficientFlux
public import PDEFoundation.Analysis.RadialVectorDivergence

/-!
# Divergence of radial coefficient fluxes
-/

@[expose] public section

open scoped BigOperators

namespace PDE

private theorem vecNormSq_rpow_half_eq_vecEuclideanNorm_rpow
    {d : ℕ} (x : Vec d) (c : ℝ) :
    (vecNormSq x) ^ (c / 2) = (vecEuclideanNorm x) ^ c := by
  rw [← vecEuclideanNorm_sq]
  have hn : 0 ≤ vecEuclideanNorm x := vecEuclideanNorm_nonneg x
  rw [← Real.rpow_natCast_mul hn 2 (c / 2)]
  congr 1
  ring

private theorem radialCoefficientFlux_eq_radialVectorField_of_ne
    {d : ℕ} (delta : ℝ) (k : Fin d) (β : ℝ) (x : Vec d) (hx : x ≠ 0) :
    radialCoefficientFlux delta k β x =
      radialVectorField (1 - delta) ((1 + delta) * β - (1 - delta))
        ((β - 1) / 2) k x := by
  rw [radialCoefficientFlux_eq]
  have hq : 0 < vecNormSq x :=
    lt_of_le_of_ne (vecNormSq_nonneg x)
      (Ne.symm (fun h => hx (vecNormSq_eq_zero h)))
  have hp : Real.rpow (vecNormSq x) ((β - 1) / 2) =
      Real.rpow (vecEuclideanNorm x) (β - 1) := by
    exact vecNormSq_rpow_half_eq_vecEuclideanNorm_rpow x (β - 1)
  have hm : (vecNormSq x) ^ ((β - 1) / 2 - 1) =
      (vecNormSq x) ^ ((β - 1) / 2) / vecNormSq x := by
    rw [Real.rpow_sub_one hq.ne' ((β - 1) / 2)]
  ext i
  simp only [radialVectorField, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    basisVec_apply]
  rw [← hp, hm]
  simp only [Real.rpow_eq_pow]
  ring

/-- The divergence of the literal radial coefficient flux, away from the
origin. -/
theorem sum_classicalGradient_radialCoefficientFlux
    {d : ℕ} (delta : ℝ) (k : Fin d) (β : ℝ) (x : Vec d) (hx : x ≠ 0) :
    (∑ i : Fin d,
      classicalGradient (fun y : Vec d => radialCoefficientFlux delta k β y i)
        x i) =
      ((1 - delta) * (β - 1) +
          ((1 + delta) * β - (1 - delta)) * (β + (d : ℝ) - 2)) *
        x k * (vecEuclideanNorm x) ^ (β - 3) := by
  let a : ℝ := 1 - delta
  let b : ℝ := (1 + delta) * β - (1 - delta)
  let s : ℝ := (β - 1) / 2
  have hfun (i : Fin d) :
      (fun y : Vec d => radialCoefficientFlux delta k β y i) =ᶠ[nhds x]
        fun y => radialVectorField a b s k y i := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact congrFun (radialCoefficientFlux_eq_radialVectorField_of_ne
      delta k β y hy) i
  have hgrad (i : Fin d) :
      classicalGradient (fun y : Vec d => radialCoefficientFlux delta k β y i) x =
        classicalGradient (fun y : Vec d => radialVectorField a b s k y i) x := by
    funext j
    rw [classicalGradient_apply, classicalGradient_apply, (hfun i).fderiv_eq]
  simp_rw [hgrad]
  rw [sum_classicalGradient_radialVectorField_component a b s k x hx]
  dsimp only [a, b, s]
  have hpow : (vecNormSq x) ^ ((β - 1) / 2 - 1) =
      (vecEuclideanNorm x) ^ (β - 3) := by
    rw [show (β - 1) / 2 - 1 = (β - 3) / 2 by ring]
    exact vecNormSq_rpow_half_eq_vecEuclideanNorm_rpow x (β - 3)
  rw [hpow]
  ring

/-- In dimension two, the divergence coefficient reduces to its quadratic
indicial polynomial. -/
theorem sum_classicalGradient_radialCoefficientFlux_fin_two
    (delta : ℝ) (k : Fin 2) (β : ℝ) (x : Vec 2) (hx : x ≠ 0) :
    (∑ i : Fin 2,
      classicalGradient (fun y : Vec 2 => radialCoefficientFlux delta k β y i)
        x i) =
      ((1 + delta) * β ^ 2 - (1 - delta)) *
        x k * (vecEuclideanNorm x) ^ (β - 3) := by
  rw [sum_classicalGradient_radialCoefficientFlux delta k β x hx]
  congr 1
  ring

/-- The planar radial mode with the indicial exponent has divergence zero away
from the origin. -/
theorem sum_classicalGradient_radialCoefficientFlux_sqrt_eq_zero
    (delta : ℝ) (hdelta0 : 0 ≤ delta) (hdelta1 : delta < 1)
    (k : Fin 2) (x : Vec 2) (hx : x ≠ 0) :
    (∑ i : Fin 2,
      classicalGradient
        (fun y : Vec 2 =>
          radialCoefficientFlux delta k
            (Real.sqrt ((1 - delta) / (1 + delta))) y i) x i) = 0 := by
  rw [sum_classicalGradient_radialCoefficientFlux_fin_two delta k _ x hx]
  have hden : 0 < 1 + delta := by linarith
  have hratio : 0 ≤ (1 - delta) / (1 + delta) :=
    div_nonneg (by linarith) hden.le
  rw [Real.sq_sqrt hratio]
  have hne : (1 + delta) ≠ 0 := ne_of_gt hden
  have hcoef : (1 + delta) * ((1 - delta) / (1 + delta)) -
      (1 - delta) = 0 := by
    field_simp
    ring
  rw [hcoef]
  simp only [zero_mul]

end PDE
