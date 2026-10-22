module

public import PDEFoundation.Euler.TorusBasic
public import PDEFoundation.Euler.TorusFubini
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Periodic integration by parts on the unit cube

For `C¹` torus-periodic `F`, `∫_{torusCube} ∂_j F = 0`; hence `∫ ∂_j f · g = -∫ f · ∂_j g`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

theorem insertNth_eq_add (j : Fin 2) (t : ℝ) (z : Vec 1) :
    (j.insertNth t z : Vec 2) = (j.insertNth 0 z : Vec 2) + t • basisVec j := by
  ext k
  obtain rfl | ⟨k', rfl⟩ := j.eq_self_or_eq_succAbove k
  · simp [basisVec_apply]
  · simp [basisVec_apply, Fin.succAbove_ne]

/-- `∫_{torusCube} ∂_j F = 0` for `C¹` periodic `F`. -/
theorem integral_cube_fderiv_basisVec {F : Vec 2 → ℝ} (hF : ContDiff ℝ 1 F)
    (hp : IsTorusPeriodic F) (j : Fin 2) :
    ∫ x in torusCube, fderiv ℝ F x (basisVec j) = 0 := by
  have hdiff : Differentiable ℝ F := hF.differentiable one_ne_zero
  have hc : Continuous fun x => fderiv ℝ F x (basisVec j) :=
    ((hF.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have hI : IntegrableOn (fun x => fderiv ℝ F x (basisVec j)) torusCube :=
    hc.integrableOn_Icc
  unfold torusCube
  rw [setIntegral_cube_peel (n := 1) j hI]
  have inner : ∀ z : Vec 1,
      ∫ t in Icc (0 : ℝ) 1, fderiv ℝ F (j.insertNth t z : Vec 2) (basisVec j) = 0 := by
    intro z
    set x0 : Vec 2 := j.insertNth 0 z with hx0
    have hpath : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x0 + t • basisVec j) (basisVec j) t := by
      intro t
      simpa using ((hasDerivAt_id t).smul_const (basisVec j)).const_add x0
    have hder : ∀ t : ℝ, HasDerivAt (fun t : ℝ => F (x0 + t • basisVec j))
        (fderiv ℝ F (x0 + t • basisVec j) (basisVec j)) t := fun t =>
      (hdiff (x0 + t • basisVec j)).hasFDerivAt.comp_hasDerivAt t (hpath t)
    have hcont : Continuous fun t : ℝ => fderiv ℝ F (x0 + t • basisVec j) (basisVec j) :=
      hc.comp (by fun_prop)
    have e1 : ∫ t in Icc (0 : ℝ) 1, fderiv ℝ F (j.insertNth t z : Vec 2) (basisVec j)
        = ∫ t in Icc (0 : ℝ) 1, fderiv ℝ F (x0 + t • basisVec j) (basisVec j) := by
      congr 1; funext t; rw [insertNth_eq_add j t z]
    rw [e1, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t)
        (hcont.intervalIntegrable _ _)]
    simp only [one_smul, zero_smul, add_zero]
    rw [hp j x0, sub_self]
  simp [inner]

/-- **Periodic integration by parts on the cube** for `C¹` periodic real functions. -/
theorem torus_integral_by_parts {f g : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfp : IsTorusPeriodic f) (hgp : IsTorusPeriodic g) (j : Fin 2) :
    ∫ x in torusCube, fderiv ℝ f x (basisVec j) * g x =
      -∫ x in torusCube, f x * fderiv ℝ g x (basisVec j) := by
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hc1 : Continuous fun x => fderiv ℝ f x (basisVec j) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hc2 : Continuous fun x => fderiv ℝ g x (basisVec j) :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hF : ContDiff ℝ 1 fun x => f x * g x := ContDiff.mul hf hg
  have hFp : IsTorusPeriodic fun x => f x * g x := hfp.mul hgp
  have h0 := integral_cube_fderiv_basisVec hF hFp j
  have hderiv : ∀ x, fderiv ℝ (fun x => f x * g x) x (basisVec j) =
      fderiv ℝ f x (basisVec j) * g x + f x * fderiv ℝ g x (basisVec j) := by
    intro x
    rw [fderiv_fun_mul (hfd x) (hgd x)]
    simp only [add_apply, smul_apply, smul_eq_mul]; ring
  simp only [hderiv] at h0
  have i1 : IntegrableOn (fun x => fderiv ℝ f x (basisVec j) * g x) torusCube :=
    (hc1.mul hg.continuous).integrableOn_Icc
  have i2 : IntegrableOn (fun x => f x * fderiv ℝ g x (basisVec j)) torusCube :=
    (hf.continuous.mul hc2).integrableOn_Icc
  rw [integral_add i1 i2] at h0
  linarith

end PDE
