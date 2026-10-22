/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.ParabolicDef
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! # Classical directional chain rules for parabolic coordinates -/

@[expose] public section

namespace PDE.Parabolic.Chain

open PDE

/-- The time derivative of a smooth scalar composition. -/
theorem parTimeDeriv_comp {d : ℕ} {F : ℝ → ℝ} {w : Vec d × ℝ → ℝ}
    (hF : ContDiff ℝ 1 F) (hw : ContDiff ℝ 1 w) (z : Vec d × ℝ) :
    parTimeDeriv (F ∘ w) z = deriv F (w z) * parTimeDeriv w z := by
  have hcomp : HasFDerivAt (F ∘ w)
      ((fderiv ℝ F (w z)).comp (fderiv ℝ w z)) z :=
    ((hF.differentiable (by norm_num) (w z)).hasFDerivAt).comp z
      ((hw.differentiable (by norm_num) z).hasFDerivAt)
  rw [parTimeDeriv, hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, fderiv_eq_deriv_mul, parTimeDeriv]

/-- The spatial coordinate derivatives of a smooth scalar composition. -/
theorem parSpaceGrad_comp {d : ℕ} {F : ℝ → ℝ} {w : Vec d × ℝ → ℝ}
    (hF : ContDiff ℝ 1 F) (hw : ContDiff ℝ 1 w) (z : Vec d × ℝ) :
    parSpaceGrad (F ∘ w) z = deriv F (w z) • parSpaceGrad w z := by
  ext i
  have hcomp : HasFDerivAt (F ∘ w)
      ((fderiv ℝ F (w z)).comp (fderiv ℝ w z)) z :=
    ((hF.differentiable (by norm_num) (w z)).hasFDerivAt).comp z
      ((hw.differentiable (by norm_num) z).hasFDerivAt)
  rw [parSpaceGrad, hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, fderiv_eq_deriv_mul, parSpaceGrad, Pi.smul_apply, smul_eq_mul]

/-- The time derivative of a product of smooth scalar fields. -/
theorem parTimeDeriv_mul {d : ℕ} {f g : Vec d × ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (z : Vec d × ℝ) :
    parTimeDeriv (fun y => f y * g y) z =
      parTimeDeriv f z * g z + f z * parTimeDeriv g z := by
  have hprod := ((hf.differentiable (by norm_num) z).hasFDerivAt).mul
      ((hg.differentiable (by norm_num) z).hasFDerivAt)
  change (fderiv ℝ (f * g) z) (0, 1) = _
  rw [hprod.fderiv]
  simp only [add_apply, smul_apply, parTimeDeriv]
  ring

/-- The spatial coordinate derivatives of a product of smooth scalar fields. -/
theorem parSpaceGrad_mul {d : ℕ} {f g : Vec d × ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (z : Vec d × ℝ) :
    parSpaceGrad (fun y => f y * g y) z =
      g z • parSpaceGrad f z + f z • parSpaceGrad g z := by
  ext i
  have hprod := ((hf.differentiable (by norm_num) z).hasFDerivAt).mul
      ((hg.differentiable (by norm_num) z).hasFDerivAt)
  change (fderiv ℝ (f * g) z) (basisVec i, 0) = _
  rw [hprod.fderiv]
  simp only [add_apply, smul_apply, parSpaceGrad, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The spatial Fréchet derivative of a scalar composition. -/
theorem vecFDeriv_comp {d : ℕ} {F : ℝ → ℝ} {w : Vec d → ℝ}
    (hF : ContDiff ℝ 1 F) (hw : ContDiff ℝ 1 w) (x e : Vec d) :
    fderiv ℝ (F ∘ w) x e = deriv F (w x) * fderiv ℝ w x e := by
  have hcomp : HasFDerivAt (F ∘ w)
      ((fderiv ℝ F (w x)).comp (fderiv ℝ w x)) x :=
    ((hF.differentiable (by norm_num) (w x)).hasFDerivAt).comp x
      ((hw.differentiable (by norm_num) x).hasFDerivAt)
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, fderiv_eq_deriv_mul]

/-- The spatial Fréchet derivative of a product in one direction. -/
theorem vecFDeriv_mul {d : ℕ} {f g : Vec d → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (x e : Vec d) :
    fderiv ℝ (fun y => f y * g y) x e =
      fderiv ℝ f x e * g x + f x * fderiv ℝ g x e := by
  have hprod := ((hf.differentiable (by norm_num) x).hasFDerivAt).mul
      ((hg.differentiable (by norm_num) x).hasFDerivAt)
  change (fderiv ℝ (f * g) x) e = _
  rw [hprod.fderiv]
  simp only [add_apply, smul_apply]
  ring

/-- A `C²` scalar function has a `C¹` first derivative. -/
theorem contDiff_deriv_of_two {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) :
    ContDiff ℝ 1 (deriv F) := by
  have hfd : ContDiff ℝ 1 (fderiv ℝ F) := by
    have h := (contDiff_succ_iff_fderiv (f := F) (n := (1 : WithTop ℕ∞))).mp hF
    exact h.2.2
  have h := hfd.clm_apply (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (1 : ℝ)))
  convert h using 1
  funext x
  exact (fderiv_apply_one_eq_deriv (f := F) (x := x)).symm

/-- The scalar correction whose time derivative converts the weak test
`F'(u) φ` into the renormalized test for `F(u)`. -/
noncomputable def renormalizationRemainder (F : ℝ → ℝ) (s : ℝ) : ℝ :=
  F s - s * deriv F s

/-- Derivative of the correction in the renormalization identity. -/
theorem deriv_renormalizationRemainder {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (s : ℝ) :
    deriv (renormalizationRemainder F) s = -s * deriv (deriv F) s := by
  have hF1 := contDiff_deriv_of_two hF
  change deriv (F - fun x => x * deriv F x) s = _
  rw [deriv_sub]
  · have hmul := (hasDerivAt_id s).mul
      ((hF1.differentiable (by norm_num) s).hasDerivAt)
    change deriv F s - deriv (id * deriv F) s = _
    rw [hmul.deriv]
    change deriv F s - (1 * deriv F s + s * deriv (deriv F) s) = _
    ring
  · exact (hF.differentiable (by norm_num) s)
  · exact (contDiff_id.mul hF1).differentiable (by norm_num) s

end PDE.Parabolic.Chain
