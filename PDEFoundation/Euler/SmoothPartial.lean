module

public import PDEFoundation.Euler.TorusBasic
public import PDEFoundation.Euler.TorusParts
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Partial derivatives of smooth periodic functions on `Vec 2`

`pd j f = ∂_j f`, with smoothness, periodicity, linearity and symmetry of mixed partials.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

/-- The partial derivative `∂_j f` of a function on `Vec 2`. -/
noncomputable def pd (j : Fin 2) (f : Vec 2 → ℝ) : Vec 2 → ℝ :=
  fun x => fderiv ℝ f x (basisVec j)

theorem pd_def (j : Fin 2) (f : Vec 2 → ℝ) (x : Vec 2) : pd j f x = fderiv ℝ f x (basisVec j) :=
  rfl

theorem contDiff_pd {f : Vec 2 → ℝ} {n : ℕ} (hf : ContDiff ℝ (n + 1 : ℕ) f) (j : Fin 2) :
    ContDiff ℝ n (PDE.pd j f) := by
  unfold PDE.pd
  exact (hf.fderiv_right (m := n) (by norm_cast)).clm_apply contDiff_const

theorem contDiff_pd_top {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (PDE.pd j f) := by
  unfold PDE.pd
  exact (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

theorem IsTorusPeriodic.pd {f : Vec 2 → ℝ} (hf : IsTorusPeriodic f) (j : Fin 2) :
    IsTorusPeriodic (pd j f) := by
  intro i x
  unfold PDE.pd
  have h : (fun y => f (y + basisVec i)) = f := funext fun y => hf i y
  have := fderiv_comp_add_right (𝕜 := ℝ) (f := f) (basisVec i) (x := x)
  rw [h] at this
  rw [← this]

theorem pd_add {f g : Vec 2 → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (j : Fin 2) :
    pd j (fun x => f x + g x) = fun x => pd j f x + pd j g x := by
  funext x
  simp only [PDE.pd]
  rw [fderiv_fun_add (hf x) (hg x)]
  rfl

theorem pd_sub {f g : Vec 2 → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (j : Fin 2) :
    pd j (fun x => f x - g x) = fun x => pd j f x - pd j g x := by
  funext x
  simp only [PDE.pd]
  rw [fderiv_fun_sub (hf x) (hg x)]
  rfl

theorem pd_neg {f : Vec 2 → ℝ} (j : Fin 2) :
    pd j (fun x => -f x) = fun x => -pd j f x := by
  funext x
  simp only [PDE.pd]
  rw [fderiv_fun_neg]
  rfl

theorem pd_zero (j : Fin 2) : pd j (fun _ => (0 : ℝ)) = fun _ => 0 := by
  funext x; simp [PDE.pd]

/-- Symmetry of mixed second partials for `C²` functions. -/
theorem pd_comm {f : Vec 2 → ℝ} (hf : ContDiff ℝ 2 f) (j k : Fin 2) :
    pd j (pd k f) = pd k (pd j f) := by
  funext x
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) x
  have key : ∀ a b : Fin 2, pd a (pd b f) x = fderiv ℝ (fderiv ℝ f) x (basisVec a) (basisVec b) := by
    intro a b
    simp only [PDE.pd]
    have : fderiv ℝ (fun y => fderiv ℝ f y (basisVec b)) x =
        (ContinuousLinearMap.apply ℝ ℝ (basisVec b)).comp (fderiv ℝ (fderiv ℝ f) x) :=
      by
        rw [fderiv_clm_apply hd (differentiableAt_const _)]
        ext v
        simp
    show fderiv ℝ (fun y => fderiv ℝ f y (basisVec b)) x (basisVec a) = _
    rw [this]; rfl
  rw [key, key]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)) _ _

end PDE
