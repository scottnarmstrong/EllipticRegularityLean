module

public import PDEFoundation.Monotonicity.Poon.IdentitiesDom
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Coordinate-derivative rules and Gaussian integration by parts

Product, sum and coordinate rules for `euclideanCoordDeriv` on smooth functions, and the
whole-space Gaussian integration by parts
`∫ ∂ᵢ G Φ = (1 / (2 s)) ∫ xᵢ G Φ`, summed over `i` for a vector field.
-/

@[expose] public section

open MeasureTheory

namespace PDE

noncomputable section

variable {d : ℕ}

/-- Smoothness class used for the integration by parts. -/
abbrev Sm (f : Vec d → ℝ) : Prop := ContDiff ℝ (⊤ : ℕ∞) f

theorem Sm.differentiableAt {f : Vec d → ℝ} (hf : Sm f) (x : Vec d) : DifferentiableAt ℝ f x :=
  (hf.differentiable (by simp)) x

theorem Sm.coordDeriv {f : Vec d → ℝ} (hf : Sm f) (i : Fin d) : Sm (euclideanCoordDeriv i f) :=
  contDiff_euclideanCoordDeriv hf i

theorem coordDeriv_mul {f g : Vec d → ℝ} (hf : Sm f) (hg : Sm g) (i : Fin d) (x : Vec d) :
    euclideanCoordDeriv i (fun y => f y * g y) x =
      euclideanCoordDeriv i f x * g x + f x * euclideanCoordDeriv i g x := by
  unfold euclideanCoordDeriv
  rw [fderiv_fun_mul (hf.differentiableAt x) (hg.differentiableAt x)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem coordDeriv_add {f g : Vec d → ℝ} (hf : Sm f) (hg : Sm g) (i : Fin d) (x : Vec d) :
    euclideanCoordDeriv i (fun y => f y + g y) x =
      euclideanCoordDeriv i f x + euclideanCoordDeriv i g x := by
  unfold euclideanCoordDeriv
  rw [fderiv_fun_add (hf.differentiableAt x) (hg.differentiableAt x)]
  rfl

theorem coordDeriv_sum {ι : Type*} (s : Finset ι) {f : ι → Vec d → ℝ} (hf : ∀ j, Sm (f j))
    (i : Fin d) (x : Vec d) :
    euclideanCoordDeriv i (fun y => ∑ j ∈ s, f j y) x = ∑ j ∈ s, euclideanCoordDeriv i (f j) x := by
  unfold euclideanCoordDeriv
  rw [fderiv_fun_sum (fun j _ => (hf j).differentiableAt x)]
  simp

theorem coordDeriv_coord (i j : Fin d) (x : Vec d) :
    euclideanCoordDeriv i (fun y : Vec d => y j) x = if i = j then 1 else 0 := by
  unfold euclideanCoordDeriv
  have h : HasFDerivAt (fun y : Vec d => y j) (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin d => ℝ) j) x := hasFDerivAt_apply j x
  rw [h.fderiv]
  simp [basisVec_apply, eq_comm]

theorem sm_coord (j : Fin d) : Sm (fun y : Vec d => y j) := contDiff_apply ℝ ℝ j

theorem coordDeriv_const_mul {f : Vec d → ℝ} (hf : Sm f) (c : ℝ) (i : Fin d) (x : Vec d) :
    euclideanCoordDeriv i (fun y => c * f y) x = c * euclideanCoordDeriv i f x := by
  unfold euclideanCoordDeriv
  rw [fderiv_const_mul (hf.differentiableAt x)]
  rfl

/-- The weight `x ↦ Φ(s,x)` has coordinate derivative `-(1/(2s)) x_i Φ`. -/
theorem coordDeriv_heatKernel' {s : ℝ} (hs : 0 < s) (i : Fin d) (x : Vec d) :
    euclideanCoordDeriv i (heatKernel d s) x = -(1 / (2 * s)) * heatKernel d s x * x i := by
  rw [euclideanCoordDeriv_heatKernel hs]

theorem differentiableAt_heatKernel (s : ℝ) (x : Vec d) :
    DifferentiableAt ℝ (heatKernel d s) x :=
  (hasFDerivAt_heatKernel s x).differentiableAt

/-- Gaussian integration by parts in the coordinate direction `i`. -/
theorem gauss_ibp {s A' : ℝ} (hs : 0 < s) (hw : WeightInt d s A') {G : Vec d → ℝ} (hG : Sm G)
    (i : Fin d) (h0 : PDom (A' + A') G) (h1 : PDom (A' + A') (euclideanCoordDeriv i G))
    (h2 : PDom (A' + A') (fun x => x i * G x)) :
    ∫ x, euclideanCoordDeriv i G x * heatKernel d s x =
      (1 / (2 * s)) * ∫ x, (x i * G x) * heatKernel d s x := by
  have hΦ : ∀ x, fderiv ℝ (heatKernel d s) x (basisVec i) =
      -(1 / (2 * s)) * heatKernel d s x * x i := fun x => coordDeriv_heatKernel' hs i x
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := G)
    (g := heatKernel d s) (v := basisVec i)
    (h1.integrable_mul_heatKernel hs hw)
    (by
      have := (h2.integrable_mul_heatKernel hs hw).const_mul (-(1 / (2 * s)))
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [hΦ]; ring)
    (h0.integrable_mul_heatKernel hs hw)
    (fun x _ => hG.differentiableAt x) (fun x _ => differentiableAt_heatKernel s x)
  simp only [hΦ] at key
  have e : ∫ x, G x * (-(1 / (2 * s)) * heatKernel d s x * x i) =
      -((1 / (2 * s)) * ∫ x, (x i * G x) * heatKernel d s x) := by
    rw [← integral_const_mul, ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only; ring
  rw [e] at key
  change _ = _ at key
  have : ∫ x, euclideanCoordDeriv i G x * heatKernel d s x =
      ∫ x, fderiv ℝ G x (basisVec i) * heatKernel d s x := rfl
  rw [this]
  linarith

end

end PDE
