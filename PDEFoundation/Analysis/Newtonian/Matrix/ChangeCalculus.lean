module

public import PDEFoundation.Analysis.Newtonian.Matrix.ChangeLinear
public import PDEFoundation.Sobolev.ClassicalLaplacian
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Calculus for the linear change of variables `y ↦ A y`

For a matrix `A` the map `y ↦ matVecMul A y` is a continuous linear map.  This module records
how coordinate derivatives, gradients, the classical divergence and the Laplacian transform
under composition with it:

* `∇(u ∘ A) = Aᵀ (∇u) ∘ A`,
* `div (y ↦ B H(A y)) = Σ_{l,j} (A B)_{lj} (∂_l H_j)(A y)`,
* `Δ(u ∘ A) = div(A Aᵀ ∇u) ∘ A`.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace PDE

namespace MatChange

variable {d : ℕ}

/-- The continuous linear map `y ↦ A y`. -/
noncomputable def linCLM (A : Mat d) : Vec d →L[ℝ] Vec d :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)

theorem linCLM_apply (A : Mat d) (y : Vec d) : linCLM A y = matVecMul A y := rfl

theorem continuous_matVecMul (A : Mat d) : Continuous fun y : Vec d => matVecMul A y :=
  (linCLM A).continuous

theorem contDiff_matVecMul (A : Mat d) {n : WithTop ℕ∞} :
    ContDiff ℝ n fun y : Vec d => matVecMul A y :=
  (linCLM A).contDiff

theorem matVecMul_basisVec (A : Mat d) (i : Fin d) : matVecMul A (basisVec i) = fun j => A j i := by
  funext j
  simp [matVecMul, basisVec, Pi.single_apply]

/-- Chain rule for coordinate derivatives under a linear change of variables. -/
theorem euclideanCoordDeriv_comp_matVecMul (A : Mat d) {u : Vec d → ℝ} (y : Vec d)
    (hu : DifferentiableAt ℝ u (matVecMul A y)) (i : Fin d) :
    euclideanCoordDeriv i (fun z => u (matVecMul A z)) y =
      ∑ j, A j i * euclideanCoordDeriv j u (matVecMul A y) := by
  have hf : DifferentiableAt ℝ (fun z : Vec d => matVecMul A z) y :=
    (linCLM A).differentiableAt
  have h := fderiv_comp (𝕜 := ℝ) y hu hf
  have e0 : fderiv ℝ (fun z : Vec d => matVecMul A z) y = linCLM A :=
    (linCLM A).hasFDerivAt.fderiv
  have e1 : fderiv ℝ (fun z => u (matVecMul A z)) y =
      (fderiv ℝ u (matVecMul A y)).comp (linCLM A) := by
    rw [show (fun z => u (matVecMul A z)) = u ∘ fun z => matVecMul A z from rfl, h, e0]
  calc euclideanCoordDeriv i (fun z => u (matVecMul A z)) y
      = fderiv ℝ u (matVecMul A y) (matVecMul A (basisVec i)) := by
        unfold euclideanCoordDeriv
        rw [e1]
        rfl
    _ = _ := by
      rw [matVecMul_basisVec, fderiv_apply_eq_vecDot_classicalGradient]
      unfold vecDot
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm]
      rfl

theorem classicalGradient_comp_matVecMul (A : Mat d) {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (y : Vec d) :
    classicalGradient (fun z => u (matVecMul A z)) y =
      matVecMul Aᵀ (classicalGradient u (matVecMul A y)) := by
  funext i
  have := euclideanCoordDeriv_comp_matVecMul A y ((hu.differentiable (by simp)) _) i
  exact this

theorem euclideanCoordDeriv_sum_mul {g : Fin d → Vec d → ℝ} (c : Fin d → ℝ)
    (hg : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (g j)) (k : Fin d) (y : Vec d) :
    euclideanCoordDeriv k (fun z => ∑ j, c j * g j z) y =
      ∑ j, c j * euclideanCoordDeriv k (g j) y := by
  unfold euclideanCoordDeriv
  have hd : ∀ j ∈ Finset.univ, DifferentiableAt ℝ (fun z => c j * g j z) y := fun j _ =>
    (((hg j).differentiable (by simp)) y).const_mul _
  rw [fderiv_fun_sum hd]
  simp only [sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fderiv_const_mul (((hg j).differentiable (by simp)) y)]
  simp

/-- Divergence of `y ↦ B H(A y)`. -/
theorem classicalDivergence_matVecMul_comp (A B : Mat d) {H : Vec d → Vec d}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (y : Vec d) :
    classicalDivergence (fun z => matVecMul B (H (matVecMul A z))) y =
      ∑ l, ∑ j, (A * B) l j * euclideanCoordDeriv l (fun z => H z j) (matVecMul A y) := by
  have hHj : ∀ j, ContDiff ℝ (⊤ : ℕ∞) fun z => H z j := fun j => contDiff_pi.1 hH j
  have hHjA : ∀ j, ContDiff ℝ (⊤ : ℕ∞) fun z => H (matVecMul A z) j := fun j =>
    (hHj j).comp (contDiff_matVecMul A)
  unfold classicalDivergence
  have step : ∀ k : Fin d, euclideanCoordDeriv k (fun z => matVecMul B (H (matVecMul A z)) k) y =
      ∑ j, B k j * ∑ l, A l k * euclideanCoordDeriv l (fun z => H z j) (matVecMul A y) := by
    intro k
    have := euclideanCoordDeriv_sum_mul (g := fun j z => H (matVecMul A z) j) (B k) hHjA k y
    simp only [matVecMul_apply]
    rw [this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [euclideanCoordDeriv_comp_matVecMul A y (((hHj j).differentiable (by simp)) _) k]
  simp only [step]
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine (Finset.sum_congr rfl fun k _ => Finset.sum_comm).trans
    (Finset.sum_comm.trans ((Finset.sum_congr rfl fun l _ => Finset.sum_comm).trans ?_))
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  ring

theorem classicalDivergence_matVecMul {B : Mat d} {H : Vec d → Vec d}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (y : Vec d) :
    classicalDivergence (fun z => matVecMul B (H z)) y =
      ∑ l, ∑ j, B l j * euclideanCoordDeriv l (fun z => H z j) y := by
  have := classicalDivergence_matVecMul_comp (1 : Mat d) B hH y
  simpa only [matVecMul_one, Matrix.one_mul] using this

/-- Divergence of the transformed field `G(y) = S⁻¹ F(S y)`. -/
theorem classicalDivergence_inv_comp {S : Mat d} (hdet : S.det ≠ 0) {F : Vec d → Vec d}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (y : Vec d) :
    classicalDivergence (fun z => matVecMul S⁻¹ (F (matVecMul S z))) y =
      classicalDivergence F (matVecMul S y) := by
  rw [classicalDivergence_matVecMul_comp S S⁻¹ hF y, mul_inv_self hdet]
  unfold classicalDivergence
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [Matrix.one_apply]

/-- `Δ(u ∘ S) = div (S Sᵀ ∇u) ∘ S`. -/
theorem euclideanCoordLaplacian_comp_matVecMul (S : Mat d) {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (y : Vec d) :
    euclideanCoordLaplacian (fun z => u (matVecMul S z)) y =
      classicalDivergence (fun z => matVecMul (S * Sᵀ) (classicalGradient u z)) (matVecMul S y) := by
  have hG : ContDiff ℝ (⊤ : ℕ∞) (classicalGradient u) :=
    contDiff_pi.2 fun i => contDiff_euclideanCoordDeriv hu i
  have h1 : euclideanCoordLaplacian (fun z => u (matVecMul S z)) y =
      classicalDivergence (classicalGradient fun z => u (matVecMul S z)) y := rfl
  have h2 : classicalGradient (fun z => u (matVecMul S z)) =
      fun z => matVecMul Sᵀ (classicalGradient u (matVecMul S z)) :=
    funext fun z => classicalGradient_comp_matVecMul S hu z
  rw [h1, h2, classicalDivergence_matVecMul_comp S Sᵀ hG y,
    classicalDivergence_matVecMul hG]

/-- The linear homeomorphism of `Vec d` given by an invertible matrix. -/
noncomputable def matHomeomorph {A T : Mat d} (h1 : A * T = 1) (h2 : T * A = 1) : Vec d ≃ₜ Vec d where
  toFun := fun y => matVecMul A y
  invFun := fun y => matVecMul T y
  left_inv := fun y => by
    simp only [matVecMul_matVecMul, h2, matVecMul_one]
  right_inv := fun y => by
    simp only [matVecMul_matVecMul, h1, matVecMul_one]
  continuous_toFun := continuous_matVecMul A
  continuous_invFun := continuous_matVecMul T

theorem hasCompactSupport_comp_matVecMul {S : Mat d} (hdet : S.det ≠ 0) {f : Vec d → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport fun y => f (matVecMul S y) :=
  hf.comp_isClosedEmbedding (matHomeomorph (mul_inv_self hdet) (inv_mul_self hdet)).isClosedEmbedding

theorem hasCompactSupport_matVecMul_comp {S : Mat d} (hdet : S.det ≠ 0) {F : Vec d → Vec d}
    (hF : HasCompactSupport F) {B : Mat d} :
    HasCompactSupport fun y => matVecMul B (F (matVecMul S y)) := by
  have h := hF.comp_isClosedEmbedding
    (matHomeomorph (mul_inv_self hdet) (inv_mul_self hdet)).isClosedEmbedding
  refine h.comp_left (g := fun v => matVecMul B v) ?_
  funext i
  simp [matVecMul]

end MatChange

end PDE
