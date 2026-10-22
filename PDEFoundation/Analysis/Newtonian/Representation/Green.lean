module

public import PDEFoundation.Analysis.Newtonian.Representation.Integrability
public import PDEFoundation.Sobolev.ClassicalLaplacian
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Regularized Green identity and the divergence-free identity

For `ε > 0` and smooth compactly supported data:

* `∫ regKernel ε (x - y) · ∇g(y) dy = ∫ regDiv ε (x - y) g(y) dy`;
* `∫ regKernel ε (x - y) · Ψ(y) dy = 0` if `div Ψ = 0`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace PDE

namespace NewtonRepresentation

noncomputable section

variable {d : ℕ}

theorem integrable_mul_fderiv {a b : Vec d → ℝ} (ha : Continuous a) (hb : ContDiff ℝ 1 b)
    (hbc : HasCompactSupport b) (v : Vec d) :
    Integrable (fun x => a x * fderiv ℝ b x v) := by
  refine Continuous.integrable_of_hasCompactSupport
    (ha.mul ((hb.continuous_fderiv (by simp)).clm_apply continuous_const)) ?_
  exact (hbc.fderiv_apply (𝕜 := ℝ) v).mul_left

theorem integrable_fderiv_mul {a b : Vec d → ℝ} (ha : ContDiff ℝ 1 a) (hb : Continuous b)
    (hbc : HasCompactSupport b) (v : Vec d) :
    Integrable (fun x => fderiv ℝ a x v * b x) := by
  refine Continuous.integrable_of_hasCompactSupport
    (((ha.continuous_fderiv (by simp)).clm_apply continuous_const).mul hb) ?_
  exact hbc.mul_left

theorem integral_mul_fderiv_eq {a b : Vec d → ℝ} (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b)
    (hbc : HasCompactSupport b) (v : Vec d) :
    ∫ x, a x * fderiv ℝ b x v = -∫ x, fderiv ℝ a x v * b x := by
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (integrable_fderiv_mul ha hb.continuous hbc v)
    (integrable_mul_fderiv ha.continuous hb hbc v)
    (Continuous.integrable_of_hasCompactSupport (ha.continuous.mul hb.continuous) hbc.mul_left)
    (fun x _ => (ha.differentiable (by simp)) x) (fun x _ => (hb.differentiable (by simp)) x)

/-- Composition `y ↦ f (x - y)` has directional derivative `-(f' (x - y)) v`. -/
theorem fderiv_comp_sub_left_apply {f : Vec d → ℝ} (hf : Differentiable ℝ f) (x y v : Vec d) :
    fderiv ℝ (fun y => f (x - y)) y v = -fderiv ℝ f (x - y) v := by
  have h1 : HasFDerivAt (fun y : Vec d => x - y) (-(ContinuousLinearMap.id ℝ (Vec d))) y :=
    (hasFDerivAt_id y).const_sub x
  have h2 := (hf (x - y)).hasFDerivAt.comp y h1
  have h3 : HasFDerivAt (fun y : Vec d => f (x - y)) _ y := h2
  rw [h3.fderiv]
  simp

theorem contDiff_comp_sub_left {f : Vec d → ℝ} {n : WithTop ℕ∞} (hf : ContDiff ℝ n f) (x : Vec d) :
    ContDiff ℝ n (fun y => f (x - y)) :=
  hf.comp (contDiff_const.sub contDiff_id)

theorem contDiff_regKernel_comp {ε : ℝ} (hε : ε ≠ 0) (i : Fin d) (x : Vec d) :
    ContDiff ℝ 1 (fun y : Vec d => regKernel ε (x - y) i) :=
  contDiff_comp_sub_left ((contDiff_regKernel_apply hε i).of_le (by exact_mod_cast le_top)) x

/-- Regularized Green identity. -/
theorem integral_regKernel_dot_gradient {ε : ℝ} (hε : ε ≠ 0) {g : Vec d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) (x : Vec d) :
    ∫ y, vecDot (regKernel ε (x - y)) (classicalGradient g y) =
      ∫ y, regDiv d ε (x - y) * g y := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by exact_mod_cast le_top)
  have hint : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      Integrable (fun y => regKernel ε (x - y) i * classicalGradient g y i) := fun i _ =>
    integrable_mul_fderiv (contDiff_regKernel_comp hε i x).continuous hg1 hgc (basisVec i)
  have key : ∀ i : Fin d, ∫ y, regKernel ε (x - y) i * classicalGradient g y i =
      ∫ y, fderiv ℝ (fun z : Vec d => regKernel ε z i) (x - y) (basisVec i) * g y := by
    intro i
    have h := integral_mul_fderiv_eq (contDiff_regKernel_comp hε i x) hg1 hgc (basisVec i)
    simp only [classicalGradient_apply]
    rw [h, ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [fderiv_comp_sub_left_apply
      ((contDiff_regKernel_apply hε i).differentiable (by simp)) x y (basisVec i)]
    ring
  have hint2 : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      Integrable (fun y => fderiv ℝ (fun z : Vec d => regKernel ε z i) (x - y) (basisVec i) * g y) := by
    intro i _
    have hKi : ContDiff ℝ 1 (fun z : Vec d => regKernel ε z i) :=
      (contDiff_regKernel_apply hε i).of_le (by exact_mod_cast le_top)
    have hc : Continuous (fun y : Vec d =>
        fderiv ℝ (fun z : Vec d => regKernel ε z i) (x - y) (basisVec i)) :=
      ((hKi.continuous_fderiv (by simp)).clm_apply continuous_const).comp (by fun_prop)
    exact Continuous.integrable_of_hasCompactSupport (hc.mul hg.continuous) hgc.mul_left
  unfold vecDot
  rw [integral_finsetSum _ hint]
  simp only [key]
  rw [← integral_finsetSum _ hint2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  beta_reduce
  rw [← Finset.sum_mul, sum_fderiv_regKernel hε]

/-- Regularized kernel against a divergence-free field integrates to zero. -/
theorem integral_regKernel_dot_divFree {ε : ℝ} (hε : ε ≠ 0) {Ψ : Vec d → Vec d}
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨc : HasCompactSupport Ψ)
    (hdiv : ∀ y, classicalDivergence Ψ y = 0) (x : Vec d) :
    ∫ y, vecDot (regKernel ε (x - y)) (Ψ y) = 0 := by
  have hγ : ContDiff ℝ 1 (fun y : Vec d => regPotential d ε (x - y)) :=
    contDiff_comp_sub_left (contDiff_one_regPotential hε) x
  have hΨi : ∀ i : Fin d, ContDiff ℝ 1 (fun y : Vec d => Ψ y i) := fun i =>
    ((contDiff_pi.1 hΨ i)).of_le (by exact_mod_cast le_top)
  have hΨic : ∀ i : Fin d, HasCompactSupport (fun y : Vec d => Ψ y i) := fun i =>
    hΨc.comp_left (g := fun v : Vec d => v i) rfl
  have hint : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      Integrable (fun y => regKernel ε (x - y) i * Ψ y i) := fun i _ =>
    Continuous.integrable_of_hasCompactSupport
      (((contDiff_regKernel_comp hε i x).continuous).mul (hΨi i).continuous) (hΨic i).mul_left
  have key : ∀ i : Fin d, ∫ y, regKernel ε (x - y) i * Ψ y i =
      ∫ y, regPotential d ε (x - y) * fderiv ℝ (fun y : Vec d => Ψ y i) y (basisVec i) := by
    intro i
    have h := integral_mul_fderiv_eq hγ (hΨi i) (hΨic i) (basisVec i)
    rw [h, ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [fderiv_comp_sub_left_apply ((contDiff_one_regPotential hε).differentiable (by simp)) x y
      (basisVec i), fderiv_regPotential_apply hε, vecDot_basisVec_right]
    ring
  have hint2 : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      Integrable (fun y => regPotential d ε (x - y) *
        fderiv ℝ (fun y : Vec d => Ψ y i) y (basisVec i)) := fun i _ =>
    integrable_mul_fderiv hγ.continuous (hΨi i) (hΨic i) (basisVec i)
  unfold vecDot
  rw [integral_finsetSum _ hint]
  simp only [key]
  rw [← integral_finsetSum _ hint2]
  have : ∀ y : Vec d, ∑ i : Fin d, regPotential d ε (x - y) *
      fderiv ℝ (fun y : Vec d => Ψ y i) y (basisVec i) = 0 := by
    intro y
    rw [← Finset.mul_sum]
    have := hdiv y
    simp only [classicalDivergence, euclideanCoordDeriv] at this
    rw [this, mul_zero]
  simp [this]

end

end NewtonRepresentation

end PDE
