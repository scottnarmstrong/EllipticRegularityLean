module

public import PDEFoundation.PDE.BallDirichletGradient
public import PDEFoundation.Sobolev.H1.GraphPairing

/-!
# Riesz representation of an `L²` source on `H¹₀(B_R)`

For `g ∈ L²(B_R)` the functional `φ ↦ ∫ g φ` is bounded for the gradient norm on `H¹₀(B_R)`
(Poincaré with constant `2R`), so it is represented by a vector field `G ∈ L²(B_R; ℝᵈ)`
through `∫ g φ = ∫ G · ∇φ`.  This reduces zeroth-order sources to divergence forcing.
-/

@[expose] public section

open scoped ENNReal RealInnerProductSpace

namespace PDE.Ch4GreenDecay

open MeasureTheory PDE

noncomputable section

variable {d : ℕ}

/-- The value component of an `H¹₀` graph point, as a continuous linear map. -/
def h10ValueCLM {U : Set (Vec d)} (hU : IsOpen U) :
    H10Graph hU →L[ℝ] ScalarLp U (2 : ℝ≥0∞) :=
  (ContinuousLinearMap.fst ℝ (ScalarLp U (2 : ℝ≥0∞)) (HilbertVectorLp U (2 : ℝ≥0∞))).comp
    ((weakGradientGraph U (2 : ℝ≥0∞)).toSubmodule.subtypeL.comp
      (h10GraphClosedSubmodule hU).toSubmodule.subtypeL)

@[simp] theorem h10ValueCLM_apply {U : Set (Vec d)} (hU : IsOpen U) (z : H10Graph hU) :
    h10ValueCLM hU z = z.1.1.1 := rfl

/-- Native representative of a Hilbert-vector class. -/
def nativeRep {U : Set (Vec d)} (g : HilbertVectorLp U (2 : ℝ≥0∞)) : Vec d → Vec d :=
  fun x => (g x).toVec

theorem memVectorL2On_nativeRep {U : Set (Vec d)} (g : HilbertVectorLp U (2 : ℝ≥0∞)) :
    MemVectorL2On U (nativeRep g) := by
  apply gradMemLpOn_iff_memLp_toHilbertVecField.mpr
  simpa only [nativeRep, toHilbertVecField, Vec.toHilbertVec_toVec] using! Lp.memLp g

theorem coeFn_nativeRep {U : Set (Vec d)} (g : HilbertVectorLp U (2 : ℝ≥0∞)) :
    ⇑g =ᵐ[volumeOn U] toHilbertVecField (nativeRep g) := by
  refine Filter.Eventually.of_forall fun x => ?_
  simp only [nativeRep, toHilbertVecField, Vec.toHilbertVec_toVec]

/-- The `L²` pairing of a scalar class with an `H¹₀` value equals the integral of the product. -/
theorem integral_mul_eq_inner {U : Set (Vec d)} {g φ : Vec d → ℝ}
    (hg : MemL2On U g) (F : ScalarLp U (2 : ℝ≥0∞))
    (hF : ⇑F =ᵐ[volumeOn U] φ) :
    (∫ x in U, g x * φ x) = inner ℝ (hg.toScalarLp) F := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toScalarLp, hF] with x hx hy
  rw [hx, hy]
  simp [mul_comm]

variable {U : Set (Vec d)}

theorem h10GradientCLM_injective_of_poincare (hU : IsOpen U) {C : ℝ}
    (hP : ∀ z : H10Graph hU, ‖z.1.1.1‖ ≤ C * ‖h10GradientCLM hU z‖) :
    Function.Injective (h10GradientCLM hU).toLinearMap := by
  intro z w hzw
  have hz' : h10GradientCLM hU (z - w) = 0 :=
    ((h10GradientCLM hU).map_sub z w).trans (sub_eq_zero.mpr hzw)
  have := h10Graph_norm_le_gradient hU hP (z - w)
  rw [hz', norm_zero, mul_zero] at this
  exact sub_eq_zero.mp (norm_le_zero_iff.mp this)

/-- The gradient map is a linear equivalence onto the closed gradient subspace. -/
def gradEquiv (hU : IsOpen U) {C : ℝ}
    (hP : ∀ z : H10Graph hU, ‖z.1.1.1‖ ≤ C * ‖h10GradientCLM hU z‖) :
    H10Graph hU ≃ₗ[ℝ] closedGradientSubspace hU :=
  LinearEquiv.ofInjective (h10GradientCLM hU).toLinearMap
    (h10GradientCLM_injective_of_poincare hU hP)

theorem gradEquiv_apply (hU : IsOpen U) {C : ℝ}
    (hP : ∀ z : H10Graph hU, ‖z.1.1.1‖ ≤ C * ‖h10GradientCLM hU z‖) (z : H10Graph hU) :
    (gradEquiv hU hP z : HilbertVectorLp U (2 : ℝ≥0∞)) = h10GradientCLM hU z := rfl

/-- The source functional on the closed gradient subspace. -/
def sourceFunctional (hU : IsOpen U) {C : ℝ}
    (hP : ∀ z : H10Graph hU, ‖z.1.1.1‖ ≤ C * ‖h10GradientCLM hU z‖)
    (gL : ScalarLp U (2 : ℝ≥0∞)) : closedGradientSubspace hU →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    (((innerSL ℝ gL).toLinearMap ∘ₗ (h10ValueCLM hU).toLinearMap) ∘ₗ
      (gradEquiv hU hP).symm.toLinearMap) (‖gL‖ * C)
    (by
      intro y
      obtain ⟨z, hz⟩ : ∃ z, gradEquiv hU hP z = y := ⟨_, LinearEquiv.apply_symm_apply _ y⟩
      have hnorm : ‖y‖ = ‖h10GradientCLM hU z‖ := by
        rw [← Submodule.norm_coe, ← hz, gradEquiv_apply]
      rw [← hz]
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply, ContinuousLinearMap.coe_coe, innerSL_apply_apply,
        h10ValueCLM_apply]
      rw [hz, hnorm]
      calc ‖inner ℝ gL (z.1.1.1)‖ ≤ ‖gL‖ * ‖z.1.1.1‖ := norm_inner_le_norm _ _
        _ ≤ ‖gL‖ * (C * ‖h10GradientCLM hU z‖) :=
          mul_le_mul_of_nonneg_left (hP z) (norm_nonneg _)
        _ = (‖gL‖ * C) * ‖h10GradientCLM hU z‖ := by ring)

theorem sourceFunctional_apply (hU : IsOpen U) {C : ℝ}
    (hP : ∀ z : H10Graph hU, ‖z.1.1.1‖ ≤ C * ‖h10GradientCLM hU z‖)
    (gL : ScalarLp U (2 : ℝ≥0∞)) (z : H10Graph hU) :
    sourceFunctional hU hP gL (gradEquiv hU hP z) = inner ℝ gL (z.1.1.1) := by
  simp [sourceFunctional]

/-- **Riesz representation of an `L²` source** on `H¹₀(B_R)`. -/
theorem exists_riesz_source (hd : 0 < d) {R : ℝ} (hR : 0 < R) {g : Vec d → ℝ}
    (hg : MemL2On (euclideanBall (0 : Vec d) R) g) :
    ∃ G : Vec d → Vec d, MemVectorL2On (euclideanBall (0 : Vec d) R) G ∧
      ∀ φ : H10Function (euclideanBall (0 : Vec d) R),
        (∫ x in euclideanBall (0 : Vec d) R, g x * φ.toH1Function.toFun x) =
          ∫ x in euclideanBall (0 : Vec d) R, vecDot (G x) (φ.toH1Function.grad x) := by
  have hU : IsOpen (euclideanBall (0 : Vec d) R) := isOpen_euclideanBall 0 R
  have hP := h10Graph_value_norm_le_two_mul_radius_gradient_norm hd (z := (0 : Vec d)) hR
  let S := closedGradientSubspace hU
  have hS : IsClosed (S : Set (HilbertVectorLp (euclideanBall (0 : Vec d) R) (2 : ℝ≥0∞))) :=
    isClosed_range_h10GradientCLM hU hP
  let : CompleteSpace S := hS.completeSpace_coe
  let ℓ := sourceFunctional hU hP hg.toScalarLp
  let GS : S := (InnerProductSpace.toDual ℝ S).symm ℓ
  have hGS : ∀ y : S, inner ℝ GS y = ℓ y := fun y => by
    simp [GS]
  refine ⟨nativeRep (GS : HilbertVectorLp (euclideanBall (0 : Vec d) R) (2 : ℝ≥0∞)),
    memVectorL2On_nativeRep _, fun φ => ?_⟩
  set z := φ.toH10Graph hU with hz
  have h1 : inner ℝ (GS : HilbertVectorLp (euclideanBall (0 : Vec d) R) (2 : ℝ≥0∞))
      (h10GradientCLM hU z) = inner ℝ hg.toScalarLp (z.1.1.1) := by
    have := hGS (gradEquiv hU hP z)
    rw [sourceFunctional_apply] at this
    exact this
  have hφcoe : ⇑(h10GradientCLM hU z) =ᵐ[volumeOn (euclideanBall (0 : Vec d) R)]
      toHilbertVecField φ.toH1Function.grad :=
    φ.toH1Function.toW1pFunction.coeFn_toW1pGraph_snd
  have hleft := setIntegral_vecDot_eq_inner_of_ae_eq
    (GS : HilbertVectorLp (euclideanBall (0 : Vec d) R) (2 : ℝ≥0∞)) (h10GradientCLM hU z)
    (nativeRep _) φ.toH1Function.grad (coeFn_nativeRep _) hφcoe
  have hright := integral_mul_eq_inner hg (z.1.1.1) (φ := φ.toH1Function.toFun)
    φ.toH1Function.toW1pFunction.coeFn_toW1pGraph_fst
  rw [hright, hleft]
  exact h1.symm

end

end PDE.Ch4GreenDecay
