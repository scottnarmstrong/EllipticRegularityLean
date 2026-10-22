module

public import PDEFoundation.Sobolev.H1.GraphRepresentative
public import PDEFoundation.Sobolev.H1.Algebra
public import PDEFoundation.Sobolev.H1.GradientProjection
public import PDEFoundation.Sobolev.W1p.GraphEnergy

/-!
# Native gradient pairings and the complete graph

Exact integral identities connect the Hilbert `L²` gradient component to the
coordinate dot product used by the weak PDE formulation.
-/

@[expose] public section

open scoped ENNReal RealInnerProductSpace

namespace PDE

open MeasureTheory

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

/-- The representative-to-graph map respects subtraction exactly. -/
theorem H1Function.toW1pGraph_sub (u v : H1Function U) :
    (u - v).toW1pFunction.toW1pGraph =
      u.toW1pFunction.toW1pGraph - v.toW1pFunction.toW1pGraph := by
  apply Subtype.ext
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [(u - v).toW1pFunction.coeFn_toW1pGraph_fst,
      Lp.coeFn_sub u.toW1pFunction.toW1pGraph.1.1 v.toW1pFunction.toW1pGraph.1.1,
      u.toW1pFunction.coeFn_toW1pGraph_fst,
      v.toW1pFunction.coeFn_toW1pGraph_fst] with x huv hsub hu hv
    change (u - v).toW1pFunction.toW1pGraph.1.1 x =
      (u.toW1pFunction.toW1pGraph.1.1 - v.toW1pFunction.toW1pGraph.1.1) x
    rw [huv, hsub]
    simp only [Pi.sub_apply, hu, hv]
    rfl
  · apply Lp.ext
    filter_upwards [(u - v).toW1pFunction.coeFn_toW1pGraph_snd,
      Lp.coeFn_sub u.toW1pFunction.toW1pGraph.1.2 v.toW1pFunction.toW1pGraph.1.2,
      u.toW1pFunction.coeFn_toW1pGraph_snd,
      v.toW1pFunction.coeFn_toW1pGraph_snd] with x huv hsub hu hv
    change (u - v).toW1pFunction.toW1pGraph.1.2 x =
      (u.toW1pFunction.toW1pGraph.1.2 - v.toW1pFunction.toW1pGraph.1.2) x
    rw [huv, hsub]
    simp only [Pi.sub_apply, hu, hv]
    rfl

/-- Scalar energy agrees exactly with the squared value-component norm. -/
theorem H1Function.setIntegral_sq_toFun_eq_norm_sq (u : H1Function U) :
    (∫ x in U, u.toFun x ^ 2) = ‖u.toW1pFunction.toW1pGraph.1.1‖ ^ 2 :=
  integral_sq_eq_sq_norm_of_ae_eq _ _ u.toW1pFunction.coeFn_toW1pGraph_fst

/-- The internal Hilbert inner product is the native Euclidean dot product. -/
theorem inner_toHilbertVec_eq_vecDot (x y : Vec d) :
    inner ℝ x.toHilbertVec y.toHilbertVec = vecDot x y := by
  rw [PiLp.inner_apply]
  simp only [Vec.toHilbertVec_apply, RCLike.inner_apply, conj_trivial, vecDot, mul_comm]

/-- Dot-product integration is precisely the inner product of gradient classes. -/
theorem setIntegral_vecDot_eq_inner_of_ae_eq
    (F G : HilbertVectorLp U (2 : ℝ≥0∞)) (f g : Vec d → Vec d)
    (hF : ⇑F =ᵐ[volumeOn U] toHilbertVecField f)
    (hG : ⇑G =ᵐ[volumeOn U] toHilbertVecField g) :
    (∫ x in U, vecDot (f x) (g x)) = inner ℝ F G := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hF, hG] with x hx hy
  rw [hx, hy]
  exact (inner_toHilbertVec_eq_vecDot (f x) (g x)).symm

/-- Gradient energy agrees exactly with the squared graph-component norm. -/
theorem H1Function.setIntegral_vecNormSq_grad_eq_norm_sq (u : H1Function U) :
    (∫ x in U, vecNormSq (u.grad x)) =
      ‖h1GradientCLM u.toW1pFunction.toW1pGraph‖ ^ 2 := by
  have h := setIntegral_vecDot_eq_inner_of_ae_eq
    (h1GradientCLM u.toW1pFunction.toW1pGraph)
    (h1GradientCLM u.toW1pFunction.toW1pGraph) u.grad u.grad
    u.toW1pFunction.coeFn_toW1pGraph_snd
    u.toW1pFunction.coeFn_toW1pGraph_snd
  exact h.trans (real_inner_self_eq_norm_sq _)

/-- The canonical graph representatives give the same exact gradient pairing. -/
theorem H1Graph.setIntegral_vecDot_grad_eq_inner (v w : H1Graph U) :
    (∫ x in U, vecDot (v.toH1Function.grad x) (w.toH1Function.grad x)) =
      inner ℝ (h1GradientCLM v) (h1GradientCLM w) := by
  apply setIntegral_vecDot_eq_inner_of_ae_eq
  · exact Filter.EventuallyEq.rfl
  · exact Filter.EventuallyEq.rfl

/-- Exact gradient pairing for arbitrary existing Sobolev representatives. -/
theorem H1Function.setIntegral_vecDot_grad_eq_inner (v w : H1Function U) :
    (∫ x in U, vecDot (v.grad x) (w.grad x)) =
      inner ℝ (h1GradientCLM v.toW1pFunction.toW1pGraph)
        (h1GradientCLM w.toW1pFunction.toW1pGraph) :=
  setIntegral_vecDot_eq_inner_of_ae_eq _ _ _ _
    v.toW1pFunction.coeFn_toW1pGraph_snd w.toW1pFunction.coeFn_toW1pGraph_snd

end

end PDE
