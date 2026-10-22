module

public import PDEFoundation.Analysis.Newtonian.Defs
public import PDEFoundation.Analysis.Newtonian.Representation.Identities

/-!
# Proof of `PDE.eq_newtonPotential_of_laplacian_eq_div`

If `w` and `F` are smooth with compact support and `Δw = div F`, then `w = newtonPotential F`.
The proof is the Green representation formula `w = E ⋆· ∇w` together with the vanishing of
`E ⋆· Ψ` for the divergence-free field `Ψ = ∇w - F`
(`PDEFoundation.Analysis.Newtonian.Representation.Identities`).
-/

@[expose] public section

open MeasureTheory

namespace PDE

namespace NewtonRepresentationProof

theorem result (d : ℕ) (hd : 0 < d)
    (w : Vec d → ℝ) (F : Vec d → Vec d)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)
    (hΔ : ∀ x, euclideanCoordLaplacian w x = classicalDivergence F x) :
    w = newtonPotential F := by
  funext x
  -- components of the gradient
  have hGs : ∀ i, ContDiff ℝ (⊤ : ℕ∞) fun y => classicalGradient w y i := fun i =>
    contDiff_euclideanCoordDeriv hw i
  have hGc : ∀ i, HasCompactSupport fun y => classicalGradient w y i := fun i =>
    hasCompactSupport_euclideanCoordDeriv hwc i
  have hFs : ∀ i, ContDiff ℝ (⊤ : ℕ∞) fun y => F y i := fun i => contDiff_pi.1 hF i
  have hFci : ∀ i, HasCompactSupport fun y => F y i := fun i =>
    hFc.comp_left (g := fun v : Vec d => v i) rfl
  set Ψ : Vec d → Vec d := fun y => classicalGradient w y - F y with hΨdef
  have hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ := contDiff_pi.2 fun i => (hGs i).sub (hFs i)
  have hΨc : HasCompactSupport Ψ := by
    have h1 : HasCompactSupport (classicalGradient w) := by
      refine HasCompactSupport.intro hwc.isCompact fun y hy => ?_
      funext i
      have : y ∉ Function.support (euclideanCoordDeriv i w) := fun h =>
        hy (support_euclideanCoordDeriv_subset_tsupport i w h)
      exact Function.notMem_support.1 this
    exact h1.sub hFc
  have hdiv : ∀ y, classicalDivergence Ψ y = 0 := by
    intro y
    have e : classicalDivergence Ψ y =
        euclideanCoordLaplacian w y - classicalDivergence F y := by
      unfold classicalDivergence euclideanCoordLaplacian euclideanCoordSecondDeriv
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have h1 : DifferentiableAt ℝ (fun y => classicalGradient w y k) y :=
        ((hGs k).differentiable (by simp)) y
      have h2 : DifferentiableAt ℝ (fun y => F y k) y := ((hFs k).differentiable (by simp)) y
      have : (fun y => Ψ y k) = fun y => classicalGradient w y k - F y k := by
        funext y; simp [hΨdef]
      simp only [euclideanCoordDeriv, this]
      rw [fderiv_fun_sub h1 h2]
      rfl
    rw [e, hΔ y, sub_self]
  have hGcont : ∀ i, Continuous fun y => classicalGradient w y i := fun i => (hGs i).continuous
  have hFcont : ∀ i, Continuous fun y => F y i := fun i => (hFs i).continuous
  have h1 := NewtonRepresentation.green_representation hd hw hwc x
  have h2 := NewtonRepresentation.integral_newtonKernel_dot_eq_zero_of_divergence_eq_zero hd hΨ
    hΨc hdiv x
  have i1 := NewtonRepresentation.integrable_newtonKernel_dot hd hFcont hFci x
  have i2 := NewtonRepresentation.integrable_newtonKernel_dot hd hGcont hGc x
  have hsplit : ∀ y, vecDot (newtonKernel (x - y)) (classicalGradient w y) =
      vecDot (newtonKernel (x - y)) (F y) + vecDot (newtonKernel (x - y)) (Ψ y) := by
    intro y
    simp only [hΨdef, vecDot, Pi.sub_apply, mul_sub]
    rw [Finset.sum_sub_distrib]
    ring
  have i3 : Integrable (fun y => vecDot (newtonKernel (x - y)) (Ψ y)) := by
    refine (i2.sub i1).congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.sub_apply]
    rw [hsplit y]; ring
  rw [h1]
  simp only [hsplit]
  rw [integral_add i1 i3, h2, add_zero]
  rfl

end NewtonRepresentationProof

end PDE
