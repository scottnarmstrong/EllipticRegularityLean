module

public import PDEFoundation.PDE.WeakDivergenceForm
public import PDEFoundation.Sobolev.W1p.ZeroBoundaryPoincare

/-!
# Functional weak equations and divergence-form equations

This file converts a functional weak identity into the existing safe
divergence-form weak formulation once a density representing the functional
has been obtained.  The representation remains an explicit hypothesis: its
construction belongs to the duality argument that consumes this lemma.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

noncomputable section

/-- The gradient component of the zero-boundary graph associated with a
smooth test function agrees almost everywhere with its literal classical
gradient. -/
theorem w10pGradientCLM_smoothCompactlySupported_ae
    {d : ℕ} {U : Set (Vec d)} (q : ENNReal) [Fact (1 ≤ q)]
    (hU : IsOpen U) (φ : WeakTestFunction U) :
    (fun x =>
      ((w10pGradientCLM q hU
        (smoothCompactlySupportedW1pGraphToW10pGraph
          (p := q) hU φ)) x).toVec) =ᵐ[volumeOn U] φ.grad := by
  let w := W1pFunction.ofContDiff hU
    (φ.contDiff.of_le (by simp)) φ.hasCompactSupport q
  have hw : ∀ᵐ x ∂volumeOn U, ∀ i : Fin d,
      w.toW1pGraph.1.2 x i = w.grad x i :=
    ae_all_iff.mpr fun i => w.coeFn_toW1pGraph_snd_apply i
  filter_upwards [hw] with x hx
  funext i
  change w.toW1pGraph.1.2 x i = φ.grad x i
  rw [hx i]
  rfl

/-- A represented functional weak equation gives the safe smooth-test
divergence-form equation.  This compatibility result does not construct the
representing density. -/
theorem isWeakDivergenceFormSolutionOn_of_functional_representation
    {d : ℕ} {q : ENNReal} [Fact (1 ≤ q)]
    {U : Set (Vec d)} (hU : IsOpen U)
    {a : CoeffField d} {u : H1Function U} {F : Vec d → Vec d}
    (hdata : DivergenceFormL2DataOn a U u (fun _ => 0) F)
    (L : W10pGraph (p := q) hU → ℝ)
    (hrepresentation : ∀ v,
      L v = -∫ x in U,
        vecDot (F x) ((w10pGradientCLM q hU v x).toVec))
    (hfunctional : ∀ φ : WeakTestFunction U,
      (∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (φ.grad x)) =
        L (smoothCompactlySupportedW1pGraphToW10pGraph
          (p := q) hU φ)) :
    IsWeakDivergenceFormSolutionOn a U u (fun _ => 0) F := by
  intro φ
  refine ⟨hdata.testable φ, ?_⟩
  rw [hfunctional φ, hrepresentation]
  have hforcing :
      (∫ x in U,
        vecDot (F x)
          ((w10pGradientCLM q hU
            (smoothCompactlySupportedW1pGraphToW10pGraph
              (p := q) hU φ) x).toVec)) =
        ∫ x in U, vecDot (F x) (φ.grad x) := by
    apply integral_congr_ae
    filter_upwards [w10pGradientCLM_smoothCompactlySupported_ae q hU φ] with x hx
    rw [hx]
  rw [hforcing]
  simp

end

end PDE
