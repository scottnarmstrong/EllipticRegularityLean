module

public import PDEFoundation.Sobolev.H1.ZeroBoundary
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Projection onto zero-boundary gradients

The gradient range of the canonical closed `H¹₀` graph is closed whenever a
Poincaré bound controls its scalar component. Orthogonal projection then gives
the Dirichlet harmonic replacement at graph level. The domain-specific
Poincaré inequality is a separate analytic theorem.
-/

@[expose] public section

open scoped ENNReal NNReal RealInnerProductSpace

namespace PDE

private instance factOneLeTwo : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

private noncomputable instance h1GraphNormedGroup {d : ℕ} (U : Set (Vec d)) :
    NormedAddCommGroup (H1Graph U) :=
  Submodule.normedAddCommGroup (weakGradientGraph U (2 : ℝ≥0∞)).toSubmodule

private noncomputable instance h10GraphNormedGroup {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) : NormedAddCommGroup (H10Graph hU) :=
  Submodule.normedAddCommGroup (h10GraphClosedSubmodule hU).toSubmodule

private noncomputable instance h1GraphNormedSpace {d : ℕ} (U : Set (Vec d)) :
    NormedSpace ℝ (H1Graph U) :=
  Submodule.normedSpace (𝕜 := ℝ) (R := ℝ)
    (weakGradientGraph U (2 : ℝ≥0∞)).toSubmodule

private noncomputable instance h10GraphNormedSpace {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) : NormedSpace ℝ (H10Graph hU) :=
  Submodule.normedSpace (𝕜 := ℝ) (R := ℝ) (h10GraphClosedSubmodule hU).toSubmodule

private noncomputable instance h10GraphComplete {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) : CompleteSpace (H10Graph hU) :=
  w10pGraphCompleteSpace (p := (2 : ℝ≥0∞)) hU

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

private theorem isClosed_range_of_norm_bound
    {E F : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    [NormedAddCommGroup F]
    (f : E →+ F) (hf : UniformContinuous f) (K : ℝ≥0)
    (hbound : ∀ z, ‖z‖ ≤ (K : ℝ) * ‖f z‖) :
    IsClosed (Set.range f) :=
  (AddMonoidHomClass.antilipschitz_of_bound f hbound).isClosed_range hf

/-- Gradient projection from the existing maximum-norm Sobolev graph. -/
def h1GradientCLM : H1Graph U →L[ℝ] HilbertVectorLp U (2 : ℝ≥0∞) :=
  (ContinuousLinearMap.snd ℝ (ScalarLp U (2 : ℝ≥0∞))
    (HilbertVectorLp U (2 : ℝ≥0∞))).comp
      (weakGradientGraph U (2 : ℝ≥0∞)).toSubmodule.subtypeL

@[simp]
theorem h1GradientCLM_apply (z : H1Graph U) : h1GradientCLM z = z.1.2 := rfl

/-- Gradient map on the canonical zero-boundary graph. -/
def h10GradientCLM (hU : IsOpen U) :
    H10Graph hU →L[ℝ] HilbertVectorLp U (2 : ℝ≥0∞) :=
  h1GradientCLM.comp (h10GraphClosedSubmodule hU).toSubmodule.subtypeL

@[simp]
theorem h10GradientCLM_apply (hU : IsOpen U) (z : H10Graph hU) :
    h10GradientCLM hU z = z.1.1.2 := rfl

/-- Poincaré controls the whole maximum-norm zero-boundary graph. -/
theorem h10Graph_norm_le_gradient (hU : IsOpen U) {C : ℝ}
    (hP : ∀ z : H10Graph hU, ‖z.1.1.1‖ ≤ C * ‖h10GradientCLM hU z‖)
    (z : H10Graph hU) :
    ‖z‖ ≤ max C 1 * ‖h10GradientCLM hU z‖ := by
  change ‖z.1‖ ≤ _
  rw [H1Graph.norm_eq_max]
  apply max_le
  · exact (hP z).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · change ‖h10GradientCLM hU z‖ ≤ _
    calc
      ‖h10GradientCLM hU z‖ = 1 * ‖h10GradientCLM hU z‖ := (one_mul _).symm
      _ ≤ max C 1 * ‖h10GradientCLM hU z‖ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

/-- A Poincaré inequality makes the range of zero-boundary gradients closed. -/
theorem isClosed_range_h10GradientCLM (hU : IsOpen U) {C : ℝ}
    (hP : ∀ z : H10Graph hU, ‖z.1.1.1‖ ≤ C * ‖h10GradientCLM hU z‖) :
    IsClosed (Set.range (h10GradientCLM hU)) := by
  let K : ℝ≥0 := ⟨max C 1, le_trans zero_le_one (le_max_right _ _)⟩
  have hbound : ∀ z : H10Graph hU, ‖z‖ ≤ (K : ℝ) * ‖h10GradientCLM hU z‖ :=
    h10Graph_norm_le_gradient hU hP
  exact isClosed_range_of_norm_bound (E := H10Graph hU)
    (F := HilbertVectorLp U (2 : ℝ≥0∞)) (h10GradientCLM hU).toAddMonoidHom
    (h10GradientCLM hU).uniformContinuous K hbound

/-- Projection constructs a harmonic graph with the original boundary class,
with the exact constant-one gradient-energy bound. -/
theorem exists_harmonicReplacement_graph (hU : IsOpen U) {C : ℝ}
    (hP : ∀ z : H10Graph hU, ‖z.1.1.1‖ ≤ C * ‖h10GradientCLM hU z‖)
    (u : H1Graph U) :
    ∃ w : H10Graph hU,
      (∀ z : H10Graph hU,
        inner ℝ (h1GradientCLM (u - w.1)) (h10GradientCLM hU z) = 0) ∧
      ‖h1GradientCLM (u - w.1)‖ ≤ ‖h1GradientCLM u‖ := by
  let S : Submodule ℝ (HilbertVectorLp U (2 : ℝ≥0∞)) :=
    LinearMap.range (h10GradientCLM hU).toLinearMap
  have hS : IsClosed (S : Set (HilbertVectorLp U (2 : ℝ≥0∞))) :=
    isClosed_range_h10GradientCLM hU hP
  let : CompleteSpace S := hS.completeSpace_coe
  let p := S.orthogonalProjectionOnto (h1GradientCLM u)
  obtain ⟨w, hw⟩ := p.2
  change h10GradientCLM hU w = (p : HilbertVectorLp U (2 : ℝ≥0∞)) at hw
  refine ⟨w, ?_, ?_⟩
  · intro z
    have hz : h10GradientCLM hU z ∈ S := ⟨z, rfl⟩
    have horth := S.sub_starProjection_mem_orthogonal (h1GradientCLM u)
    have heq : h1GradientCLM (u - w.1) = h1GradientCLM u - (p : _) := by
      rw [map_sub]
      change h1GradientCLM u - h10GradientCLM hU w = _
      rw [hw]
    rw [heq]
    exact (S.mem_orthogonal' _).mp horth _ hz
  · have heq : h1GradientCLM (u - w.1) = h1GradientCLM u - (p : _) := by
      rw [map_sub]
      change h1GradientCLM u - h10GradientCLM hU w = _
      rw [hw]
    rw [heq]
    simpa only [Submodule.starProjection_orthogonal_val] using!
      S.orthogonal.norm_starProjection_apply_le (h1GradientCLM u)

end

end PDE
