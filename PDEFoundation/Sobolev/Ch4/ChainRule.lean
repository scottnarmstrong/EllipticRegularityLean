module

public import PDEFoundation.Sobolev.Ch4.Truncation
public import PDEFoundation.Sobolev.H1.Composition

/-!
# Weak chain rule for `H¹` on arbitrary bounded open sets

For a `C¹` function `G` with bounded derivative, `G ∘ u` has weak gradient `G'(u) ∇u` on any
open set `U` of finite measure when `u ∈ H¹(U)`: the convex-domain theorem
`H1Function.hasWeakGradient_comp_contDiff_of_deriv_bounded` is applied on cubes inside `U` and
combined by the locality principle.
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory

namespace PDE.Ch4Infra

variable {d : ℕ} {U : Set (Vec d)}

theorem memL2On_comp_of_deriv_bounded (hfin : volume U ≠ ⊤) (u : H1Function U) {G : ℝ → ℝ}
    (hG : ContDiff ℝ 1 G) {M : ℝ} (hM : 0 ≤ M) (hderiv : ∀ t, |deriv G t| ≤ M) :
    MemL2On U (fun x => G (u.toFun x)) := by
  have := isFiniteMeasure_volumeOn_of_ne_top' hfin
  have hlip := lipschitzWith_of_abs_deriv_le hM (hG.differentiable (by simp)) hderiv
  have hsub : MemL2On U (fun x => G (u.toFun x) - G 0) := by
    refine (u.memL2.const_mul M).mono
      ((hG.continuous.comp_aestronglyMeasurable u.memL2.aestronglyMeasurable).sub
        aestronglyMeasurable_const)
      (Filter.Eventually.of_forall fun x => ?_)
    have := hlip.dist_le_mul (u.toFun x) 0
    rw [Real.dist_eq, Real.dist_eq, sub_zero, Real.coe_toNNReal M hM] at this
    simpa [Real.norm_eq_abs, abs_of_nonneg hM] using this
  have := hsub.add (memLp_const (G 0))
  have e : ((fun x => G (u.toFun x) - G 0) + fun _ => G 0) = fun x => G (u.toFun x) := by
    funext x; simp
  rwa [e] at this
where
  isFiniteMeasure_volumeOn_of_ne_top' (h : volume U ≠ ⊤) : IsFiniteMeasure (volumeOn U) :=
    ⟨by simpa [volumeOn] using h.lt_top⟩

theorem gradMemL2_comp_of_deriv_bounded (u : H1Function U) {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    {M : ℝ} (hM : 0 ≤ M) (hderiv : ∀ t, |deriv G t| ≤ M) :
    GradMemL2On U (fun x i => deriv G (u.toFun x) * u.grad x i) := fun i => by
  refine ((u.gradMemL2 i).const_mul M).mono
    (((hG.continuous_deriv le_rfl).comp_aestronglyMeasurable
      u.memL2.aestronglyMeasurable).mul (u.gradMemL2 i).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hM]
  exact mul_le_mul_of_nonneg_right (hderiv _) (abs_nonneg _)

/-- **Weak chain rule on an open set of finite measure.** -/
theorem hasWeakGradientOn_comp_open (hU : IsOpen U) (hfin : volume U ≠ ⊤) (u : H1Function U)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) {M : ℝ} (hM : 0 ≤ M) (hderiv : ∀ t, |deriv G t| ≤ M) :
    HasWeakGradientOn U (fun x => G (u.toFun x))
      (fun x i => deriv G (u.toFun x) * u.grad x i) := by
  refine hasWeakGradientOn_of_local_ball hU
    (locallyIntegrableOn_of_memL2On (memL2On_comp_of_deriv_bounded hfin u hG hM hderiv))
    (fun i => locallyIntegrableOn_of_memL2On (gradMemL2_comp_of_deriv_bounded u hG hM hderiv i)) ?_
  intro x hx
  obtain ⟨r, hr, hsub⟩ := exists_ball_subset hU hx
  exact ⟨r, hr, hsub, H1Function.hasWeakGradient_comp_contDiff_of_deriv_bounded
    (isOpenBoundedConvexDomain_ball x r) (u.restrict Metric.isOpen_ball hsub) hG hM hderiv⟩

/-- Composition of an `H¹` function on a bounded open set with a `C¹` function of bounded
derivative: value `G ∘ u`, gradient `G'(u) ∇u`. -/
noncomputable def compOpen (hU : IsOpen U) (hfin : volume U ≠ ⊤) (u : H1Function U)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) {M : ℝ} (hM : 0 ≤ M) (hderiv : ∀ t, |deriv G t| ≤ M) :
    H1Function U where
  toFun := fun x => G (u.toFun x)
  grad := fun x i => deriv G (u.toFun x) * u.grad x i
  memL2 := memL2On_comp_of_deriv_bounded hfin u hG hM hderiv
  gradMemL2 := gradMemL2_comp_of_deriv_bounded u hG hM hderiv
  hasWeakGradient := hasWeakGradientOn_comp_open hU hfin u hG hM hderiv

@[simp] theorem compOpen_toFun (hU : IsOpen U) (hfin : volume U ≠ ⊤) (u : H1Function U)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) {M : ℝ} (hM : 0 ≤ M) (hderiv : ∀ t, |deriv G t| ≤ M) :
    (compOpen hU hfin u hG hM hderiv).toFun = fun x => G (u.toFun x) := rfl

@[simp] theorem compOpen_grad (hU : IsOpen U) (hfin : volume U ≠ ⊤) (u : H1Function U)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) {M : ℝ} (hM : 0 ≤ M) (hderiv : ∀ t, |deriv G t| ≤ M) :
    (compOpen hU hfin u hG hM hderiv).grad = fun x i => deriv G (u.toFun x) * u.grad x i := rfl

end PDE.Ch4Infra
