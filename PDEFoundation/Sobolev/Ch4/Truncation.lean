module

public import PDEFoundation.Sobolev.Ch4.Local
public import PDEFoundation.Sobolev.H1.Truncation
public import PDEFoundation.Sobolev.H1.LevelSets
public import PDEFoundation.Sobolev.H1.Algebra
public import PDEFoundation.Sobolev.WeakDerivative.Algebra

/-!
# Positive-part truncation of `H¹` on arbitrary open sets

The convex-domain positive-part theorem (`H1Function.positivePartSubConst`) is transported to
an arbitrary open set `U` by the locality principle `hasWeakGradientOn_of_local_ball`:
on every sup-norm cube inside `U` the truncation of the restriction has weak gradient
`1_{u > c} ∇u`.
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory

namespace PDE.Ch4Infra

variable {d : ℕ} {U : Set (Vec d)}

theorem isOpenBoundedConvexDomain_ball (x : Vec d) (r : ℝ) :
    IsOpenBoundedConvexDomain (Metric.ball x r) :=
  ⟨Metric.isOpen_ball, Bornology.IsBounded.isBoundedDomain Metric.isBounded_ball, convex_ball x r⟩

theorem locallyIntegrableOn_of_memL2On {f : Vec d → ℝ} (h : MemL2On U f) :
    LocallyIntegrableOn f U volume :=
  locallyIntegrableOn_of_locallyIntegrable_restrict (h.locallyIntegrable (by norm_num))

/-- The truncated gradient `1_{u > c} ∇u`. -/
noncomputable def posPartGrad (u : H1Function U) (c : ℝ) : Vec d → Vec d :=
  {y | c < u.toFun y}.indicator u.grad

theorem posPartGrad_gradMemL2 (u : H1Function U) (c : ℝ) :
    GradMemL2On U (posPartGrad u c) := by
  intro i
  have hset : NullMeasurableSet {y | c < u.toFun y} (volumeOn U) :=
    nullMeasurableSet_lt aemeasurable_const u.memL2.aemeasurable
  have heq : (fun x => posPartGrad u c x i) =
      {y | c < u.toFun y}.indicator (fun x => u.grad x i) := by
    funext x
    by_cases hx : x ∈ {y | c < u.toFun y} <;> simp [posPartGrad, hx]
  rw [heq]
  refine (u.gradMemL2 i).mono ((u.gradMemL2 i).aestronglyMeasurable.indicator₀ hset)
    (Filter.Eventually.of_forall fun x => norm_indicator_le_norm_self _ _)

/-- The truncated value belongs to `L²(U)` when the level is nonnegative. -/
theorem memL2On_positivePart_of_nonneg (u : H1Function U) {c : ℝ} (hc : 0 ≤ c) :
    MemL2On U (fun x => max (u.toFun x - c) 0) := by
  refine u.memL2.mono ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact ((u.memL2.aestronglyMeasurable.sub aestronglyMeasurable_const).sup
      aestronglyMeasurable_const)
  · simp only [Real.norm_eq_abs]
    rcases le_total (u.toFun x - c) 0 with h | h
    · rw [max_eq_right h, abs_zero]; exact abs_nonneg _
    · rw [max_eq_left h, abs_of_nonneg h]
      exact (by linarith [le_abs_self (u.toFun x)] : u.toFun x - c ≤ |u.toFun x|)

/-- The truncated value belongs to `L²(U)` when `U` has finite measure. -/
theorem memL2On_positivePart_of_finite (u : H1Function U) (hfin : volume U ≠ ⊤) (c : ℝ) :
    MemL2On U (fun x => max (u.toFun x - c) 0) := by
  have : IsFiniteMeasure (volumeOn U) := ⟨by simpa [volumeOn] using hfin.lt_top⟩
  have hc : MemL2On U (fun x => u.toFun x - c) := u.memL2.sub (memLp_const c)
  refine hc.mono ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact ((u.memL2.aestronglyMeasurable.sub aestronglyMeasurable_const).sup
      aestronglyMeasurable_const)
  · simp only [Real.norm_eq_abs]
    rcases le_total (u.toFun x - c) 0 with h | h
    · rw [max_eq_right h, abs_zero]; exact abs_nonneg _
    · rw [max_eq_left h]

/-- **Weak gradient of the positive part on an arbitrary open set.** -/
theorem hasWeakGradientOn_positivePart (hU : IsOpen U) (u : H1Function U) (c : ℝ)
    (hmem : MemL2On U (fun x => max (u.toFun x - c) 0)) :
    HasWeakGradientOn U (fun x => max (u.toFun x - c) 0) (posPartGrad u c) := by
  refine hasWeakGradientOn_of_local_ball hU (locallyIntegrableOn_of_memL2On hmem)
    (fun i => locallyIntegrableOn_of_memL2On (posPartGrad_gradMemL2 u c i)) ?_
  intro x hx
  obtain ⟨r, hr, hsub⟩ := exists_ball_subset hU hx
  exact ⟨r, hr, hsub,
    ((u.restrict Metric.isOpen_ball hsub).positivePartSubConst
      (isOpenBoundedConvexDomain_ball x r) c).hasWeakGradient⟩

/-- Positive-part truncation `(u - c)₊` of an `H¹` function on an arbitrary open set, with
gradient `1_{u > c} ∇u`.  The `L²` membership of the truncated value is a (simple)
hypothesis, discharged by `memL2On_positivePart_of_nonneg` (for `c ≥ 0`) and
`memL2On_positivePart_of_finite` (for finite-measure `U`). -/
noncomputable def positivePartOpen (hU : IsOpen U) (u : H1Function U) (c : ℝ)
    (hmem : MemL2On U (fun x => max (u.toFun x - c) 0)) : H1Function U where
  toFun := fun x => max (u.toFun x - c) 0
  grad := posPartGrad u c
  memL2 := hmem
  gradMemL2 := posPartGrad_gradMemL2 u c
  hasWeakGradient := hasWeakGradientOn_positivePart hU u c hmem

/-- Weak gradient of a shifted function: `∇(u - c) = ∇u`. -/
theorem hasWeakPartialDerivOn_sub_const (hfin : volume U ≠ ⊤) (u : H1Function U) (c : ℝ)
    (i : Fin d) :
    HasWeakPartialDerivOn U i (fun x => u.toFun x - c) (fun x => u.grad x i) := by
  have : IsFiniteMeasure (volumeOn U) := ⟨by simpa [volumeOn] using hfin.lt_top⟩
  have hconst : HasWeakPartialDerivOn U i (fun _ : Vec d => -c) (fun _ => 0) := by
    have := HasWeakPartialDerivOn.of_contDiff (U := U) (i := i)
      (contDiff_const (c := -c) : ContDiff ℝ 1 fun _ : Vec d => -c)
    simpa using this
  have hu := u.hasWeakPartialDerivOn i
  have h := hu.add hconst (u.memL2.locallyIntegrable (by norm_num))
    (locallyIntegrable_const (-c))
    ((u.grad_memL2 i).locallyIntegrable (by norm_num)) (locallyIntegrable_const 0)
  have e1 : (u.toFun + fun _ => -c) = fun x => u.toFun x - c := by
    funext x; simp [sub_eq_add_neg]
  have e2 : ((fun x => u.grad x i) + fun _ => (0 : ℝ)) = fun x => u.grad x i := by
    funext x; simp
  rwa [e1, e2] at h

/-- **The weak gradient vanishes a.e. on every level set**, on any open set of finite measure. -/
theorem grad_ae_zero_on_level_set (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    (u : H1Function U) (c : ℝ) :
    ∀ᵐ x ∂(volumeOn U), u.toFun x = c → u.grad x = 0 := by
  let v₁ := positivePartOpen hU u c (memL2On_positivePart_of_finite u hfin c)
  let v₂ := positivePartOpen hU (-u) (-c) (memL2On_positivePart_of_finite (-u) hfin (-c))
  let v : H1Function U := v₁ - v₂
  have hcoord : ∀ i : Fin d, (fun x => v.grad x i) =ᵐ[volumeOn U] (fun x => u.grad x i) := by
    intro i
    refine HasWeakPartialDerivOn.ae_eq hU
      (locallyIntegrableOn_of_memL2On (v.gradMemL2 i))
      (locallyIntegrableOn_of_memL2On (u.gradMemL2 i)) ?_
      (hasWeakPartialDerivOn_sub_const hfin u c i)
    have h := v.hasWeakPartialDerivOn i
    have hval : v.toFun = fun x => u.toFun x - c := by
      funext x
      change max (u.toFun x - c) 0 - max ((-u).toFun x - -c) 0 = _
      simp only [H1Function.neg_toFun]
      rcases le_total (u.toFun x - c) 0 with h | h
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    rwa [hval] at h
  have hall : ∀ᵐ x ∂(volumeOn U), ∀ i, v.grad x i = u.grad x i := ae_all_iff.mpr hcoord
  filter_upwards [hall] with x hx hxc
  funext i
  rw [← hx i]
  change (posPartGrad u c x - posPartGrad (-u) (-c) x) i = 0
  have h1 : posPartGrad u c x = 0 := by
    simp [posPartGrad, hxc]
  have h2 : posPartGrad (-u) (-c) x = 0 := by
    simp [posPartGrad, hxc]
  simp [h1, h2]

end PDE.Ch4Infra
