module

public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Pairing with bounded measurable functions from indicator values -/

@[expose] public section

namespace PDE
open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

private theorem integrable_simple_mul_of_integrable
    (g : α → ℝ) (hg : Integrable g μ) (s : SimpleFunc α ℝ) :
    Integrable (fun x => s x * g x) μ := by
  apply hg.bdd_mul s.aestronglyMeasurable
  filter_upwards with x
  have h := Finset.le_sup (f := fun c : ℝ => ‖c‖₊) (s.mem_range_self x)
  exact_mod_cast h

/-- An integrable density representing a functional on every measurable-set
indicator also represents it on every bounded measurable function. This is a
conditional approximation lemma; it does not assert `Lᵖ` duality. -/
theorem exists_memLp_and_apply_eq_integral_of_indicator_pairing
    [IsFiniteMeasure μ] {p : ENNReal} [Fact (1 ≤ p)] (hpTop : p ≠ ⊤)
    (L : Lp ℝ p μ →L[ℝ] ℝ) (g : α → ℝ) (hg : Integrable g μ)
    (hIndicator : ∀ (A : Set α) (hA : MeasurableSet A),
      L (indicatorConstLp p hA (measure_ne_top μ A) (1 : ℝ)) = ∫ x in A, g x ∂μ)
    (f : α → ℝ) (hfMeas : Measurable f) (M : ℝ)
    (hfBound : ∀ x, ‖f x‖ ≤ M) :
    ∃ hf : MemLp f p μ, L (hf.toLp f) = ∫ x, f x * g x ∂μ := by
  classical
  have hf : MemLp f p μ := MemLp.of_bound hfMeas.aestronglyMeasurable M
    (Filter.Eventually.of_forall hfBound)
  have hsimple : ∀ s : SimpleFunc α ℝ, ∀ hs : MemLp s p μ,
      L (hs.toLp s) = ∫ x, s x * g x ∂μ := by
    intro s
    induction s using SimpleFunc.induction with
    | @const c A hA =>
      intro hs
      have hfun : ((SimpleFunc.piecewise A hA (SimpleFunc.const α c)
          (SimpleFunc.const α 0)) : α → ℝ) =
          c • A.indicator (fun _ => (1 : ℝ)) := by
        funext x
        by_cases hx : x ∈ A <;> simp [hx]
      have hLp : hs.toLp _ = c • indicatorConstLp p hA (measure_ne_top μ A) (1 : ℝ) := by
        apply Lp.ext
        filter_upwards [hs.coeFn_toLp, Lp.coeFn_smul c
          (indicatorConstLp p hA (measure_ne_top μ A) (1 : ℝ)),
          indicatorConstLp_coeFn (p := p) (hs := hA) (hμs := measure_ne_top μ A) (c := (1 : ℝ))] with x hx hsx hind
        rw [hx, hsx]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [hind]
        simpa only [Pi.smul_apply, smul_eq_mul] using congrFun hfun x
      rw [hLp, map_smul, hIndicator A hA]
      simp only [smul_eq_mul]
      rw [← integral_const_mul]
      rw [hfun]
      simp only [Pi.smul_apply, smul_eq_mul]
      have hi : (fun x => (c * A.indicator (fun _ => (1 : ℝ)) x) * g x) =
          A.indicator (fun x => c * g x) := by
        funext x
        by_cases hx : x ∈ A <;> simp [hx]
      rw [hi, integral_indicator hA]
    | @add s t _ ihs iht =>
      intro hst
      have hs : MemLp s p μ := by
        apply MemLp.of_bound s.aestronglyMeasurable
          (C := (s.range.sup fun c => ‖c‖₊ : NNReal))
        filter_upwards with x
        exact_mod_cast Finset.le_sup (f := fun c : ℝ => ‖c‖₊) (s.mem_range_self x)
      have ht : MemLp t p μ := by
        apply MemLp.of_bound t.aestronglyMeasurable
          (C := (t.range.sup fun c => ‖c‖₊ : NNReal))
        filter_upwards with x
        exact_mod_cast Finset.le_sup (f := fun c : ℝ => ‖c‖₊) (t.mem_range_self x)
      have heq : hst.toLp _ = hs.toLp s + ht.toLp t := by
        exact MemLp.toLp_add hs ht
      rw [heq, map_add, ihs hs, iht ht]
      simp only [SimpleFunc.coe_add, Pi.add_apply, add_mul]
      exact (integral_add (integrable_simple_mul_of_integrable g hg s)
        (integrable_simple_mul_of_integrable g hg t)).symm
  let s : ℕ → SimpleFunc α ℝ := fun n =>
    SimpleFunc.approxOn f hfMeas (Set.range f ∪ {0}) 0 (by simp) n
  have hs : ∀ n, MemLp (s n) p μ :=
    fun n => SimpleFunc.memLp_approxOn_range hfMeas hf n
  have hLp := SimpleFunc.tendsto_approxOn_range_Lp hpTop hfMeas hf
  have hApply : Tendsto (fun n => L ((hs n).toLp (s n))) atTop (𝓝 (L (hf.toLp f))) :=
    (L.continuous.tendsto _).comp hLp
  have hBound : ∀ n x, ‖s n x * g x‖ ≤ (2 * M) * ‖g x‖ := by
    intro n x
    rw [norm_mul]
    have hsn := SimpleFunc.norm_approxOn_zero_le hfMeas
      (show (0 : ℝ) ∈ Set.range f ∪ {0} by simp) x n
    have hsn' : ‖s n x‖ ≤ 2 * M := by
      exact hsn.trans (by nlinarith only [hfBound x])
    exact mul_le_mul_of_nonneg_right hsn' (norm_nonneg _)
  have hPoint : ∀ x, Tendsto (fun n => s n x * g x) atTop (𝓝 (f x * g x)) := by
    intro x
    exact (SimpleFunc.tendsto_approxOn hfMeas
      (show (0 : ℝ) ∈ Set.range f ∪ {0} by simp)
      (subset_closure (by simp : f x ∈ Set.range f ∪ {0}))).mul_const (g x)
  have hIntegral : Tendsto (fun n => ∫ x, s n x * g x ∂μ) atTop
      (𝓝 (∫ x, f x * g x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => (2 * M) * ‖g x‖)
    · intro n
      exact (hs n).aestronglyMeasurable.mul hg.aestronglyMeasurable
    · exact hg.norm.const_mul _
    · intro n
      exact Filter.Eventually.of_forall (hBound n)
    · exact Filter.Eventually.of_forall hPoint
  have hTerms : (fun n => L ((hs n).toLp (s n))) =
      fun n => ∫ x, s n x * g x ∂μ := by
    funext n
    exact hsimple (s n) (hs n)
  rw [hTerms] at hApply
  exact ⟨hf, tendsto_nhds_unique hApply hIntegral⟩

end

end PDE
