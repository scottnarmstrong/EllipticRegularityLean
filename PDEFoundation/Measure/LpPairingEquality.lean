module

public import PDEFoundation.Measure.LpBoundedPairing
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Analysis.Normed.Operator.Mul

/-! # Identification of a functional with the genuine `Lᵖ` pairing -/

@[expose] public section

namespace PDE
open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Once an indicator-representing integrable density has genuine conjugate
`Lᵖ` membership, simple-function approximation identifies the whole continuous
functional with its standard integral pairing. Membership is an explicit
premise of this conditional helper, not asserted by this lemma. -/
theorem lpFunctional_eq_pairing_of_indicator_density
    [IsFiniteMeasure μ] {p q : ENNReal} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate q p] (hpTop : p ≠ ⊤)
    (L : Lp ℝ p μ →L[ℝ] ℝ) {g : α → ℝ} (hgInt : Integrable g μ)
    (hg : MemLp g q μ)
    (hIndicator : ∀ (A : Set α) (hA : MeasurableSet A),
      L (indicatorConstLp p hA (measure_ne_top μ A) (1 : ℝ)) = ∫ x in A, g x ∂μ) :
    L = (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p (hg.toLp g) := by
  classical
  let J : Lp ℝ p μ →L[ℝ] ℝ :=
    (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p (hg.toLp g)
  apply ContinuousLinearMap.ext
  intro f
  have hfMeas : Measurable (f : α → ℝ) := (Lp.stronglyMeasurable f).measurable
  have hf : MemLp (f : α → ℝ) p μ := Lp.memLp f
  let s : ℕ → SimpleFunc α ℝ := fun n =>
    SimpleFunc.approxOn f hfMeas (Set.range f ∪ {0}) 0 (by simp) n
  have hs : ∀ n, MemLp (s n) p μ :=
    fun n => SimpleFunc.memLp_approxOn_range hfMeas hf n
  have hLp : Tendsto (fun n => (hs n).toLp (s n)) atTop (𝓝 f) := by
    have h := SimpleFunc.tendsto_approxOn_range_Lp hpTop hfMeas hf
    rwa [Lp.toLp_coeFn f hf] at h
  have heq (n : ℕ) : L ((hs n).toLp (s n)) = J ((hs n).toLp (s n)) := by
    let C : ℝ := ↑((s n).range.sup fun c => ‖c‖₊)
    have hbound : ∀ x, ‖s n x‖ ≤ C := by
      intro x
      exact_mod_cast Finset.le_sup (f := fun c : ℝ => ‖c‖₊) ((s n).mem_range_self x)
    rcases exists_memLp_and_apply_eq_integral_of_indicator_pairing hpTop
        L g hgInt hIndicator (s n) (s n).measurable C hbound with ⟨hs', hEq⟩
    rw [show hs'.toLp (s n) = (hs n).toLp (s n) from rfl] at hEq
    rw [hEq]
    change _ = (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p (hg.toLp g) _
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp, (hs n).coeFn_toLp] with x hgx hsx
    simp [hgx, hsx, mul_comm]
  have hL := (L.continuous.tendsto f).comp hLp
  have hJ := (J.continuous.tendsto f).comp hLp
  have hseq : (fun n => L ((hs n).toLp (s n))) =
      fun n => J ((hs n).toLp (s n)) := funext heq
  change Tendsto (fun n => L ((hs n).toLp (s n))) atTop (𝓝 (L f)) at hL
  change Tendsto (fun n => J ((hs n).toLp (s n))) atTop (𝓝 (J f)) at hJ
  rw [hseq] at hL
  exact tendsto_nhds_unique hL hJ

end

end PDE
