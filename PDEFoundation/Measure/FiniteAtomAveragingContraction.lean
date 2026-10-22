module

public import PDEFoundation.Measure.FiniteAtomAverageLp
public import PDEFoundation.Measure.FiniteDisjointAtomLp

@[expose] public section

namespace PDE

open MeasureTheory Set Function
open scoped ENNReal BigOperators

noncomputable section

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]

/-- The finite atom averaging function, written as the literal disjoint atom
sum of the averages on its atoms. -/
def finiteAtomAveraging (μ : Measure α) (E : ι → Set α) (f : α → ℝ) : α → ℝ :=
  finiteDisjointAtomSum E (fun i => finiteAtomAverage μ (E i) f)

/-- A finite atom averaging function belongs to every extended `Lᵖ` space on
a finite measure space. -/
theorem memLp_finiteAtomAveraging
    (μ : Measure α) [IsFiniteMeasure μ]
    (E : ι → Set α) (hE : ∀ i, MeasurableSet (E i))
    (f : α → ℝ) (p : ENNReal) :
    MemLp (finiteAtomAveraging μ E f) p μ := by
  exact memLp_finiteDisjointAtomSum μ E hE
    (fun i => finiteAtomAverage μ (E i) f) p

/-- Averaging a real function on finitely many measurable pairwise disjoint
atoms contracts its `Lᵖ` seminorm for every real `p ≥ 1`. -/
theorem eLpNorm_finiteAtomAveraging_le
    (μ : Measure α) [IsFiniteMeasure μ]
    (E : ι → Set α) (hE : ∀ i, MeasurableSet (E i))
    (hdisj : Pairwise (Disjoint on E))
    (f : α → ℝ) {p : ℝ} (hp : 1 ≤ p)
    (hf : MemLp f (ENNReal.ofReal p) μ) :
    eLpNorm (finiteAtomAveraging μ E f) (ENNReal.ofReal p) μ ≤
      eLpNorm f (ENNReal.ofReal p) μ := by
  let g : α → ℝ := fun x => |f x| ^ p
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hg : Integrable g μ := by
    simpa only [g, Real.norm_eq_abs, ENNReal.toReal_ofReal hp0.le] using
      hf.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hp0).ne'
        ENNReal.ofReal_ne_top
  have hsum :
      ∑ i, ∫ x in E i, g x ∂μ ≤ ∫ x, g x ∂μ := by
    rw [← integral_iUnion_fintype hE hdisj (fun _ => hg.integrableOn)]
    exact setIntegral_le_integral hg
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg _) _)
  have hatom :
      ∑ i, (μ (E i)).toReal * |finiteAtomAverage μ (E i) f| ^ p ≤
        ∑ i, ∫ x in E i, g x ∂μ := by
    exact Finset.sum_le_sum fun i _ =>
      measureReal_mul_abs_finiteAtomAverage_rpow_le μ (E i) f hp
        (hf.restrict (E i))
  have hpow :
      (eLpNorm (finiteAtomAveraging μ E f) (ENNReal.ofReal p) μ).toReal ^ p ≤
        (eLpNorm f (ENNReal.ofReal p) μ).toReal ^ p := by
    calc
      (eLpNorm (finiteAtomAveraging μ E f) (ENNReal.ofReal p) μ).toReal ^ p =
          ∑ i, (μ (E i)).toReal * |finiteAtomAverage μ (E i) f| ^ p :=
        eLpNorm_finiteDisjointAtomSum_toReal_rpow μ E hE hdisj
          (fun i => finiteAtomAverage μ (E i) f) hp0
      _ ≤ ∑ i, ∫ x in E i, g x ∂μ := hatom
      _ ≤ ∫ x, g x ∂μ := hsum
      _ = (eLpNorm f (ENNReal.ofReal p) μ).toReal ^ p := by
        symm
        simpa only [g, Real.norm_eq_abs] using
          toReal_eLpNorm_ofReal_rpow_eq_integral_rpow_norm hp0 hf
  have hreal :
      (eLpNorm (finiteAtomAveraging μ E f) (ENNReal.ofReal p) μ).toReal ≤
        (eLpNorm f (ENNReal.ofReal p) μ).toReal :=
    (Real.rpow_le_rpow_iff ENNReal.toReal_nonneg ENNReal.toReal_nonneg hp0).mp hpow
  exact (ENNReal.toReal_le_toReal
    (memLp_finiteAtomAveraging μ E hE f (ENNReal.ofReal p)).eLpNorm_ne_top
    hf.eLpNorm_ne_top).mp hreal

end

end PDE
