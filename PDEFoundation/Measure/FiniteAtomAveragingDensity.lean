module

public import PDEFoundation.Measure.FiniteAtomAveragingApproximation
public import PDEFoundation.Measure.SimpleFunctionAtoms
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

@[expose] public section

namespace PDE

open Filter MeasureTheory Set Function
open scoped ENNReal Topology

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- Every genuine real `L²` function on a finite measure space admits a
sequence of literal simple-function atom partitions whose averaging operators
converge back to the function in `L²`. -/
theorem exists_simpleFunc_tendsto_eLpNorm_finiteAtomAveraging_sub
    (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → ℝ) (hf : MemLp f 2 μ) :
    ∃ s : ℕ → SimpleFunc α ℝ,
      Tendsto
        (fun n => eLpNorm
          (finiteAtomAveraging μ (simpleFuncAtomSet (s n)) f - f) 2 μ)
        atTop (𝓝 0) := by
  let ε : ℕ → ENNReal := fun n => ((n + 1 : ℕ) : ENNReal)⁻¹
  have hεne (n : ℕ) : ε n ≠ 0 := by
    simp [ε]
  have hex (n : ℕ) : ∃ g : SimpleFunc α ℝ,
      eLpNorm (f - ⇑g) 2 μ < ε n ∧ MemLp g 2 μ :=
    hf.exists_simpleFunc_eLpNorm_sub_lt (by norm_num) (hεne n)
  choose s hs _ using hex
  refine ⟨s, ?_⟩
  have hε : Tendsto ε atTop (𝓝 0) := by
    exact ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  have htwo : Tendsto (fun n => 2 * ε n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul hε (Or.inr (by norm_num))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds htwo (fun _ => bot_le) (fun n => ?_)
  have happ := eLpNorm_finiteAtomAveraging_sub_le_two_mul
    μ (simpleFuncAtomSet (s n))
    (measurableSet_simpleFuncAtomSet (s n))
    (pairwise_disjoint_simpleFuncAtomSet (s n)) f hf
    (simpleFuncAtomValue (s n))
  rw [finiteDisjointAtomSum_simpleFuncAtomSet] at happ
  exact happ.trans (by
    simpa only [mul_comm] using mul_le_mul_right (hs n).le 2)

end

end PDE
