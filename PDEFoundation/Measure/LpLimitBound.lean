module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Norm bounds under convergence in measure -/

@[expose] public section

namespace PDE

open Filter MeasureTheory
open scoped ENNReal Topology

/-- A finite varying `L^p` bound passes to a limit in measure. Measurability and
`L^p` membership of the limit are derived from the approximating sequence. -/
theorem memLp_and_eLpNorm_le_of_tendstoInMeasure
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {p : ENNReal}
    (f : ℕ → α → E) (g : α → E)
    (hf : ∀ n, MemLp (f n) p μ)
    (hconv : TendstoInMeasure μ f atTop g)
    (b : ℕ → ENNReal) (B : ENNReal) (hB : B ≠ ∞)
    (hb : Tendsto b atTop (𝓝 B))
    (hbound : ∀ n, eLpNorm (f n) p μ ≤ b n) :
    MemLp g p μ ∧ eLpNorm g p μ ≤ B := by
  have hgMeas : AEStronglyMeasurable g μ :=
    hconv.aestronglyMeasurable fun n => (hf n).aestronglyMeasurable
  have hnorm : eLpNorm g p μ ≤ B := by
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hBlt : B < B + (ε : ENNReal) :=
      ENNReal.lt_add_right hB (ENNReal.coe_ne_zero.mpr hε.ne')
    have hbEventually : ∀ᶠ n in atTop, b n ≤ B + (ε : ENNReal) :=
      hb.eventually_le_const hBlt
    exact eLpNorm_le_of_tendstoInMeasure
      (hbEventually.mono fun n hn => (hbound n).trans hn) hconv
      fun n => (hf n).aestronglyMeasurable
  exact ⟨hnorm.trans_lt (lt_top_iff_ne_top.mpr hB), hnorm⟩

end PDE
