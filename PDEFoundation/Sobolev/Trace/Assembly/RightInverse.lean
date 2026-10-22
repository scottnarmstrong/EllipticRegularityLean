module

public import PDEFoundation.Sobolev.Trace.Extension.ExtW1p
public import PDEFoundation.Sobolev.Trace.Extension.Shift
public import PDEFoundation.Sobolev.Trace.Assembly.Basic

/-!
# The right inverse of the trace

`right_inverse_of_extData`: the extension operator `ExtData.extW1p` (manuscript (1.53) composed
with charts, cutoffs and a partition of unity) is linear on the Besov class, bounded from
`B^{1-1/p}_{p,p}(∂Ω)` to `W^{1,p}(Ω)`, and `g` is a trace of its extension: the upward shifts
`ExtData.shift` are `C¹(Ω̄)` approximants converging in `W^{1,p}(Ω)` and on `∂Ω`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

variable {n : ℕ} {Ω : Set (Vec (n + 1))} {p : ℝ}

/-- `g` is a trace of its extension. -/
theorem ExtData.isTraceOf_extW1p (D : ExtData Ω) (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hp : 1 < p) {g : Vec (n + 1) → ℝ} (hg : IsBesov Ω (1 - 1 / p) p g) :
    IsTraceOf Ω p (D.extW1p hΩo hΩb hp g) g := by
  have hgLp : MemLp g (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) := by
    have h := hg.2
    unfold besovNorm at h
    exact lt_of_le_of_lt le_self_add h
  refine ⟨hgLp, fun k => D.shift (1 / ((k : ℝ) + 1)) g,
    fun k => D.shift_contDiffOn hp hg (by positivity), ?_, D.tendsto_shift_boundary hΩo hΩb hp hg⟩
  have hcongr : ∀ k : ℕ, w1pPairNorm Ω p (D.shift (1 / ((k : ℝ) + 1)) g - (D.extW1p hΩo hΩb hp g).toFun)
      (classicalGradient (D.shift (1 / ((k : ℝ) + 1)) g) - (D.extW1p hΩo hΩb hp g).grad) =
      w1pPairNorm Ω p (D.shift (1 / ((k : ℝ) + 1)) g - D.ext g)
        (classicalGradient (D.shift (1 / ((k : ℝ) + 1)) g) - classicalGradient (D.ext g)) := by
    intro k
    refine w1pPairNorm_congr_ae (Eventually.of_forall fun x => by
      rw [D.extW1p_toFun hΩo hΩb hp hg]) ?_
    filter_upwards [ae_restrict_mem hΩo.measurableSet] with x hx
    simp only [Pi.sub_apply, D.extW1p_grad hΩo hΩb hp hg hx]
  simp_rw [hcongr]
  exact D.tendsto_shift_w1p hΩo hΩb hp hg

/-- **Right inverse** of the trace, for a given set of extension data. -/
theorem right_inverse_of_extData (D : ExtData Ω) (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hp : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)] :
    ∃ (C : ℝ≥0) (E : (Vec (n + 1) → ℝ) → W1pFunction Ω (ENNReal.ofReal p)),
      (∀ g h, IsBesov Ω (1 - 1 / p) p g → IsBesov Ω (1 - 1 / p) p h → E (g + h) = E g + E h) ∧
      (∀ (a : ℝ) g, IsBesov Ω (1 - 1 / p) p g → E (a • g) = a • E g) ∧
      ∀ g, IsBesov Ω (1 - 1 / p) p g →
        IsTraceOf Ω p (E g) g ∧
        w1pNorm Ω p (E g) ≤ (C : ℝ≥0∞) * besovNorm Ω (1 - 1 / p) p g := by
  obtain ⟨C, hC⟩ := D.extW1p_bound hΩo hΩb hp
  exact ⟨C, D.extW1p hΩo hΩb hp, fun g h hg hh => D.extW1p_add hΩo hΩb hp hg hh,
    fun a g hg => D.extW1p_smul hΩo hΩb hp a hg,
    fun g hg => ⟨D.isTraceOf_extW1p hΩo hΩb hp hg, hC g hg⟩⟩

end PDE.TraceLane
