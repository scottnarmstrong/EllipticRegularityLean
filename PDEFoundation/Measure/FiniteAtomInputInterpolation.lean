module

public import PDEFoundation.Measure.FiniteAtomAveragingDensity
public import PDEFoundation.Measure.FiniteAtomCompressedInterpolation
public import PDEFoundation.Measure.LpLimitBound

@[expose] public section

namespace PDE

open Filter MeasureTheory Set Function
open scoped ENNReal Topology

noncomputable section

variable {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [Fintype ι]

/-- Genuine endpoint bounds imply the interpolated bound for every finite atom
input, with output `Lᵖ` membership derived by finite atom averaging density. -/
theorem memLp_and_eLpNorm_operator_finiteAtomInput_le_of_two_four
    (μ : Measure α) (ν : Measure β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : ι → Set α) (hE : ∀ i, MeasurableSet (E i))
    (hEdisj : Pairwise (Disjoint on E))
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν)
    {p M : ℝ} (hp : 2 ≤ p) (hpFour : p ≤ 4) (hM : 1 ≤ M)
    (hTwo : ∀ f : Lp ℝ 2 μ, MemLp f 2 μ →
      eLpNorm (T f) 2 ν ≤ ENNReal.ofReal M * eLpNorm f 2 μ)
    (hFour : ∀ f : Lp ℝ 2 μ, MemLp f 4 μ →
      eLpNorm (T f) 4 ν ≤ ENNReal.ofReal M * eLpNorm f 4 μ)
    (v : ι → ℝ) :
    MemLp (T (finiteAtomInputLinearMap μ E hE v))
        (ENNReal.ofReal p) ν ∧
      eLpNorm (T (finiteAtomInputLinearMap μ E hE v))
          (ENNReal.ofReal p) ν ≤
        ENNReal.ofReal M *
          eLpNorm (finiteDisjointAtomSum E v) (ENNReal.ofReal p) μ := by
  let f₂ : Lp ℝ 2 μ := finiteAtomInputLinearMap μ E hE v
  let fout : β → ℝ := T f₂
  have hfoutTwo : MemLp fout 2 ν := Lp.memLp (T f₂)
  obtain ⟨s, hs⟩ :=
    exists_simpleFunc_tendsto_eLpNorm_finiteAtomAveraging_sub ν fout hfoutTwo
  let A : ℕ → β → ℝ := fun n =>
    finiteAtomAveraging ν (simpleFuncAtomSet (s n)) fout
  have hAMem (n : ℕ) : MemLp (A n) (ENNReal.ofReal p) ν := by
    exact memLp_finiteAtomAveraging ν (simpleFuncAtomSet (s n))
      (measurableSet_simpleFuncAtomSet (s n)) fout (ENNReal.ofReal p)
  have hconv : TendstoInMeasure ν A atTop fout := by
    apply tendstoInMeasure_of_tendsto_eLpNorm (p := (2 : ENNReal)) (by norm_num)
    simpa only [A] using hs
  let B : ENNReal := ENNReal.ofReal M *
    eLpNorm (finiteDisjointAtomSum E v) (ENNReal.ofReal p) μ
  have hinput : MemLp (finiteDisjointAtomSum E v) (ENNReal.ofReal p) μ :=
    memLp_finiteDisjointAtomSum μ E hE v (ENNReal.ofReal p)
  have hBtop : B ≠ ∞ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hinput.eLpNorm_ne_top
  have hbound (n : ℕ) : eLpNorm (A n) (ENNReal.ofReal p) ν ≤ B := by
    exact eLpNorm_finiteAtomAveraging_operator_le_of_two_four
      μ ν E hE hEdisj (simpleFuncAtomSet (s n))
      (measurableSet_simpleFuncAtomSet (s n))
      (pairwise_disjoint_simpleFuncAtomSet (s n)) T
      hp hpFour hM hTwo hFour v
  exact memLp_and_eLpNorm_le_of_tendstoInMeasure
    A fout hAMem hconv (fun _ => B) B hBtop tendsto_const_nhds hbound

end

end PDE
