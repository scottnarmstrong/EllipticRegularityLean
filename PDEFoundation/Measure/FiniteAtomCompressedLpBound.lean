module

public import PDEFoundation.Measure.FiniteAtomAveragingContraction
public import PDEFoundation.Measure.FiniteAtomOperatorCompression

@[expose] public section

namespace PDE

open MeasureTheory Set Function
open scoped ENNReal BigOperators

noncomputable section

variable {α β ι κ : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [Fintype ι] [Fintype κ]

/-- A genuine `Lᵖ` bound for an `L²` operator descends to the exact weighted
`p`-moment bound for its finite atom-average compression. -/
theorem finiteAtomOperatorMatrix_weighted_rpow_le
    (μ : Measure α) (ν : Measure β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : ι → Set α) (hE : ∀ i, MeasurableSet (E i))
    (hEdisj : Pairwise (Disjoint on E))
    (H : κ → Set β) (hH : ∀ j, MeasurableSet (H j))
    (hHdisj : Pairwise (Disjoint on H))
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν)
    {q M : ℝ} (hq : 1 ≤ q) (hM : 0 ≤ M)
    (hT : ∀ f : Lp ℝ 2 μ,
      MemLp f (ENNReal.ofReal q) μ →
      eLpNorm (T f) (ENNReal.ofReal q) ν ≤
        ENNReal.ofReal M * eLpNorm f (ENNReal.ofReal q) μ)
    (v : ι → ℝ) :
    ∑ j, (ν (H j)).toReal *
        |∑ i, finiteAtomOperatorMatrix μ ν E hE H T j i * v i| ^ q ≤
      M ^ q * ∑ i, (μ (E i)).toReal * |v i| ^ q := by
  let f₂ : Lp ℝ 2 μ := finiteAtomInputLinearMap μ E hE v
  let fatom : α → ℝ := finiteDisjointAtomSum E v
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hfatom : MemLp fatom (ENNReal.ofReal q) μ :=
    memLp_finiteDisjointAtomSum μ E hE v (ENNReal.ofReal q)
  have hfrep : (f₂ : α → ℝ) =ᵐ[μ] fatom :=
    finiteAtomInputLinearMap_ae_eq_finiteDisjointAtomSum μ E hE v
  have hf₂q : MemLp f₂ (ENNReal.ofReal q) μ :=
    MemLp.ae_eq hfrep.symm hfatom
  have hTbound := hT f₂ hf₂q
  have hTrhsTop :
      ENNReal.ofReal M * eLpNorm f₂ (ENNReal.ofReal q) μ < ∞ :=
    ENNReal.mul_lt_top (by simp) hf₂q.eLpNorm_lt_top
  have hTfTop : eLpNorm (T f₂) (ENNReal.ofReal q) ν < ∞ :=
    lt_of_le_of_lt hTbound hTrhsTop
  have hTfq : MemLp (T f₂) (ENNReal.ofReal q) ν :=
    (hTfTop)
  have havg := eLpNorm_finiteAtomAveraging_le
    ν H hH hHdisj (T f₂) hq hTfq
  have hTreal :
      (eLpNorm (T f₂) (ENNReal.ofReal q) ν).toReal ≤
        M * (eLpNorm f₂ (ENNReal.ofReal q) μ).toReal := by
    have := (ENNReal.toReal_le_toReal hTfq.eLpNorm_ne_top hTrhsTop.ne).mpr hTbound
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM] using this
  have havgreal :
      (eLpNorm (finiteAtomAveraging ν H (T f₂))
        (ENNReal.ofReal q) ν).toReal ≤
        (eLpNorm (T f₂) (ENNReal.ofReal q) ν).toReal :=
    (ENNReal.toReal_le_toReal
      (memLp_finiteAtomAveraging ν H hH (T f₂)
        (ENNReal.ofReal q)).eLpNorm_ne_top
      hTfq.eLpNorm_ne_top).mpr havg
  have hnorm :
      (eLpNorm (finiteAtomAveraging ν H (T f₂))
        (ENNReal.ofReal q) ν).toReal ^ q ≤
        M ^ q * (eLpNorm f₂ (ENNReal.ofReal q) μ).toReal ^ q := by
    calc
      _ ≤ (eLpNorm (T f₂) (ENNReal.ofReal q) ν).toReal ^ q :=
        Real.rpow_le_rpow ENNReal.toReal_nonneg havgreal hq0.le
      _ ≤ (M * (eLpNorm f₂ (ENNReal.ofReal q) μ).toReal) ^ q :=
        Real.rpow_le_rpow ENNReal.toReal_nonneg hTreal hq0.le
      _ = M ^ q * (eLpNorm f₂ (ENNReal.ofReal q) μ).toReal ^ q :=
        Real.mul_rpow hM ENNReal.toReal_nonneg
  have hinNorm :
      (eLpNorm f₂ (ENNReal.ofReal q) μ).toReal ^ q =
        ∑ i, (μ (E i)).toReal * |v i| ^ q := by
    rw [eLpNorm_congr_ae hfrep]
    exact eLpNorm_finiteDisjointAtomSum_toReal_rpow
      μ E hE hEdisj v hq0
  have houtNorm :
      (eLpNorm (finiteAtomAveraging ν H (T f₂))
        (ENNReal.ofReal q) ν).toReal ^ q =
        ∑ j, (ν (H j)).toReal *
          |∑ i, finiteAtomOperatorMatrix μ ν E hE H T j i * v i| ^ q := by
    unfold finiteAtomAveraging
    rw [eLpNorm_finiteDisjointAtomSum_toReal_rpow
      ν H hH hHdisj
      (fun j => finiteAtomAverage ν (H j) (T f₂)) hq0]
    apply Finset.sum_congr rfl
    intro j _
    rw [finiteAtomAverage_operator_input_eq_matrix_mul
      μ ν E hE H T v j]
  rw [← houtNorm, ← hinNorm]
  exact hnorm

end

end PDE
