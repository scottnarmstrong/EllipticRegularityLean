module

public import PDEFoundation.FunctionalInequalities.Isoperimetric.Defs
public import PDEFoundation.FunctionalInequalities.SobolevSharpOne.BMStep
public import PDEFoundation.FunctionalInequalities.BrunnMinkowskiProof
public import Mathlib.Geometry.Euclidean.Volume.Measure

/-!
# The Brunn--Minkowski half of the isoperimetric inequality

Conditional on the upper outer Minkowski content bound `MinkowskiBound d` (a separately proved
statement), the isoperimetric inequality for `d ≥ 2` follows from Brunn--Minkowski applied to
`closure E` and a small closed round ball, together with Bernoulli's inequality.
-/

@[expose] public section

namespace PDE.IsoperimetricProof

open MeasureTheory Set
open scoped Pointwise

/-- Upper outer Minkowski content bound (proved separately as `minkowski_content_le`). -/
def MinkowskiBound (d : ℕ) : Prop :=
  ∀ E : Set (HilbertVec d), IsOpen E → Bornology.IsBounded E → HasC1Frontier E →
    (μHE[d - 1] : Measure (HilbertVec d)) (frontier E) ≠ ⊤ → ∀ η : ℝ, 0 < η →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        (μHE[d] : Measure (HilbertVec d)) (Metric.cthickening ε (closure E) \ closure E) ≤
          ENNReal.ofReal ε * ((μHE[d - 1] : Measure (HilbertVec d)) (frontier E) + ENNReal.ofReal η)

variable {d : ℕ}

theorem measurePreserving_toHilbert_hausdorff :
    MeasurePreserving (Internal.toHilbert : Vec d → HilbertVec d) volume μHE[d] := by
  have h := InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := HilbertVec d)
  simp only [finrank_euclideanSpace, Fintype.card_fin] at h
  rw [h]
  exact Internal.measurePreserving_toHilbert

/-- The Hausdorff measure of the image of a closed set is its volume. -/
theorem hausdorff_image_toHilbert {S : Set (Vec d)} (hS : IsClosed S) :
    (μHE[d] : Measure (HilbertVec d)) (Internal.toHilbert '' S) = volume S := by
  have hc : IsClosed ((Internal.toHilbert : Vec d ≃L[ℝ] HilbertVec d) '' S) :=
    (Internal.toHilbert (d := d)).toHomeomorph.isClosed_image.mpr hS
  rw [← measurePreserving_toHilbert_hausdorff.measure_preimage hc.measurableSet.nullMeasurableSet,
    Set.preimage_image_eq _ (Internal.toHilbert (d := d)).injective]

/-- Bernoulli-type lower bound for the closed-ball thickening, in plain reals. -/
theorem ofReal_le_hausdorff_thickening_diff (hd : 2 ≤ d) (E : Set (Vec d))
    (hEbdd : Bornology.IsBounded E) (hEne : E.Nonempty) {ε : ℝ} (hε : 0 < ε)
    (hnull : volume (closure E) = volume E) :
    ENNReal.ofReal ((d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal ^ ((1 : ℝ) / d) * ε *
        (volume E).toReal ^ (((d : ℝ) - 1) / d)) ≤
      (μHE[d] : Measure (HilbertVec d))
        (Metric.cthickening ε (closure (Vec.toHilbertVec '' E)) \
          closure (Vec.toHilbertVec '' E)) := by
  set e : Vec d ≃L[ℝ] HilbertVec d := Internal.toHilbert with he
  have hEimg : Vec.toHilbertVec '' E = e '' E := rfl
  have hcl : closure (e '' E) = e '' closure E := (e.toHomeomorph.image_closure E).symm
  rw [hEimg, hcl]
  set A := closure E with hA
  set B := euclideanClosedBall (0 : Vec d) ε with hB
  have hAc : IsCompact A := hEbdd.isCompact_closure
  have hBc : IsCompact B := isCompact_euclideanClosedBall _ hε.le
  have hAne : A.Nonempty := hEne.closure
  have hBne : B.Nonempty := ⟨0, PDE.SobolevSharp.zero_mem_euclideanClosedBall_zero hε.le⟩
  have hABc : IsCompact (A + B) := hAc.add hBc
  have hbm := PDE.BrunnMinkowskiProof.result d (by omega) A B hAc hBc hAne hBne
  have hA_top : volume A ≠ ⊤ := hAc.measure_lt_top.ne
  have hB_top : volume B ≠ ⊤ := hBc.measure_lt_top.ne
  have hAB_top : volume (A + B) ≠ ⊤ := hABc.measure_lt_top.ne
  have hp : (0 : ℝ) ≤ (1 : ℝ) / d := by positivity
  have hreal := ENNReal.toReal_mono (ENNReal.rpow_ne_top_of_nonneg hp hAB_top) hbm
  rw [ENNReal.toReal_add (ENNReal.rpow_ne_top_of_nonneg hp hA_top)
    (ENNReal.rpow_ne_top_of_nonneg hp hB_top), ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
    ← ENNReal.toReal_rpow] at hreal
  have hb0 : 0 ≤ (volume (euclideanBall (0 : Vec d) 1)).toReal := ENNReal.toReal_nonneg
  have hball : (volume (euclideanBall (0 : Vec d) 1)).toReal * ε ^ d ≤ (volume B).toReal := by
    rw [mul_comm]; exact PDE.SobolevSharp.volume_closedBall_toReal_ge hε
  obtain ⟨k, hk⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  have hBpow : ε * (volume (euclideanBall (0 : Vec d) 1)).toReal ^ ((1 : ℝ) / d)
      ≤ (volume B).toReal ^ ((1 : ℝ) / d) := by
    have h1 := Real.rpow_le_rpow (by positivity) hball hp
    rw [Real.mul_rpow hb0 (by positivity), one_div, Real.pow_rpow_inv_natCast hε.le
      (by omega), mul_comm] at h1
    simpa [one_div] using h1
  have hbm'' : (volume A).toReal ^ ((1 : ℝ) / d) +
      ε * (volume (euclideanBall (0 : Vec d) 1)).toReal ^ ((1 : ℝ) / d) ≤
      (volume (A + B)).toReal ^ ((1 : ℝ) / d) := by linarith [hreal, hBpow]
  have hstep : (d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal ^ ((1 : ℝ) / d) * ε *
        (volume A).toReal ^ (((d : ℝ) - 1) / d) ≤
      (volume (A + B)).toReal - (volume A).toReal := by
    subst hk
    exact PDE.SobolevSharp.bm_step_real k ENNReal.toReal_nonneg hb0 hε.le
      ENNReal.toReal_nonneg hbm''
  -- measure-theoretic comparison
  have hsub : e '' (A + B) ⊆ Metric.cthickening ε (e '' A) := by
    rintro _ ⟨_, ⟨a, ha, z, hz, rfl⟩, rfl⟩
    refine Metric.mem_cthickening_of_dist_le _ (e a) ε _ ⟨a, ha, rfl⟩ ?_
    have hz' : e z ∈ Metric.closedBall (e 0) ε := by
      have : z ∈ e ⁻¹' Metric.closedBall (e 0) ε := by
        rw [show (e : Vec d → HilbertVec d) = Internal.toHilbert from rfl,
          Internal.preimage_closedBall_toHilbert 0 hε.le]
        exact hz
      exact this
    rw [map_add, dist_self_add_left]
    simpa [map_zero, Metric.mem_closedBall, dist_zero_right] using hz'
  have hAcl : IsClosed (e '' A) := e.toHomeomorph.isClosed_image.mpr isClosed_closure
  have hmA : (μHE[d] : Measure (HilbertVec d)) (e '' A) = volume A := hausdorff_image_toHilbert isClosed_closure
  have hmAB : (μHE[d] : Measure (HilbertVec d)) (e '' (A + B)) = volume (A + B) :=
    hausdorff_image_toHilbert hABc.isClosed
  have hcont : e '' A ⊆ Metric.cthickening ε (e '' A) := Metric.self_subset_cthickening _
  rw [measure_sdiff hcont hAcl.measurableSet.nullMeasurableSet (by rw [hmA]; exact hA_top)]
  have hle : volume (A + B) - volume A ≤
      (μHE[d] : Measure (HilbertVec d)) (Metric.cthickening ε (e '' A)) -
        (μHE[d] : Measure (HilbertVec d)) (e '' A) := by
    rw [← hmA, ← hmAB]
    exact tsub_le_tsub_right (measure_mono hsub) _
  refine le_trans ?_ hle
  rw [← hnull]
  have hrew : volume (A + B) - volume A =
      ENNReal.ofReal ((volume (A + B)).toReal - (volume A).toReal) := by
    rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hAB_top,
      ENNReal.ofReal_toReal hA_top]
  rw [hrew]
  exact ENNReal.ofReal_le_ofReal hstep

/-- **Isoperimetric inequality for `d ≥ 2`**, conditional on the Minkowski content bound. -/
theorem isoperimetric_of_minkowskiBound (d : ℕ) (hd : 2 ≤ d) (hM : MinkowskiBound d)
    (E : Set (Vec d)) (hEopen : IsOpen E) (hEbdd : Bornology.IsBounded E) (hEne : E.Nonempty)
    (hE : HasC1Boundary E) :
    ENNReal.ofReal ((d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal ^ ((1 : ℝ) / d) *
        (volume E).toReal ^(((d : ℝ) - 1) / d)) ≤
      (μHE[d - 1] : Measure (HilbertVec d)) (Vec.toHilbertVec '' frontier E) := by
  set e : Vec d ≃L[ℝ] HilbertVec d := Internal.toHilbert with he
  have hEimg : Vec.toHilbertVec '' E = e '' E := rfl
  have hfr : Vec.toHilbertVec '' frontier E = frontier (Vec.toHilbertVec '' E) := by
    rw [hEimg]; exact e.toHomeomorph.image_frontier E
  rw [hfr]
  set H := (μHE[d - 1] : Measure (HilbertVec d)) (frontier (Vec.toHilbertVec '' E)) with hH
  by_cases htop : H = ⊤
  · rw [htop]; exact le_top
  have hopen : IsOpen (Vec.toHilbertVec '' E) := by
    rw [hEimg]; exact e.toHomeomorph.isOpenMap E hEopen
  have hbdd : Bornology.IsBounded (Vec.toHilbertVec '' E) := by
    rw [hEimg]; exact (e.toContinuousLinearMap.lipschitzWith).isBounded_image hEbdd
  have hC1 := hasC1Frontier_toHilbertVec hE
  -- the frontier is null
  have hnullH : (μHE[d] : Measure (HilbertVec d)) (frontier (Vec.toHilbertVec '' E)) = 0 := by
    rcases Measure.euclideanHausdorffMeasure_zero_or_top (d₁ := d - 1) (d₂ := d) (by omega)
      (frontier (Vec.toHilbertVec '' E)) with h | h
    · exact h
    · exact absurd h htop
  have hnull : volume (closure E) = volume E := by
    have hfv : volume (frontier E) = 0 := by
      rw [← hausdorff_image_toHilbert isClosed_frontier, show (Internal.toHilbert '' frontier E) =
        frontier (Vec.toHilbertVec '' E) from hfr]
      exact hnullH
    refine le_antisymm ?_ (measure_mono subset_closure)
    calc volume (closure E) ≤ volume (E ∪ frontier E) :=
          measure_mono (by rw [closure_eq_self_union_frontier])
      _ ≤ volume E + volume (frontier E) := measure_union_le _ _
      _ = volume E := by rw [hfv, add_zero]
  -- cancel epsilon and let eta tend to 0
  set K := (d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal ^ ((1 : ℝ) / d) *
        (volume E).toReal ^ (((d : ℝ) - 1) / d) with hK
  refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
  obtain ⟨ε₀, hε₀, hmink⟩ := hM _ hopen hbdd hC1 htop (η : ℝ) (by exact_mod_cast hη)
  have h1 := ofReal_le_hausdorff_thickening_diff hd E hEbdd hEne hε₀ hnull
  have h2 := hmink ε₀ hε₀ le_rfl
  have h3 := h1.trans h2
  have hrw : (d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal ^ ((1 : ℝ) / d) * ε₀ *
        (volume E).toReal ^ (((d : ℝ) - 1) / d) = ε₀ * K := by rw [hK]; ring
  rw [hrw, ENNReal.ofReal_mul hε₀.le] at h3
  have hne0 : ENNReal.ofReal ε₀ ≠ 0 := by simpa using hε₀
  have h4 := (ENNReal.mul_le_mul_iff_right hne0 ENNReal.ofReal_ne_top).mp h3
  simpa using h4

end PDE.IsoperimetricProof
