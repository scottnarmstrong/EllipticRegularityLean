module

public import PDEFoundation.Ambient.HilbertVec
public import PDEFoundation.Geometry.EuclideanBall
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The isoperimetric inequality in dimension one

For `d = 1` the claim reads `|B₁| ≤ H⁰(∂E) = #∂E`; here `|B₁| = 2`, and a bounded nonempty open
subset of the line has the two distinct frontier points `inf E < sup E`.
-/

@[expose] public section

namespace PDE.IsoperimetricProof

open MeasureTheory Set

/-- The coordinate homeomorphism `Vec 1 ≃ ℝ`. -/
noncomputable def coordOne : Vec 1 ≃ₜ ℝ := Homeomorph.funUnique (Fin 1) ℝ

theorem coordOne_apply (x : Vec 1) : coordOne x = x 0 := rfl

theorem euclideanBall_one_eq : euclideanBall (0 : Vec 1) 1 = coordOne ⁻¹' Ioo (-1) 1 := by
  ext x
  simp only [euclideanBall, euclideanSqDist, vecNormSq, vecDot, mem_ofPred_eq, mem_preimage,
    coordOne_apply, Fin.sum_univ_one, sub_zero, one_pow, mem_Ioo]
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg (x 0 + 1), sq_nonneg (x 0 - 1)]
  · rintro ⟨h1, h2⟩
    nlinarith

theorem volume_euclideanBall_one : volume (euclideanBall (0 : Vec 1) 1) = 2 := by
  rw [euclideanBall_one_eq]
  have h := (volume_preserving_funUnique (Fin 1) ℝ).measure_preimage
    (measurableSet_Ioo (a := (-1 : ℝ)) (b := 1)).nullMeasurableSet
  change volume ((MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' Ioo (-1) 1) = 2
  refine h.trans ?_
  rw [Real.volume_Ioo]
  norm_num

/-- A bounded nonempty open subset of `ℝ` has two distinct frontier points. -/
theorem exists_two_frontier_real {S : Set ℝ} (hSo : IsOpen S) (hSb : Bornology.IsBounded S)
    (hSne : S.Nonempty) : ∃ a ∈ frontier S, ∃ b ∈ frontier S, a ≠ b := by
  have hbdA : BddAbove S := hSb.bddAbove
  have hbdB : BddBelow S := hSb.bddBelow
  obtain ⟨x, hx⟩ := hSne
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hSo x hx
  have hlo : sInf S ≤ x - δ / 2 := csInf_le hbdB (hball (by
    rw [Metric.mem_ball, Real.dist_eq]; rw [abs_of_neg (by linarith)]; linarith))
  have hhi : x + δ / 2 ≤ sSup S := le_csSup hbdA (hball (by
    rw [Metric.mem_ball, Real.dist_eq]; rw [abs_of_pos (by linarith)]; linarith))
  have hinf : sInf S ∉ S := by
    intro h
    obtain ⟨ε, hε, hεb⟩ := Metric.isOpen_iff.1 hSo _ h
    have : sInf S - ε / 2 ∈ S := hεb (by
      rw [Metric.mem_ball, Real.dist_eq]; rw [abs_of_neg (by linarith)]; linarith)
    have := csInf_le hbdB this
    linarith
  have hsup : sSup S ∉ S := by
    intro h
    obtain ⟨ε, hε, hεb⟩ := Metric.isOpen_iff.1 hSo _ h
    have : sSup S + ε / 2 ∈ S := hεb (by
      rw [Metric.mem_ball, Real.dist_eq]; rw [abs_of_pos (by linarith)]; linarith)
    have := le_csSup hbdA this
    linarith
  refine ⟨sInf S, ⟨csInf_mem_closure ⟨x, hx⟩ hbdB, ?_⟩, sSup S,
    ⟨csSup_mem_closure ⟨x, hx⟩ hbdA, ?_⟩, by linarith⟩
  · rw [hSo.interior_eq]; exact hinf
  · rw [hSo.interior_eq]; exact hsup

/-- **Dimension one.** The statement of `isoperimetric_inequality` with `d = 1`. -/
theorem isoperimetric_dim_one (d : ℕ) (hd : d = 1) (E : Set (Vec d))
    (hEopen : IsOpen E) (hEbdd : Bornology.IsBounded E) (hEne : E.Nonempty) :
    ENNReal.ofReal ((d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal ^ ((1 : ℝ) / d) *
        (volume E).toReal ^(((d : ℝ) - 1) / d)) ≤
      (μHE[d - 1] : Measure (HilbertVec d)) (Vec.toHilbertVec '' frontier E) := by
  subst hd
  have hlhs : ((1 : ℕ) : ℝ) * (volume (euclideanBall (0 : Vec 1) 1)).toReal ^ ((1 : ℝ) / (1 : ℕ)) *
      (volume E).toReal ^ ((((1 : ℕ) : ℝ) - 1) / (1 : ℕ)) = 2 := by
    rw [volume_euclideanBall_one]
    norm_num
  rw [hlhs, show (1 - 1 : ℕ) = 0 from rfl, Measure.euclideanHausdorffMeasure_zero]
  -- two frontier points
  have hSo : IsOpen (coordOne '' E) := coordOne.isOpenMap E hEopen
  have hSb : Bornology.IsBounded (coordOne '' E) := by
    have hlip : LipschitzWith 1 (fun x : Vec 1 => x 0) :=
      LipschitzWith.eval (α := fun _ : Fin 1 => ℝ) 0
    exact hlip.isBounded_image hEbdd
  obtain ⟨a, ha, b, hb, hab⟩ := exists_two_frontier_real hSo hSb (hEne.image _)
  rw [← coordOne.image_frontier] at ha hb
  obtain ⟨xa, hxa, rfl⟩ := ha
  obtain ⟨xb, hxb, rfl⟩ := hb
  have hne : xa.toHilbertVec ≠ xb.toHilbertVec := fun h => hab (by
    have := congrArg (fun v : HilbertVec 1 => v 0) h
    simpa [coordOne_apply] using this)
  calc ENNReal.ofReal 2 = (μH[0] : Measure (HilbertVec 1)) {xa.toHilbertVec, xb.toHilbertVec} := by
        rw [show ({xa.toHilbertVec, xb.toHilbertVec} : Set (HilbertVec 1)) =
            {xa.toHilbertVec} ∪ {xb.toHilbertVec} from rfl,
          measure_union (disjoint_singleton.2 hne) (measurableSet_singleton _),
          Measure.hausdorffMeasure_zero_singleton, Measure.hausdorffMeasure_zero_singleton]
        norm_num
    _ ≤ _ := measure_mono (by
        rintro z (rfl | rfl)
        · exact mem_image_of_mem _ hxa
        · exact mem_image_of_mem _ hxb)

end PDE.IsoperimetricProof
