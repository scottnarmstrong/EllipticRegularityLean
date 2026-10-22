module

public import PDEFoundation.Sobolev.Trace.Chart.FactsTopology
public import PDEFoundation.Analysis.HilbertDictionary

/-!
# Surface measure of a graph: set-function bounds

For a graph chart `φ` with boundary parametrisation `Ψ₀ x' = φ.map (x', 0)`, the surface measure
of `Ψ₀ '' A` is comparable with the Lebesgue measure of `A`:
`|A| ≤ σ(Ψ₀ '' A) ≤ √(1+L²)^n |A|`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ}

/-- `μHE[d]` scales under Lipschitz maps by `K^d`. -/
theorem euclideanHausdorffMeasure_image_le {X Y : Type*} [EMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] {f : X → Y} {K : NNReal}
    (hf : LipschitzWith K f) (d : ℕ) (s : Set X) :
    (μHE[d] : Measure Y) (f '' s) ≤ (K : ℝ≥0∞) ^ d * (μHE[d] : Measure X) s := by
  simp only [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def,
    smul_eq_mul]
  calc _ ≤ _ * ((K : ℝ≥0∞) ^ (d : ℝ) * μH[(d : ℝ)] s) :=
        mul_le_mul_right (hf.hausdorffMeasure_image_le (Nat.cast_nonneg d) s) _
    _ = _ := by rw [ENNReal.rpow_natCast]; ring

/-- Euclidean Hausdorff measure on `HilbertVec n` is Lebesgue measure. -/
theorem euclideanHausdorffMeasure_hilbertVec :
    (μHE[n] : Measure (HilbertVec n)) = volume := by
  simpa using (InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := HilbertVec n))

/-- The Lebesgue measure of the Hilbert image of a measurable set. -/
theorem volume_toHilbertVec_image {A : Set (Vec n)} (hA : MeasurableSet A) :
    (volume : Measure (HilbertVec n)) (Vec.toHilbertVec '' A) = volume A := by
  have : Vec.toHilbertVec '' A = (PDE.Internal.toHilbert.symm : HilbertVec n → Vec n) ⁻¹' A := by
    ext w
    simp only [mem_image, mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩; simpa using hx
    · intro h; exact ⟨w.toVec, h, rfl⟩
  rw [this]
  exact PDE.Internal.measurePreserving_toHilbert_symm.measure_preimage hA.nullMeasurableSet

theorem dist_toHilbertVec (a b : Vec n) :
    dist a.toHilbertVec b.toHilbertVec = vecEuclideanNorm (a - b) := by
  rw [dist_eq_norm, Vec.vecEuclideanNorm_eq_norm_toHilbertVec]; rfl

theorem dist_hilbertVec (y y' : HilbertVec n) :
    dist y y' = vecEuclideanNorm (y.toVec - y'.toVec) := by
  rw [dist_eq_norm, HilbertVec.norm_eq_vecEuclideanNorm]; rfl

namespace GraphChart

variable {Ω : Set (Vec (n + 1))}

/-- The boundary parametrisation `x' ↦ Ψ(x', 0)` transported to Hilbert vectors. -/
noncomputable def hilbertGraph (φ : GraphChart Ω) (y : HilbertVec n) : HilbertVec (n + 1) :=
  (φ.map (y.toVec, 0)).toHilbertVec

/-- The projection `Ψ(x', t) ↦ x'` transported to Hilbert vectors. -/
noncomputable def hilbertProj (φ : GraphChart Ω) (w : HilbertVec (n + 1)) : HilbertVec n :=
  (φ.inv w.toVec).1.toHilbertVec

theorem lipschitzWith_hilbertGraph (φ : GraphChart Ω) :
    LipschitzWith (Real.toNNReal (Real.sqrt (1 + φ.L ^ 2))) φ.hilbertGraph := by
  refine LipschitzWith.of_dist_le_mul fun y y' => ?_
  rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _), hilbertGraph, hilbertGraph, dist_toHilbertVec,
    dist_hilbertVec]
  exact vecEuclideanNorm_graphMap_zero_sub_le φ.γ_lip _ _

theorem lipschitzWith_hilbertProj (φ : GraphChart Ω) : LipschitzWith 1 φ.hilbertProj := by
  refine LipschitzWith.of_dist_le_mul fun w w' => ?_
  rw [NNReal.coe_one, one_mul, dist_hilbertVec, hilbertProj, hilbertProj]
  have h := vecEuclideanNorm_sub_le_graphMap (i := φ.i) (γ := φ.γ) (sgn := φ.sgn)
    (φ.inv w.toVec) (φ.inv w'.toVec)
  have e1 : graphMap φ.i φ.γ φ.sgn (φ.inv w.toVec) = w.toVec :=
    graphMap_graphMapInv φ.sgn_sq _
  have e2 : graphMap φ.i φ.γ φ.sgn (φ.inv w'.toVec) = w'.toVec :=
    graphMap_graphMapInv φ.sgn_sq _
  rw [e1, e2] at h
  rw [dist_hilbertVec w w']
  exact h

theorem hilbertProj_hilbertGraph (φ : GraphChart Ω) (y : HilbertVec n) :
    φ.hilbertProj (φ.hilbertGraph y) = y := by
  have : φ.inv (φ.map (y.toVec, 0)) = (y.toVec, 0) := graphMapInv_graphMap φ.sgn_sq _
  simp only [hilbertProj, hilbertGraph, HilbertVec.toVec_toHilbertVec]
  rw [this]; rfl

/-- Two-sided comparison of the surface measure of a graph piece with its parameter volume. -/
theorem volume_le_hausdorff_graph (φ : GraphChart Ω) {A : Set (Vec n)} (hA : MeasurableSet A) :
    volume A ≤ (μHE[n] : Measure (HilbertVec (n + 1)))
      (Vec.toHilbertVec '' ((fun x' => φ.map (x', 0)) '' A)) := by
  have himg : Vec.toHilbertVec '' ((fun x' => φ.map (x', 0)) '' A) =
      φ.hilbertGraph '' (Vec.toHilbertVec '' A) := by
    ext w
    simp only [mem_image]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  have h1 := euclideanHausdorffMeasure_image_le φ.lipschitzWith_hilbertProj n
    (φ.hilbertGraph '' (Vec.toHilbertVec '' A))
  have h2 : φ.hilbertProj '' (φ.hilbertGraph '' (Vec.toHilbertVec '' A)) =
      Vec.toHilbertVec '' A := by
    rw [image_image]
    simp only [hilbertProj_hilbertGraph, image_id']
  rw [h2] at h1
  simp only [ENNReal.coe_one, one_pow, one_mul] at h1
  rw [himg, ← volume_toHilbertVec_image hA]
  rw [euclideanHausdorffMeasure_hilbertVec] at h1
  exact h1

theorem hausdorff_graph_le_volume (φ : GraphChart Ω) {A : Set (Vec n)} (hA : MeasurableSet A) :
    (μHE[n] : Measure (HilbertVec (n + 1)))
      (Vec.toHilbertVec '' ((fun x' => φ.map (x', 0)) '' A)) ≤
      ENNReal.ofReal (Real.sqrt (1 + φ.L ^ 2) ^ n) * volume A := by
  have himg : Vec.toHilbertVec '' ((fun x' => φ.map (x', 0)) '' A) =
      φ.hilbertGraph '' (Vec.toHilbertVec '' A) := by
    ext w
    simp only [mem_image]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  have h1 := euclideanHausdorffMeasure_image_le φ.lipschitzWith_hilbertGraph n
    (Vec.toHilbertVec '' A)
  rw [himg]
  rw [euclideanHausdorffMeasure_hilbertVec, volume_toHilbertVec_image hA] at h1
  rw [ENNReal.ofReal_pow (Real.sqrt_nonneg _)]
  exact h1

end GraphChart

end PDE.TraceLane
