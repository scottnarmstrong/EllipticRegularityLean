module

public import PDEFoundation.Monotonicity.FriedlandHayman.Sphere.Positive

/-!
# Friedland--Hayman: normalized sphere measure

`sphFrac d A = σ(A ∩ S) / σ(S)`; monotonicity, subadditivity on disjoint sets, positivity on
open sets meeting the sphere, and a pointwise comparison for supports of continuous functions.
-/

@[expose] public section

open MeasureTheory

namespace PDE.FHLane

noncomputable section

/-- Normalized sphere measure `|A| = σ(A ∩ S)/σ(S)`. -/
noncomputable def sphFrac (d : ℕ) (A : Set (Vec d)) : ℝ :=
  sphereIntegral (0 : Vec d) 1
    ((A ∩ euclideanSphere (0 : Vec d) 1).indicator fun _ => (1 : ℝ)) / sphereArea d

namespace Assem

variable {d : ℕ}

theorem toVec_mem_sphere (ω : Metric.sphere (0 : HilbertVec d) 1) :
    (ω : HilbertVec d).toVec ∈ euclideanSphere (0 : Vec d) 1 := by
  have hn : ‖(ω : HilbertVec d)‖ = 1 := by simp
  have hv : vecEuclideanNorm (ω : HilbertVec d).toVec = 1 := by
    rw [Vec.vecEuclideanNorm_eq_norm_toHilbertVec]; simp
  have : euclideanSqDist (ω : HilbertVec d).toVec 0 = 1 ^ 2 := by
    have h2 := vecEuclideanNorm_sq (ω : HilbertVec d).toVec
    rw [hv] at h2
    simpa [euclideanSqDist] using h2.symm
  exact this

/-- The preimage of `A` on the Hilbert sphere. -/
def pre (A : Set (Vec d)) : Set (Metric.sphere (0 : HilbertVec d) 1) :=
  {ω | (ω : HilbertVec d).toVec ∈ A}

theorem measurableSet_pre {A : Set (Vec d)} (hA : MeasurableSet A) :
    MeasurableSet (pre A : Set (Metric.sphere (0 : HilbertVec d) 1)) :=
  (continuous_toVec.comp continuous_subtype_val).measurable hA

theorem sphereIntegral_indicator_eq {A : Set (Vec d)} (hA : MeasurableSet A) :
    sphereIntegral (0 : Vec d) 1 ((A ∩ euclideanSphere (0 : Vec d) 1).indicator fun _ => (1 : ℝ)) =
      ((volume : Measure (HilbertVec d)).toSphere).real (pre A) := by
  unfold sphereIntegral
  simp only [one_pow, one_mul, zero_add, one_smul]
  rw [← integral_indicator_one (measurableSet_pre hA)]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  by_cases h : (ω : HilbertVec d).toVec ∈ A
  · simp [Set.indicator, pre, h, toVec_mem_sphere ω]
  · simp [Set.indicator, pre, h]

theorem sphereIntegral_indicator_eq' {A : Set (Vec d)} (hA : MeasurableSet A) :
    sphereIntegral (0 : Vec d) 1 (A.indicator fun _ => (1 : ℝ)) =
      ((volume : Measure (HilbertVec d)).toSphere).real (pre A) := by
  unfold sphereIntegral
  simp only [one_pow, one_mul, zero_add, one_smul]
  rw [← integral_indicator_one (measurableSet_pre hA)]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  by_cases h : (ω : HilbertVec d).toVec ∈ A
  · simp [Set.indicator, pre, h]
  · simp [Set.indicator, pre, h]

theorem sphereArea_eq : sphereArea d = ((volume : Measure (HilbertVec d)).toSphere).real Set.univ :=
  rfl

theorem sphereIntegral_indicator_mono {A B : Set (Vec d)} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (h : A ∩ euclideanSphere (0 : Vec d) 1 ⊆ B) :
    sphereIntegral (0 : Vec d) 1 ((A ∩ euclideanSphere (0 : Vec d) 1).indicator fun _ => (1 : ℝ)) ≤
      sphereIntegral (0 : Vec d) 1 ((B ∩ euclideanSphere (0 : Vec d) 1).indicator fun _ => (1 : ℝ)) := by
  rw [sphereIntegral_indicator_eq hA, sphereIntegral_indicator_eq hB]
  refine measureReal_mono (fun ω hω => ?_)
  exact h ⟨hω, toVec_mem_sphere ω⟩

end Assem

theorem sphFrac_mono {d : ℕ} [NeZero d] {A B : Set (Vec d)} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (h : A ∩ euclideanSphere (0 : Vec d) 1 ⊆ B) :
    sphFrac d A ≤ sphFrac d B :=
  div_le_div_of_nonneg_right (Assem.sphereIntegral_indicator_mono hA hB h) sphereArea_pos.le

theorem sphFrac_add_le {d : ℕ} [NeZero d] {A B : Set (Vec d)} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAB : Disjoint A B) : sphFrac d A + sphFrac d B ≤ 1 := by
  unfold sphFrac
  rw [← add_div, div_le_one sphereArea_pos, Assem.sphereIntegral_indicator_eq hA,
    Assem.sphereIntegral_indicator_eq hB, Assem.sphereArea_eq,
    ← measureReal_union _ (Assem.measurableSet_pre hB)]
  · exact measureReal_mono (Set.subset_univ _)
  · exact Set.disjoint_left.2 fun ω h1 h2 => Set.disjoint_left.1 hAB h1 h2

theorem sphFrac_pos {d : ℕ} [NeZero d] {U : Set (Vec d)} (hU : IsOpen U)
    (hne : (U ∩ euclideanSphere (0 : Vec d) 1).Nonempty) : 0 < sphFrac d U := by
  unfold sphFrac
  refine div_pos ?_ sphereArea_pos
  rw [Assem.sphereIntegral_indicator_eq hU.measurableSet, ← Assem.sphereIntegral_indicator_eq' hU.measurableSet]
  exact sphereIntegral_indicator_pos hU hne

theorem sphFrac_lt_one {d : ℕ} [NeZero d] {A U : Set (Vec d)} (hA : MeasurableSet A)
    (hU : IsOpen U) (hne : (U ∩ euclideanSphere (0 : Vec d) 1).Nonempty)
    (hAU : Disjoint A U) : sphFrac d A < 1 := by
  have h1 := sphFrac_add_le hA hU.measurableSet hAU
  have h2 := sphFrac_pos hU hne
  linarith

/-- Pointwise comparison for the support of a continuous function. -/
theorem sphereIntegral_support_le {d : ℕ} {f : Vec d → ℝ} (hf : Continuous f) {Ω : Set (Vec d)}
    (hΩ : MeasurableSet Ω)
    (h : closure {x | x ∈ euclideanSphere (0 : Vec d) 1 ∧ f x ≠ 0} ⊆ Ω) :
    sphereIntegral (0 : Vec d) 1 ({x | f x ≠ 0}.indicator (1 : Vec d → ℝ)) ≤
      sphereIntegral (0 : Vec d) 1 ((Ω ∩ euclideanSphere (0 : Vec d) 1).indicator fun _ => (1 : ℝ)) := by
  have hm : MeasurableSet {x | f x ≠ 0} := (isOpen_ne_fun hf continuous_const).measurableSet
  have e : ({x | f x ≠ 0}.indicator (1 : Vec d → ℝ)) =
      {x | f x ≠ 0}.indicator fun _ => (1 : ℝ) := rfl
  rw [e, Assem.sphereIntegral_indicator_eq' hm, Assem.sphereIntegral_indicator_eq hΩ]
  refine measureReal_mono (fun ω hω => ?_)
  exact h (subset_closure ⟨Assem.toVec_mem_sphere ω, hω⟩)

end

end PDE.FHLane
