module

public import PDEFoundation.Sobolev.Trace.Extension.ExtLp

/-!
# The `W^{1,p}(Ω)` bound for the extension operator

Summing the pointwise bounds of the summands (`ExtData.term_bound`) and using the `L^p` bound of the
majorants (`ExtData.eLpNorm_majorant_le`) gives
`‖E g‖_{W^{1,p}(Ω)} ≤ C ‖g‖_{B^{1-1/p}_{p,p}(∂Ω)}`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

theorem ext_vecEuclideanNorm_sum_le {d : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Vec d) :
    vecEuclideanNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, vecEuclideanNorm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact (vecEuclideanNorm_eq_zero_iff.2 rfl).le
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (vecEuclideanNorm_add_le _ _).trans (add_le_add le_rfl ih)

/-- The gradient of the extension at a point of `Ω` is the sum of the summand gradients. -/
theorem ExtData.classicalGradient_ext (D : ExtData Ω) (hΩo : IsOpen Ω) {p : ℝ} (hp : 1 < p)
    {g : Vec (n + 1) → ℝ} (hg : IsBesov Ω (1 - 1 / p) p g) {x : Vec (n + 1)} (hx : x ∈ Ω) :
    classicalGradient (D.ext g) x = ∑ j, classicalGradient
      (fun y => D.η j y * modelExt n (D.flat j g) ((D.A.chart j).inv y)) x := by
  have hd : ∀ j ∈ (Finset.univ : Finset (Fin D.A.N)), DifferentiableAt ℝ
      (fun y => D.η j y * modelExt n (D.flat j g) ((D.A.chart j).inv y)) x := fun j _ =>
    ((D.contDiffOn_term j (modelExt_contDiffOn hp _ (D.memLp_flat j hp hg))).differentiableOn
      one_ne_zero).differentiableAt (hΩo.mem_nhds hx)
  funext i
  have h1 : D.ext g = fun y => ∑ j, D.η j y * modelExt n (D.flat j g) ((D.A.chart j).inv y) :=
    rfl
  simp only [classicalGradient_apply, h1, Finset.sum_apply]
  rw [fderiv_fun_sum hd, sum_apply]

/-- The `W^{1,p}(Ω)` bound for the extension operator. -/
theorem ExtData.ext_bound (D : ExtData Ω) (hΩo : IsOpen Ω) (_hΩb : Bornology.IsBounded Ω)
    {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ≥0, ∀ g : Vec (n + 1) → ℝ, IsBesov Ω (1 - 1 / p) p g →
      w1pPairNorm Ω p (D.ext g) (classicalGradient (D.ext g)) ≤
        C * besovNorm Ω (1 - 1 / p) p g := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp.le
  choose K hK0 hK using fun j => D.term_bound j
  choose C hC using fun j => D.eLpNorm_majorant_le hp j (hK0 j)
  refine ⟨2 * ∑ j, C j, fun g hg => ?_⟩
  set m : Fin D.A.N → Vec (n + 1) → ℝ := fun j => D.majorant j (K j) (modelExt n (D.flat j g))
    with hm
  have hF : ∀ j, ContDiffOn ℝ 1 (modelExt n (D.flat j g)) (upperHalf n) := fun j =>
    modelExt_contDiffOn hp _ (D.memLp_flat j hp hg)
  have hmnn : ∀ j x, 0 ≤ m j x := fun j x => D.majorant_nonneg j (hK0 j) _ x
  set S : Vec (n + 1) → ℝ := fun x => ∑ j, m j x with hS
  have hSnn : ∀ x, 0 ≤ S x := fun x => Finset.sum_nonneg fun j _ => hmnn j x
  have hpt : ∀ᵐ x ∂(volumeOn Ω), |D.ext g x| ≤ S x ∧
      vecEuclideanNorm (classicalGradient (D.ext g) x) ≤ S x := by
    refine (ae_restrict_iff' hΩo.measurableSet).2 (Eventually.of_forall fun x hx => ?_)
    have h1 : D.ext g x = ∑ j, D.η j x * modelExt n (D.flat j g) ((D.A.chart j).inv x) := rfl
    constructor
    · rw [h1]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      exact Finset.sum_le_sum fun j _ => (hK j _ (hF j) x hx).1
    · rw [D.classicalGradient_ext hΩo hp hg hx]
      refine (ext_vecEuclideanNorm_sum_le _ _).trans ?_
      exact Finset.sum_le_sum fun j _ => (hK j _ (hF j) x hx).2
  have hSle : eLpNorm S (ENNReal.ofReal p) (volumeOn Ω) ≤
      ∑ j, (C j : ℝ≥0∞) * besovNorm Ω (1 - 1 / p) p g := by
    have h1 : S = ∑ j, m j := by funext x; simp [hS]
    rw [h1]
    refine (eLpNorm_sum_le hp1).trans ?_
    exact Finset.sum_le_sum fun j _ => hC j g hg
  have hcd : ContDiffOn ℝ 1 (D.ext g) Ω := D.ext_contDiffOn hp hg
  have haes : AEStronglyMeasurable (D.ext g) (volumeOn Ω) :=
    hcd.continuousOn.aestronglyMeasurable hΩo.measurableSet
  have hgaes : AEStronglyMeasurable (fun x => vecEuclideanNorm (classicalGradient (D.ext g) x))
      (volumeOn Ω) := by
    have hcont : ContinuousOn (fderiv ℝ (D.ext g)) Ω :=
      hcd.continuousOn_fderiv_of_isOpen hΩo le_rfl
    have hgrad : ContinuousOn (classicalGradient (D.ext g)) Ω :=
      continuousOn_pi.2 fun i => hcont.clm_apply continuousOn_const
    exact ((continuous_vecEuclideanNorm (n + 1)).comp_continuousOn hgrad).aestronglyMeasurable
      hΩo.measurableSet
  have hS1 : eLpNorm (D.ext g) (ENNReal.ofReal p) (volumeOn Ω) ≤
      eLpNorm S (ENNReal.ofReal p) (volumeOn Ω) := by
    refine eLpNorm_mono_ae_real haes (hpt.mono fun x hx => ?_)
    simpa [Real.norm_eq_abs] using hx.1
  have hS2 : eLpNorm (fun x => vecEuclideanNorm (classicalGradient (D.ext g) x))
      (ENNReal.ofReal p) (volumeOn Ω) ≤ eLpNorm S (ENNReal.ofReal p) (volumeOn Ω) := by
    refine eLpNorm_mono_ae_real hgaes (hpt.mono fun x hx => ?_)
    simpa [Real.norm_eq_abs, abs_of_nonneg (vecEuclideanNorm_nonneg _)] using hx.2
  unfold w1pPairNorm
  calc _ ≤ eLpNorm S (ENNReal.ofReal p) (volumeOn Ω) + eLpNorm S (ENNReal.ofReal p) (volumeOn Ω) :=
        add_le_add hS1 hS2
    _ ≤ (∑ j, (C j : ℝ≥0∞) * besovNorm Ω (1 - 1 / p) p g) +
          ∑ j, (C j : ℝ≥0∞) * besovNorm Ω (1 - 1 / p) p g := add_le_add hSle hSle
    _ = _ := by
        rw [← Finset.sum_mul]
        push_cast
        ring

end PDE.TraceLane
