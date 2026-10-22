module

public import PDEFoundation.Analysis.Gehring.Tail

/-!
# The tail estimate for a subfamily of a Whitney family

Family-general form (`lintegral_gt_le_family`): for any subfamily `T` of a Whitney family `F` of
`E_t`, any set `D` with `{g > t} ∩ D ⊆ ⋃_{i ∈ T} Q_i` a.e., and the reverse Hölder inequality
required only for the cubes of `T`,
`∫_{{g>t} ∩ D} g ≤ A H t |E_t| + B N_σ ∫_{E_t} h`.
-/

@[expose] public section

namespace PDE.Gehring

open MeasureTheory Set
open scoped ENNReal

variable {d : ℕ}

/-- **Family-general tail estimate** (Lemma 4.6, cover form): `W` is a Whitney cover of
`E_t` such that the averaging bound `(⨍_{σQ_i} g^θ)^{1/θ} ≤ H t` holds for the cubes of `T`. -/
theorem lintegral_gt_le_cover (hd : 0 < d) {g h : Vec d → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (hh0 : ∀ x, 0 ≤ h x) (hg : Integrable g volume) (hh : LocallyIntegrable h volume)
    {σ A B t : ℝ} (hσ : σ = 2 ∨ σ = 4) (hA : 0 ≤ A) (hB : 0 ≤ B) (ht : 0 ≤ t)
    (W : WhitneyCover (gehringE g t) σ) (T : Set W.ι) (D : Set (Vec d))
    (hav : ∀ i ∈ T, (integralAverage (centeredAxisCube (W.center i) (σ * W.side i / 2))
        (fun x => g x ^ gehringTheta d)) ^ (((d : ℝ) + 1) / d) ≤ gehringH d * t)
    (hrh : ∀ i ∈ T, GehringRH d σ A B g h (W.center i) (W.side i / 2))
    (hcov : ∀ᵐ x ∂(volume : Measure (Vec d)),
      x ∈ {x | t < g x} ∩ D → x ∈ ⋃ i ∈ T, W.cube i) :
    ∫⁻ x in {x | t < g x} ∩ D, ENNReal.ofReal (g x) ≤
      ENNReal.ofReal (A * gehringH d * t) * volume (gehringE g t) +
        ENNReal.ofReal (B * gehringN σ d) * ∫⁻ x in gehringE g t, ENNReal.ofReal (h x) := by
  classical
  have hσ0 : 0 ≤ σ := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hσ1 : 1 / 2 ≤ σ := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hEmeas : MeasurableSet (gehringE g t) := (isOpen_gehringE hd g ht).measurableSet
  have hdil : ∀ i, W.dilate σ i ⊆ gehringE g t := fun i => W.dilate_subset (by linarith) i
  have hdisj : Pairwise (Function.onFun Disjoint fun i : T => W.cube i) := fun i j hij =>
    W.cube_pairwise_disjoint (fun h => hij (Subtype.ext h))
  -- step 1: reduce to the union of the cubes and split
  have h1 : ∫⁻ x in {x | t < g x} ∩ D, ENNReal.ofReal (g x) ≤
      ∑' i : T, ∫⁻ x in W.cube i, ENNReal.ofReal (g x) := by
    rw [← lintegral_iUnion (fun i : T => W.measurableSet_cube i) hdisj]
    refine lintegral_mono_set' ?_
    filter_upwards [hcov] with x hx hxs
    have := hx hxs
    rwa [← Set.biUnion_eq_iUnion T (fun i _ => W.cube i)]
  -- step 2: per-cube estimate
  have h2 : ∀ i : T, ∫⁻ x in W.cube i, ENNReal.ofReal (g x) ≤
      ENNReal.ofReal (A * gehringH d * t) * volume (W.cube i) +
        ENNReal.ofReal B * ∫⁻ x in W.dilate σ i, ENNReal.ofReal (h x) := by
    intro i
    have := lintegral_cube_le_of_rh hg0 hh0 hg hh hA hB ht (W.center i) (W.side_pos i)
      (σ := σ) (hav i i.2) (hrh i i.2)
    have hd' : W.dilate σ i = centeredAxisCube (W.center i) (σ * (W.side i / 2)) := by
      unfold WhitneyCover.dilate; rw [mul_div_assoc]
    rw [hd']
    exact this
  -- step 3: sums
  have h3 : ∑' i : T, volume (W.cube i) ≤ volume (gehringE g t) := by
    rw [← measure_iUnion hdisj (fun i : T => W.measurableSet_cube i)]
    exact measure_mono (iUnion_subset fun i => W.cube_subset hσ1 i)
  have h4 : ∑' i : T, ∫⁻ x in W.dilate σ i, ENNReal.ofReal (h x) ≤
      ENNReal.ofReal (gehringN σ d) * ∫⁻ x in gehringE g t, ENNReal.ofReal (h x) := by
    have hhm : AEMeasurable (fun x => ENNReal.ofReal (h x)) volume :=
      ENNReal.measurable_ofReal.comp_aemeasurable hh.aestronglyMeasurable.aemeasurable
    have hmeas : ∀ i : T, MeasurableSet (W.dilate σ i) := fun i =>
      (isOpen_centeredAxisCube _ _).measurableSet
    have e1 : ∀ i : T, ∫⁻ x in W.dilate σ i, ENNReal.ofReal (h x) =
        ∫⁻ x, (W.dilate σ i).indicator (fun x => ENNReal.ofReal (h x)) x :=
      fun i => (lintegral_indicator (hmeas i) _).symm
    simp_rw [e1]
    rw [← lintegral_tsum (fun i => hhm.indicator (hmeas i))]
    calc ∫⁻ x, ∑' i : T, (W.dilate σ i).indicator (fun x => ENNReal.ofReal (h x)) x
        ≤ ∫⁻ x, (gehringE g t).indicator
            (fun x => ENNReal.ofReal (gehringN σ d) * ENNReal.ofReal (h x)) x := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ gehringE g t
          · rw [Set.indicator_of_mem hx]
            have : ∀ i : T, (W.dilate σ i).indicator (fun x => ENNReal.ofReal (h x)) x =
                (W.dilate σ i).indicator (fun _ => (1 : ℝ≥0∞)) x * ENNReal.ofReal (h x) := by
              intro i
              by_cases hxi : x ∈ W.dilate σ i <;> simp [hxi]
            simp_rw [this]
            rw [ENNReal.tsum_mul_right]
            show _ ≤ ENNReal.ofReal (3 * (σ + 1) ^ d) * _
            exact mul_le_mul_left (W.tsum_indicator_dilate_le hσ T x) _
          · rw [Set.indicator_of_notMem hx]
            refine le_of_eq (ENNReal.tsum_eq_zero.2 fun i => ?_)
            rw [Set.indicator_of_notMem fun hxi => hx (hdil i hxi)]
      _ = _ := by
          rw [lintegral_indicator hEmeas, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc ∫⁻ x in {x | t < g x} ∩ D, ENNReal.ofReal (g x)
      ≤ ∑' i : T, (ENNReal.ofReal (A * gehringH d * t) * volume (W.cube i) +
        ENNReal.ofReal B * ∫⁻ x in W.dilate σ i, ENNReal.ofReal (h x)) :=
        h1.trans (ENNReal.tsum_le_tsum h2)
    _ = ENNReal.ofReal (A * gehringH d * t) * ∑' i : T, volume (W.cube i) +
        ENNReal.ofReal B * ∑' i : T, ∫⁻ x in W.dilate σ i, ENNReal.ofReal (h x) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
    _ ≤ ENNReal.ofReal (A * gehringH d * t) * volume (gehringE g t) +
        ENNReal.ofReal B * (ENNReal.ofReal (gehringN σ d) *
          ∫⁻ x in gehringE g t, ENNReal.ofReal (h x)) :=
        add_le_add (by gcongr) (by gcongr)
    _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul hB]

/-- The family form of the tail estimate: `F` is a Whitney family for `E_t`. -/
theorem lintegral_gt_le_family (hd : 0 < d) {g h : Vec d → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (hh0 : ∀ x, 0 ≤ h x) (hg : Integrable g volume) (hh : LocallyIntegrable h volume)
    {σ A B t : ℝ} (hσ : σ = 2 ∨ σ = 4) (hA : 0 ≤ A) (hB : 0 ≤ B) (ht : 0 ≤ t)
    (F : WhitneyFamily d g t σ) (T : Set F.ι) (D : Set (Vec d))
    (hrh : ∀ i ∈ T, GehringRH d σ A B g h (F.toWhitneyCover.center i)
      (F.toWhitneyCover.side i / 2))
    (hcov : ∀ᵐ x ∂(volume : Measure (Vec d)),
      x ∈ {x | t < g x} ∩ D → x ∈ ⋃ i ∈ T, F.toWhitneyCover.cube i) :
    ∫⁻ x in {x | t < g x} ∩ D, ENNReal.ofReal (g x) ≤
      ENNReal.ofReal (A * gehringH d * t) * volume (gehringE g t) +
        ENNReal.ofReal (B * gehringN σ d) * ∫⁻ x in gehringE g t, ENNReal.ofReal (h x) :=
  lintegral_gt_le_cover hd hg0 hh0 hg hh hσ hA hB ht F.toWhitneyCover T D
    (fun i _ => F.avg_le i) hrh hcov

end PDE.Gehring
