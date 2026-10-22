module

public import PDEFoundation.Analysis.Newtonian.WeakType.DecompositionGoodBad

/-! # Integral bounds for the Calderón–Zygmund decomposition

`‖g‖₁ ≤ ‖F‖₁`, `‖g‖₂² ≤ 2^d λ ‖F‖₁`, and `‖b_k‖₁ ≤ 2 ‖F‖_{L¹(Q_k)}`, all in `lintegral` form,
over the root box `I`.
-/

@[expose] public section

open BoxIntegral MeasureTheory Set Filter
open scoped ENNReal Topology Function

namespace PDE.NewtonWeakType

noncomputable section

variable {d : ℕ} {I : Box (Fin d)} {F : Vec d → Vec d} {lam : ℝ} {S : CZStopping I F lam}

private theorem ofReal_norm_mul_volume_le (hF : ∀ i, IntegrableOn (fun x => F x i) (I : Set (Vec d)))
    (k : S.ι) :
    ENNReal.ofReal (vecEuclideanNorm (czAvg S k)) * volume (S.cube k : Set (Vec d)) ≤
      ∫⁻ x in (S.cube k : Set (Vec d)), ENNReal.ofReal (vecEuclideanNorm (F x)) := by
  set Q : Set (Vec d) := (S.cube k : Set (Vec d)) with hQ
  set a : ℝ := integralAverage Q (fun x => vecEuclideanNorm (F x)) with ha
  have hpos := czCube_volume_toReal_pos S k
  have hQtop := czCube_volume_lt_top S k
  have ha0 : 0 ≤ a := integralAverage_nonneg (S.cube k).measurableSet_coe
    (fun x _ => vecEuclideanNorm_nonneg _)
  have hint : IntegrableOn (fun x => vecEuclideanNorm (F x)) Q :=
    integrable_vecEuclideanNorm_of_coord (μ := volume.restrict Q) F
      (fun i => (hF i).mono_set (czCube_subset_root S k))
  have heq : ∫⁻ x in Q, ENNReal.ofReal (vecEuclideanNorm (F x)) =
      ENNReal.ofReal a * volume Q := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun x => vecEuclideanNorm_nonneg _),
      setIntegral_eq_integralAverage_mul Q _ hpos, ENNReal.ofReal_mul ha0,
      ENNReal.ofReal_toReal hQtop.ne]
  rw [heq]
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (vecEuclideanNorm_czAvg_le hF k)) _

/-- On a stopping cube the good part has the cube's average of `F`. -/
private theorem lintegral_czGood_cube (k : S.ι) :
    ∫⁻ x in (S.cube k : Set (Vec d)), ENNReal.ofReal (vecEuclideanNorm (czGood S x)) =
      ENNReal.ofReal (vecEuclideanNorm (czAvg S k)) * volume (S.cube k : Set (Vec d)) := by
  rw [setLIntegral_congr_fun (S.cube k).measurableSet_coe
    (fun x hx => by rw [czGood_of_mem S hx]), setLIntegral_const]

/-- **`‖g‖₁ ≤ ‖F‖₁`** over the root box. -/
theorem lintegral_vecEuclideanNorm_czGood_le
    (hF : ∀ i, IntegrableOn (fun x => F x i) (I : Set (Vec d))) :
    ∫⁻ x in (I : Set (Vec d)), ENNReal.ofReal (vecEuclideanNorm (czGood S x)) ≤
      ∫⁻ x in (I : Set (Vec d)), ENNReal.ofReal (vecEuclideanNorm (F x)) := by
  set U : Set (Vec d) := ⋃ k, (S.cube k : Set (Vec d)) with hU
  have hUm : MeasurableSet U := MeasurableSet.iUnion fun k => (S.cube k).measurableSet_coe
  have hUI : U ⊆ (I : Set (Vec d)) := iUnion_subset fun k => czCube_subset_root S k
  have hmeas : ∀ k, MeasurableSet (S.cube k : Set (Vec d)) := fun k => (S.cube k).measurableSet_coe
  have hsplit : ∀ f : Vec d → ℝ≥0∞, ∫⁻ x in (I : Set (Vec d)), f x =
      (∫⁻ x in U, f x) + ∫⁻ x in (I : Set (Vec d)) \ U, f x := by
    intro f
    rw [← lintegral_inter_add_sdiff f (I : Set (Vec d)) hUm, inter_eq_right.mpr hUI]
  rw [hsplit, hsplit (fun x => ENNReal.ofReal (vecEuclideanNorm (F x)))]
  have hdiff : ∫⁻ x in (I : Set (Vec d)) \ U, ENNReal.ofReal (vecEuclideanNorm (czGood S x)) =
      ∫⁻ x in (I : Set (Vec d)) \ U, ENNReal.ofReal (vecEuclideanNorm (F x)) := by
    apply setLIntegral_congr_fun (I.measurableSet_coe.diff hUm)
    intro x hx
    dsimp only
    rw [czGood_of_notMem S (fun k hk => hx.2 (mem_iUnion.mpr ⟨k, hk⟩))]
  rw [hdiff]
  refine add_le_add_left ?_ _
  rw [hU, lintegral_iUnion hmeas S.pairwise_disjoint, lintegral_iUnion hmeas S.pairwise_disjoint]
  refine ENNReal.tsum_le_tsum fun k => ?_
  rw [lintegral_czGood_cube]
  exact ofReal_norm_mul_volume_le hF k

/-- **`‖g‖₂² ≤ 2^d λ ‖F‖₁`** over the root box. -/
theorem lintegral_vecNormSq_czGood_le
    (hF : ∀ i, IntegrableOn (fun x => F x i) (I : Set (Vec d))) :
    ∫⁻ x in (I : Set (Vec d)), ENNReal.ofReal (vecNormSq (czGood S x)) ≤
      ENNReal.ofReal (2 ^ d * lam) *
        ∫⁻ x in (I : Set (Vec d)), ENNReal.ofReal (vecEuclideanNorm (F x)) := by
  have hae : ∀ᵐ x ∂(volume.restrict (I : Set (Vec d))),
      ENNReal.ofReal (vecNormSq (czGood S x)) ≤
        ENNReal.ofReal (2 ^ d * lam) * ENNReal.ofReal (vecEuclideanNorm (czGood S x)) := by
    rw [ae_restrict_iff' I.measurableSet_coe]
    filter_upwards [ae_vecEuclideanNorm_czGood_le (S := S) hF] with x hx hxI
    rw [← ENNReal.ofReal_mul (by have := S.lam_pos; positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [← vecEuclideanNorm_sq, sq]
    have := hx hxI
    nlinarith [vecEuclideanNorm_nonneg (czGood S x)]
  calc
    _ ≤ ∫⁻ x in (I : Set (Vec d)), ENNReal.ofReal (2 ^ d * lam) *
        ENNReal.ofReal (vecEuclideanNorm (czGood S x)) := lintegral_mono_ae hae
    _ = ENNReal.ofReal (2 ^ d * lam) *
        ∫⁻ x in (I : Set (Vec d)), ENNReal.ofReal (vecEuclideanNorm (czGood S x)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul_right (lintegral_vecEuclideanNorm_czGood_le hF) _

/-- **`‖b_k‖₁ ≤ 2 ‖F‖_{L¹(Q_k)}`.** -/
theorem lintegral_vecEuclideanNorm_czBad_le
    (hF : ∀ i, IntegrableOn (fun x => F x i) (I : Set (Vec d))) (k : S.ι) :
    ∫⁻ x, ENNReal.ofReal (vecEuclideanNorm (czBad S k x)) ≤
      2 * ∫⁻ x in (S.cube k : Set (Vec d)), ENNReal.ofReal (vecEuclideanNorm (F x)) := by
  set Q : Set (Vec d) := (S.cube k : Set (Vec d)) with hQ
  have hQm : MeasurableSet Q := (S.cube k).measurableSet_coe
  have h1 : (fun x => ENNReal.ofReal (vecEuclideanNorm (czBad S k x))) =
      Q.indicator (fun x => ENNReal.ofReal (vecEuclideanNorm (F x - czAvg S k))) := by
    funext x
    by_cases hx : x ∈ Q
    · rw [czBad_of_mem S hx, Set.indicator_of_mem hx]
    · rw [czBad_of_notMem S hx, Set.indicator_of_notMem hx,
        vecEuclideanNorm_eq_zero_iff.mpr rfl, ENNReal.ofReal_zero]
  rw [h1, lintegral_indicator hQm]
  have h2 : ∀ x, ENNReal.ofReal (vecEuclideanNorm (F x - czAvg S k)) ≤
      ENNReal.ofReal (vecEuclideanNorm (F x)) + ENNReal.ofReal (vecEuclideanNorm (czAvg S k)) := by
    intro x
    rw [← ENNReal.ofReal_add (vecEuclideanNorm_nonneg _) (vecEuclideanNorm_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have := vecEuclideanNorm_add_le (F x) (-czAvg S k)
    rwa [← sub_eq_add_neg, vecEuclideanNorm_neg] at this
  calc
    _ ≤ ∫⁻ x in Q, (ENNReal.ofReal (vecEuclideanNorm (F x)) +
        ENNReal.ofReal (vecEuclideanNorm (czAvg S k))) := lintegral_mono h2
    _ = (∫⁻ x in Q, ENNReal.ofReal (vecEuclideanNorm (F x))) +
        ENNReal.ofReal (vecEuclideanNorm (czAvg S k)) * volume Q := by
      rw [lintegral_add_right _ measurable_const, setLIntegral_const]
    _ ≤ _ := by
      rw [two_mul]
      exact add_le_add_right (ofReal_norm_mul_volume_le hF k) _

/-- The bad parts together have `L¹` mass at most `2 ‖F‖₁`. -/
theorem tsum_lintegral_vecEuclideanNorm_czBad_le
    (hF : ∀ i, IntegrableOn (fun x => F x i) (I : Set (Vec d))) :
    ∑' k, ∫⁻ x, ENNReal.ofReal (vecEuclideanNorm (czBad S k x)) ≤
      2 * ∫⁻ x in (I : Set (Vec d)), ENNReal.ofReal (vecEuclideanNorm (F x)) := by
  have hmeas : ∀ k, MeasurableSet (S.cube k : Set (Vec d)) := fun k => (S.cube k).measurableSet_coe
  calc
    _ ≤ ∑' k, 2 * ∫⁻ x in (S.cube k : Set (Vec d)), ENNReal.ofReal (vecEuclideanNorm (F x)) :=
      ENNReal.tsum_le_tsum fun k => lintegral_vecEuclideanNorm_czBad_le hF k
    _ = 2 * ∫⁻ x in ⋃ k, (S.cube k : Set (Vec d)), ENNReal.ofReal (vecEuclideanNorm (F x)) := by
      rw [ENNReal.tsum_mul_left, lintegral_iUnion hmeas S.pairwise_disjoint]
    _ ≤ _ := mul_le_mul_right
      (lintegral_mono_set (iUnion_subset fun k => czCube_subset_root S k)) _

/-- Each coordinate of the good part is a.e. measurable on the root box. -/
theorem aemeasurable_czGood_coord
    (hF : ∀ i, IntegrableOn (fun x => F x i) (I : Set (Vec d))) (i : Fin d) :
    AEMeasurable (fun x => czGood S x i) (volume.restrict (I : Set (Vec d))) := by
  have hsum : AEMeasurable (fun x => ∑' k, czBad S k x i) (volume.restrict (I : Set (Vec d))) :=
    AEMeasurable.tsum fun k => (integrable_czBad_coord hF (S := S) k i).aemeasurable.restrict
  refine ((hF i).aemeasurable.sub hsum).congr (Eventually.of_forall fun x => ?_)
  have h := (Pi.hasSum.mp (hasSum_czBad S x) i).tsum_eq
  simp only [Pi.sub_apply] at h
  show F x i - ∑' k, czBad S k x i = czGood S x i
  rw [h]
  ring

end

end PDE.NewtonWeakType
