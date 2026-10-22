module

public import EllipticRegularity.DeGiorgi.Assembly.Scaling
public import PDEFoundation.Regularity.Holder

/-!
# Essential extrema of continuous functions on open sets
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE.DGNMAssembly

open MeasureTheory Filter

variable {d : ℕ}

theorem measure_pos_of_continuousOn_gt {W : Set (Vec d)} (hW : IsOpen W) {g : Vec d → ℝ≥0∞}
    (hg : ContinuousOn g W) {z : Vec d} (hz : z ∈ W) {c : ℝ≥0∞} (hc : c < g z) :
    volumeOn W {x | c < g x} ≠ 0 := by
  have hopen : IsOpen (W ∩ g ⁻¹' Set.Ioi c) := hg.isOpen_inter_preimage hW isOpen_Ioi
  have hpos : 0 < volume (W ∩ g ⁻¹' Set.Ioi c) :=
    hopen.measure_pos volume ⟨z, hz, hc⟩
  have : volumeOn W {x | c < g x} = volume (W ∩ g ⁻¹' Set.Ioi c) := by
    rw [volumeOn, Measure.restrict_apply' hW.measurableSet, Set.inter_comm]
    rfl
  rw [this]
  exact hpos.ne'

theorem measure_pos_of_continuousOn_lt {W : Set (Vec d)} (hW : IsOpen W) {g : Vec d → ℝ≥0∞}
    (hg : ContinuousOn g W) {z : Vec d} (hz : z ∈ W) {c : ℝ≥0∞} (hc : g z < c) :
    volumeOn W {x | g x < c} ≠ 0 := by
  have hopen : IsOpen (W ∩ g ⁻¹' Set.Iio c) := hg.isOpen_inter_preimage hW isOpen_Iio
  have hpos : 0 < volume (W ∩ g ⁻¹' Set.Iio c) :=
    hopen.measure_pos volume ⟨z, hz, hc⟩
  have : volumeOn W {x | g x < c} = volume (W ∩ g ⁻¹' Set.Iio c) := by
    rw [volumeOn, Measure.restrict_apply' hW.measurableSet, Set.inter_comm]
    rfl
  rw [this]
  exact hpos.ne'

/-- A continuous function on an open set is bounded above by its essential supremum there. -/
theorem le_essSup_of_continuousOn {W : Set (Vec d)} (hW : IsOpen W) {g : Vec d → ℝ≥0∞}
    (hg : ContinuousOn g W) {z : Vec d} (hz : z ∈ W) :
    g z ≤ essSup g (volumeOn W) := by
  by_contra h
  rw [not_le] at h
  exact measure_pos_of_continuousOn_gt hW hg hz h (meas_essSup_lt)

/-- A continuous function on an open set is bounded below by its essential infimum there. -/
theorem essInf_le_of_continuousOn {W : Set (Vec d)} (hW : IsOpen W) {g : Vec d → ℝ≥0∞}
    (hg : ContinuousOn g W) {z : Vec d} (hz : z ∈ W) :
    essInf g (volumeOn W) ≤ g z := by
  by_contra h
  rw [not_le] at h
  exact measure_pos_of_continuousOn_lt hW hg hz h (meas_lt_essInf)

/-- A continuous function that is almost everywhere positive on an open set is nonnegative
there. -/
theorem nonneg_of_continuousOn_ae_pos {W : Set (Vec d)} (hW : IsOpen W) {f : Vec d → ℝ}
    (hf : ContinuousOn f W) (hpos : ∀ᵐ x ∂(volumeOn W), 0 < f x) {z : Vec d} (hz : z ∈ W) :
    0 ≤ f z := by
  by_contra h
  rw [not_le] at h
  have hopen : IsOpen (W ∩ f ⁻¹' Set.Iio 0) := hf.isOpen_inter_preimage hW isOpen_Iio
  have hpos' : 0 < volume (W ∩ f ⁻¹' Set.Iio 0) := hopen.measure_pos volume ⟨z, hz, h⟩
  have hnull : volumeOn W {x | ¬ 0 < f x} = 0 := ae_iff.mp hpos
  rw [volumeOn, Measure.restrict_apply' hW.measurableSet] at hnull
  refine hpos'.ne' (measure_mono_null ?_ hnull)
  intro x hx
  exact ⟨fun h0 => absurd hx.2 (not_lt.2 h0.le), hx.1⟩

/-- A continuous representative on an open set `W ⊆ U` is bounded above by the essential
supremum of the function it represents over `U`. -/
theorem ofReal_le_essSup_of_cont {W U : Set (Vec d)} (hW : IsOpen W) (hWU : W ⊆ U)
    {v : Vec d → ℝ} (hv : ContinuousOn v W) {g : Vec d → ℝ≥0∞}
    (hvg : (fun x => ENNReal.ofReal (v x)) =ᵐ[volumeOn W] g) {y : Vec d} (hy : y ∈ W) :
    ENNReal.ofReal (v y) ≤ essSup g (volumeOn U) := by
  calc ENNReal.ofReal (v y) ≤ essSup (fun x => ENNReal.ofReal (v x)) (volumeOn W) :=
        le_essSup_of_continuousOn hW (ENNReal.continuous_ofReal.comp_continuousOn hv) hy
    _ = essSup g (volumeOn W) := essSup_congr_ae hvg
    _ ≤ essSup g (volumeOn U) := essSup_mono_measure' (Measure.restrict_mono hWU le_rfl)

/-- A continuous representative on an open set `W ⊆ U` is bounded below by the essential
infimum of the function it represents over `U`. -/
theorem essInf_le_ofReal_of_cont {W U : Set (Vec d)} (hW : IsOpen W) (hWU : W ⊆ U)
    {v : Vec d → ℝ} (hv : ContinuousOn v W) {g : Vec d → ℝ≥0∞}
    (hvg : (fun x => ENNReal.ofReal (v x)) =ᵐ[volumeOn W] g) {z : Vec d} (hz : z ∈ W) :
    essInf g (volumeOn U) ≤ ENNReal.ofReal (v z) := by
  calc essInf g (volumeOn U) ≤ essInf g (volumeOn W) :=
        essInf_antitone_measure (Measure.absolutelyContinuous_of_le
          (Measure.restrict_mono hWU le_rfl))
    _ = essInf (fun x => ENNReal.ofReal (v x)) (volumeOn W) := (essInf_congr_ae hvg).symm
    _ ≤ ENNReal.ofReal (v z) :=
        essInf_le_of_continuousOn hW (ENNReal.continuous_ofReal.comp_continuousOn hv) hz

/-- A Euclidean Hölder function with positive exponent is continuous. -/
theorem continuousOn_of_euclideanHolder {U : Set (Vec d)} {v : Vec d → ℝ} {α K : ℝ}
    (hα : 0 < α) (h : EuclideanHolderSeminormLE U v α K) : ContinuousOn v U := by
  intro x hx
  rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
  have hb : Tendsto (fun y : Vec d => K * vecEuclideanNorm (y - x) ^ α) (𝓝 x) (𝓝 0) := by
    have hc : Continuous (fun y : Vec d => K * vecEuclideanNorm (y - x) ^ α) :=
      continuous_const.mul ((Real.continuous_rpow_const hα.le).comp
        (continuous_vecEuclideanNorm.comp (continuous_id.sub continuous_const)))
    have := hc.tendsto x
    have h0 : vecEuclideanNorm (0 : Vec d) = 0 := vecEuclideanNorm_eq_zero_iff.2 rfl
    simpa [h0, Real.zero_rpow hα.ne'] using this
  refine squeeze_zero' (Eventually.of_forall fun y => dist_nonneg) ?_ (hb.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [Real.dist_eq]
  exact h y hy x hx

end PDE.DGNMAssembly
