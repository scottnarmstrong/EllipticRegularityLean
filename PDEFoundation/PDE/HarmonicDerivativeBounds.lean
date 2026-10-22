module

public import PDEFoundation.PDE.HarmonicFirstDerivCore
public import PDEFoundation.PDE.HarmonicReproductionConvolution
public import PDEFoundation.PDE.HarmonicIterateCore
public import PDEFoundation.Geometry.EuclideanBall.Topology

/-! # Harmonic first and iterated derivative bounds -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology Convolution

noncomputable section

namespace PDE

private theorem locallyIntegrable_indicator_euclideanBall_of_contDiffOn
    {d : ℕ} {w : Vec d → ℝ} {y : Vec d} {r t : ℝ}
    (hr : 0 < r) (hrt : r < t)
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) w (euclideanBall y t)) :
    LocallyIntegrable (Set.indicator (euclideanBall y r) w) volume := by
  let B := euclideanBall y r
  let Cb := euclideanClosedBall y r
  have hclosedSub : Cb ⊆ euclideanBall y t :=
    euclideanClosedBall_subset_euclideanBall hr.le hrt
  obtain ⟨C, hC⟩ :=
    (isCompact_euclideanClosedBall y hr.le).exists_bound_of_continuousOn
      ((hw.mono hclosedSub).continuousOn)
  have hCabs : ∀ z ∈ Cb, |w z| ≤ C := by
    intro z hz
    simpa only [Real.norm_eq_abs] using hC z hz
  have hcontClosed : ContinuousOn w Cb := (hw.mono hclosedSub).continuousOn
  have hclosedMeas : MeasurableSet Cb :=
    (isClosed_euclideanClosedBall y r).measurableSet
  have hliOnClosed : LocallyIntegrableOn w Cb volume :=
    hcontClosed.locallyIntegrableOn hclosedMeas
  have hliClosed : LocallyIntegrable w (volume.restrict Cb) :=
    (locallyIntegrableOn_iff_locallyIntegrable_restrict
      (isClosed_euclideanClosedBall y r)).mp hliOnClosed
  have hballClosed : B ⊆ Cb := euclideanBall_subset_euclideanClosedBall y r
  have hmeasOn : AEStronglyMeasurable w (volume.restrict B) :=
    hliClosed.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono_set volume hballClosed)
  have hmeas : AEStronglyMeasurable (Set.indicator B w) volume :=
    (aestronglyMeasurable_indicator_iff (isOpen_euclideanBall y r).measurableSet).2 hmeasOn
  have hcompactSupport : HasCompactSupport (Set.indicator B w) := by
    apply (isCompact_euclideanClosedBall y hr.le).of_isClosed_subset (isClosed_tsupport _)
    change closure (Function.support (Set.indicator B w)) ⊆ Cb
    apply closure_minimal
    · intro z hz
      exact (euclideanBall_subset_euclideanClosedBall y r)
        (Set.support_indicator_subset hz)
    · exact isClosed_euclideanClosedBall y r
  have hbound : ∀ z, ‖Set.indicator B w z‖ ≤ max C 0 := by
    intro z
    by_cases hz : z ∈ B
    · rw [Set.indicator_of_mem hz]
      simpa only [Real.norm_eq_abs] using (hCabs z
        ((euclideanBall_subset_euclideanClosedBall y r) hz)).trans (le_max_left C 0)
    · simp [Set.indicator, hz]
  have hmemLp : MemLp (Set.indicator B w) 2 volume :=
    hcompactSupport.memLp_of_bound hmeas (max C 0)
      (Filter.Eventually.of_forall hbound)
  exact hmemLp.locallyIntegrable (by norm_num)

/-- A smooth harmonic function has the dimension-explicit first derivative
bound on an interior ball. The zero extension is taken on a slightly smaller
ball to ensure its local integrability. -/
theorem abs_euclideanCoordDeriv_le_of_harmonicOn
    {d : ℕ} (hd : 0 < d) {w : Vec d → ℝ} {y : Vec d} {t s M : ℝ}
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) w (euclideanBall y t))
    (hharm : ∀ z ∈ euclideanBall y t, euclideanCoordLaplacian w z = 0)
    (hs : 0 < s) (hst : s < t)
    (hbound : ∀ z ∈ euclideanBall y s, |w z| ≤ M) (i : Fin d) :
    |euclideanCoordDeriv i w y| ≤ harmonicKernelDerivConst d / s * M := by
  obtain ⟨r, hsr, hrt⟩ := exists_between hst
  have hr : 0 < r := hs.trans hsr
  have hballSub : euclideanBall y r ⊆ euclideanBall y t :=
    euclideanBall_mono hr.le hrt.le
  have hw' : ContDiffOn ℝ (⊤ : ℕ∞) w (euclideanBall y r) := hw.mono hballSub
  have hharm' : ∀ z ∈ euclideanBall y r, euclideanCoordLaplacian w z = 0 :=
    fun z hz => hharm z (hballSub hz)
  let g : Vec d → ℝ := Set.indicator (euclideanBall y r) w
  have hg : LocallyIntegrable g volume := by
    dsimp [g]
    exact locallyIntegrable_indicator_euclideanBall_of_contDiffOn hr hrt hw
  have hsmall : ∀ z ∈ euclideanBall y s, |g z| ≤ M := by
    intro z hz
    have hz' : z ∈ euclideanBall y r := (euclideanBall_mono hs.le hsr.le) hz
    rw [show g z = w z by simp [g, Set.indicator_of_mem hz']]
    exact hbound z hz
  have hmargin : 0 < r - s := by linarith
  have heq : w =ᶠ[𝓝 y]
      (harmonicKernelScaled s ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) := by
    filter_upwards [((isOpen_euclideanBall y (r - s)).mem_nhds
      (center_mem_euclideanBall y hmargin))] with z hz
    exact (harmonicKernelScaled_convolution_indicator_eq_of_harmonicOn
      hd hw' hharm' hs hsr hz).symm
  exact abs_euclideanCoordDeriv_le_of_eventuallyEq_convolution
    hs hg heq M hsmall i

/-- Higher coordinate derivatives obey the iterated first-derivative bound
on an interior closed ball. -/
theorem abs_iteratedCoordDeriv_le_of_harmonicOn
    {d : ℕ} (hd : 0 < d) {v : Vec d → ℝ} {x : Vec d} {R ρ M : ℝ}
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v (euclideanBall x R))
    (hharm : ∀ z ∈ euclideanBall x R, euclideanCoordLaplacian v z = 0)
    (hρ : 0 < ρ) (hρR : ρ < R)
    (hM : ∀ z ∈ euclideanClosedBall x ρ, |v z| ≤ M)
    (m : ℕ) (hm : 1 ≤ m) (ι : Fin m → Fin d) :
    |iteratedCoordDeriv m ι v x| ≤
      (harmonicKernelDerivConst d * m / ρ) ^ m * M := by
  exact abs_iteratedCoordDeriv_le_of_firstDerivEstimate
    (K := harmonicKernelDerivConst d) harmonicKernelDerivConst_nonneg
    (fun w y t s M i hw hharm hs hst hbound =>
      abs_euclideanCoordDeriv_le_of_harmonicOn hd hw hharm hs hst hbound i)
    hv hharm hρ hρR hM m hm ι

end PDE

end
