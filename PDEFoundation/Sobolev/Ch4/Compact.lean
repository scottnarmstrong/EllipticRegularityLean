module

public import PDEFoundation.Sobolev.Ch4.ZeroExtension
public import PDEFoundation.Sobolev.Inequalities.SobolevWholeSpaceMollify
public import PDEFoundation.Sobolev.Inequalities.SobolevWholeSpaceCutoff
public import PDEFoundation.Sobolev.H1.ZeroBoundary

/-!
# Compactly supported `H¹` functions have zero boundary values

An `H¹(U)` function vanishing outside a compact set `K ⊆ U` is in `H¹₀(U)`.  The approximants
are whole-space mollifications of its zero extension at scales below the distance from `K` to
`Uᶜ`; the coordinate derivative of a mollification is the mollification of the weak gradient
(`euclideanCoordDeriv_convolution_eq_of_hasWeakPartialDerivOn`), and mollifications converge in
`L²` (`tendsto_eLpNorm_wholeSpaceMollify_sub`).
-/

@[expose] public section

open scoped ENNReal Convolution Topology
open MeasureTheory Set Filter

namespace PDE.Ch4Infra

variable {d : ℕ} {U : Set (Vec d)}

/-- The mollification at scale `a` of `h` is supported in the closed `a`-thickening of the
support of `h`. -/
theorem support_wholeSpaceMollify_subset_cthickening {h : Vec d → ℝ} {a : ℝ} (ha : 0 < a) :
    Function.support (wholeSpaceMollify a h) ⊆ Metric.cthickening a (tsupport h) := by
  intro x hx
  by_contra hxn
  apply hx
  simp only [wholeSpaceMollify, convolution_def]
  have : ∀ t, (ContinuousLinearMap.lsmul ℝ ℝ)
      (scaledConvexApproxKernel (unitConvexApproxKernel (d := d)) a t) (h (x - t)) = 0 := by
    intro t
    by_cases ht : a < ‖t‖
    · simp [scaledUnitKernel_eq_zero_of_lt_norm ha ht]
    · have hmem : x - t ∉ tsupport h := fun hm =>
        hxn (Metric.mem_cthickening_of_dist_le x (x - t) a _ hm (by
          rw [dist_eq_norm, sub_sub_cancel]; exact not_lt.mp ht))
      simp [image_eq_zero_of_notMem_tsupport hmem]
  simp [this]

/-- **Compactly supported `H¹` functions are `H¹₀`**: a supported smooth approximation of a
function of `H¹(U)` vanishing outside a compact `K ⊆ U`. -/
theorem nonempty_supportedSmoothApproximation_of_compact (hU : IsOpen U) (f : H1Function U)
    {K : Set (Vec d)} (hKU : K ⊆ U) (hK : IsCompact K)
    (hf0 : ∀ x ∈ U, x ∉ K → f.toFun x = 0) : Nonempty f.SupportedSmoothApproximation := by
  classical
  have hρ := isConvexApproxKernel_unitConvexApproxKernel (d := d)
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  let δ' : ℝ := min δ 1
  have hδ' : 0 < δ' := lt_min hδ one_pos
  let a : ℕ → ℝ := fun n => δ' * unitConvexApproxScale n
  have ha : ∀ n, 0 < a n := fun n => mul_pos hδ' (unitConvexApproxScale_pos n)
  have ha1 : ∀ n, a n ≤ 1 := fun n =>
    calc a n ≤ 1 * 1 := mul_le_mul (min_le_right _ _) (unitConvexApproxScale_le_one n)
            (unitConvexApproxScale_pos n).le zero_le_one
      _ = 1 := one_mul 1
  have haδ : ∀ n, a n ≤ δ := fun n =>
    calc a n ≤ δ' * 1 := mul_le_mul_of_nonneg_left (unitConvexApproxScale_le_one n) hδ'.le
      _ ≤ δ := by rw [mul_one]; exact min_le_left _ _
  have ha0 : Tendsto a atTop (𝓝 0) := by
    simpa [a] using tendsto_unitConvexApproxScale_zero.const_mul δ'
  set F : Vec d → ℝ := U.indicator f.toFun with hF
  set G : Fin d → Vec d → ℝ := fun i => U.indicator (fun x => f.grad x i) with hG
  have hFmem : MemLp F 2 volume := (memLp_indicator_iff_restrict hU.measurableSet).2 f.memL2
  have hGmem : ∀ i, MemLp (G i) 2 volume := fun i =>
    (memLp_indicator_iff_restrict hU.measurableSet).2 (f.gradMemL2 i)
  have hweak := hasWeakPartialDerivOn_univ_zeroExtend hU f hKU hK hf0
  have hFK : tsupport F ⊆ K := by
    refine closure_minimal (fun x hx => ?_) hK.isClosed
    by_contra hxK
    apply hx
    by_cases hxU : x ∈ U
    · simp [hF, Set.indicator_of_mem hxU, hf0 x hxU hxK]
    · simp [hF, Set.indicator_of_notMem hxU]
  let M : ℕ → Vec d → ℝ := fun n => wholeSpaceMollify (a n) F
  have hMs : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (M n) := fun n =>
    (contDiff_memLp_convolution_scaledConvexApproxKernel hρ (ha n) (by norm_num) (by norm_num)
      hFmem).1
  have hMderiv : ∀ n i, euclideanCoordDeriv i (M n) = wholeSpaceMollify (a n) (G i) := fun n i =>
    euclideanCoordDeriv_convolution_eq_of_hasWeakPartialDerivOn
      (hasCompactSupport_scaledConvexApproxKernel hρ.compactSupport (ha n))
      (contDiff_scaledConvexApproxKernel hρ _) (hFmem.locallyIntegrable (by norm_num)) (hweak i)
  have hMts : ∀ n, tsupport (M n) ⊆ Metric.cthickening (a n) K := fun n =>
    closure_minimal
      ((support_wholeSpaceMollify_subset_cthickening (ha n)).trans
        (Metric.cthickening_subset_of_subset (a n) hFK))
      Metric.isClosed_cthickening
  have hMc : ∀ n, HasCompactSupport (M n) := fun n =>
    HasCompactSupport.of_support_subset_isCompact (hK.cthickening (r := a n))
      ((support_wholeSpaceMollify_subset_cthickening (ha n)).trans
        (Metric.cthickening_subset_of_subset (a n) hFK))
  refine ⟨
    { approx := M
      approx_smooth := hMs
      approx_hasCompactSupport := hMc
      approx_tsupport_subset := fun n =>
        (hMts n).trans ((Metric.cthickening_mono (haδ n) K).trans hδU)
      tendsto_value := ?_
      tendsto_grad := ?_ }⟩
  · have h := tendsto_eLpNorm_wholeSpaceMollify_sub (p := 2) (by norm_num) (by norm_num) hFmem ha ha1 ha0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun n => bot_le)
      (fun n => ?_)
    change eLpNorm (M n - f.toFun) 2 (volumeOn U) ≤ _
    have e : eLpNorm (M n - f.toFun) 2 (volumeOn U) = eLpNorm (M n - F) 2 (volumeOn U) := by
      apply eLpNorm_congr_ae
      filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
      simp [hF, Set.indicator_of_mem hx]
    rw [e]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  · intro i
    have h := tendsto_eLpNorm_wholeSpaceMollify_sub (p := 2) (by norm_num) (by norm_num)
      (hGmem i) ha ha1 ha0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun n => bot_le)
      (fun n => ?_)
    change eLpNorm (fun x => (fderiv ℝ (M n) x) (basisVec i) - f.grad x i) 2 (volumeOn U) ≤ _
    have e : eLpNorm (fun x => (fderiv ℝ (M n) x) (basisVec i) - f.grad x i) 2 (volumeOn U) =
        eLpNorm (wholeSpaceMollify (a n) (G i) - G i) 2 (volumeOn U) := by
      apply eLpNorm_congr_ae
      filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
      have := congrFun (hMderiv n i) x
      simp only [euclideanCoordDeriv] at this
      simp [this, hG, Set.indicator_of_mem hx]
    rw [e]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self

/-- An `H¹(U)` function vanishing outside a compact subset of `U` is an `H¹₀(U)` function
with the same value and gradient representatives. -/
noncomputable def toH10OfCompact (hU : IsOpen U) (f : H1Function U)
    {K : Set (Vec d)} (hKU : K ⊆ U) (hK : IsCompact K)
    (hf0 : ∀ x ∈ U, x ∉ K → f.toFun x = 0) : H10Function U :=
  f.toH10Function (nonempty_supportedSmoothApproximation_of_compact hU f hKU hK hf0).some

end PDE.Ch4Infra
