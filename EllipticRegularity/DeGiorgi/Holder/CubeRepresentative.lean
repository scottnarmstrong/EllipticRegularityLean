module

public import PDEFoundation.Regularity.EssentialOscillationHolder

/-!
# Hölder estimate for the dyadic cube representative

A copy (with the representative exposed in the statement) of the proof of
`CenteredCubeEssentialOscillationDecayOn.hasEuclideanHolderRepresentativeOn_closed_inner`
from `PDEFoundation.Regularity.EssentialOscillationHolder`.  The fixed function
`dyadicCenteredCubeRepresentative u (R / 8)` is Hölder on every closed cube
`closedCenteredAxisCube x₀ (R / 8)` for which the oscillation decay holds on the
cube of half-side `R` around `x₀`; exposing it allows gluing over several `x₀`.
-/

@[expose] public section

namespace PDE.DGNMHolder

open PDE Filter MeasureTheory Topology

noncomputable section

variable {d : ℕ}

theorem centeredCubeAverage_mem_Icc
    {u : Vec d → ℝ} {x : Vec d} {r a b : ℝ}
    (hr : 0 < r) (hu : IntegrableOn u (centeredAxisCube x r))
    (hRange : EssentialRangeBoundsOn u (centeredAxisCube x r) a b) :
    centeredCubeAverage u x r ∈ Set.Icc a b := by
  have havg : centeredCubeAverage u x r =
      ⨍ z in centeredAxisCube x r, u z ∂volume := by
    rw [centeredCubeAverage, setAverage_eq]
    rfl
  rw [havg]
  exact
    (convex_Icc a b).set_average_mem isClosed_Icc
      (volume_centeredAxisCube_pos x hr).ne'
      (volume_centeredAxisCube_ne_top x r) hRange hu

private theorem centeredAxisCube_subset_of_norm_add_lt
    {x y : Vec d} {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R) (hxy : ‖y - x‖ + r < R) :
    centeredAxisCube y r ⊆ centeredAxisCube x R := by
  rw [centeredAxisCube_eq_metric_ball y hr,
    centeredAxisCube_eq_metric_ball x hR]
  apply Metric.ball_subset_ball'
  simpa only [dist_eq_norm, add_comm] using hxy.le

private theorem dyadicRadius_pos {R : ℝ} (hR : 0 < R) (n : ℕ) :
    0 < R / (2 : ℝ) ^ n :=
  div_pos hR (by positivity)

private theorem dyadicRadius_antitone {R : ℝ} (hR : 0 < R)
    {m n : ℕ} (hmn : m ≤ n) :
    R / (2 : ℝ) ^ n ≤ R / (2 : ℝ) ^ m := by
  apply div_le_div_of_nonneg_left hR.le (by positivity)
  exact pow_le_pow_right₀ (by norm_num) hmn

private theorem tendsto_dyadicRadius (R : ℝ) :
    Tendsto (fun n : ℕ => R / (2 : ℝ) ^ n) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))

private theorem norm_sub_le_of_mem_closedCenteredAxisCube
    {x x₀ : Vec d} {R : ℝ} (hR : 0 ≤ R)
    (hx : x ∈ closedCenteredAxisCube x₀ R) :
    ‖x - x₀‖ ≤ R := by
  rw [closedCenteredAxisCube_eq_metric_closedBall x₀ hR] at hx
  simpa only [Metric.mem_closedBall, dist_eq_norm] using hx

private theorem dyadicCenteredCubeMeanSeq_mem_Icc
    {u : Vec d → ℝ} {x : Vec d} {R a b : ℝ} {m N : ℕ}
    (hR : 0 < R) (hNm : N ≤ m)
    (hu : LocallyIntegrable u volume)
    (hRange : EssentialRangeBoundsOn u
      (centeredAxisCube x (R / (2 : ℝ) ^ N)) a b) :
    dyadicCenteredCubeMeanSeq u R x m ∈ Set.Icc a b := by
  have hRm : 0 < R / (2 : ℝ) ^ m := dyadicRadius_pos hR m
  have hsub : centeredAxisCube x (R / (2 : ℝ) ^ m) ⊆
      centeredAxisCube x (R / (2 : ℝ) ^ N) :=
    centeredAxisCube_mono x (dyadicRadius_antitone hR hNm)
  apply centeredCubeAverage_mem_Icc hRm
    (locallyIntegrable_integrableOn_centeredAxisCube hu x hRm)
  exact hRange.mono hsub

private theorem cauchySeq_dyadicCenteredCubeMeanSeq_of_essentialOscillation
    {u : Vec d → ℝ} {x x₀ : Vec d} {R α K : ℝ}
    (hR : 0 < R) (hα : 0 < α)
    (hu : LocallyIntegrable u volume)
    (hx : x ∈ closedCenteredAxisCube x₀ (R / 8))
    (hdecay : CenteredCubeEssentialOscillationDecayOn u
      (centeredAxisCube x₀ R) α K) :
    CauchySeq (dyadicCenteredCubeMeanSeq u (R / 8) x) := by
  have hbase : 0 < R / 8 := by positivity
  have hxnorm : ‖x - x₀‖ ≤ R / 8 :=
    norm_sub_le_of_mem_closedCenteredAxisCube hbase.le hx
  have hsmallCube : ∀ n : ℕ,
      centeredAxisCube x ((R / 8) / (2 : ℝ) ^ n) ⊆
        centeredAxisCube x₀ R := by
    intro n
    have hrn : 0 < (R / 8) / (2 : ℝ) ^ n := dyadicRadius_pos hbase n
    have hrnle : (R / 8) / (2 : ℝ) ^ n ≤ R / 8 :=
      by simpa using dyadicRadius_antitone hbase (Nat.zero_le n)
    apply centeredAxisCube_subset_of_norm_add_lt hrn hR
    linarith
  have hdecayToZero :
      Tendsto (fun n : ℕ => K * (((R / 8) / (2 : ℝ) ^ n) ^ α))
        atTop (𝓝 0) := by
    have hpow : Tendsto (fun n : ℕ =>
        ((R / 8) / (2 : ℝ) ^ n) ^ α) atTop (𝓝 0) := by
      have hcont := Real.continuousAt_rpow_const 0 α (Or.inr hα.le)
      simpa only [Real.zero_rpow hα.ne'] using!
        hcont.tendsto.comp (tendsto_dyadicRadius (R / 8))
    simpa using tendsto_const_nhds.mul hpow
  refine Metric.cauchySeq_iff'.2 fun ε hε => ?_
  have hEventually : ∀ᶠ n in atTop,
      K * (((R / 8) / (2 : ℝ) ^ n) ^ α) < ε :=
    hdecayToZero.eventually (Iio_mem_nhds hε)
  rcases (eventually_atTop.1 hEventually) with ⟨N, hN⟩
  refine ⟨N, fun m hm => ?_⟩
  obtain ⟨a, b, hRange, hab⟩ :=
    hdecay x ((R / 8) / (2 : ℝ) ^ N)
      (dyadicRadius_pos hbase N) (hsmallCube N)
  have hmRange := dyadicCenteredCubeMeanSeq_mem_Icc hbase hm hu hRange
  have hNRange := dyadicCenteredCubeMeanSeq_mem_Icc hbase le_rfl hu hRange
  have hdist :
      dist (dyadicCenteredCubeMeanSeq u (R / 8) x m)
          (dyadicCenteredCubeMeanSeq u (R / 8) x N) ≤
        b - a := by
    rw [Real.dist_eq]
    apply abs_le.mpr
    constructor <;> linarith [hmRange.1, hmRange.2, hNRange.1, hNRange.2]
  exact hdist.trans_lt (hab.trans_lt (hN N le_rfl))

theorem tendsto_dyadicCenteredCubeMeanSeq_of_essentialOscillation
    {u : Vec d → ℝ} {x x₀ : Vec d} {R α K : ℝ}
    (hR : 0 < R) (hα : 0 < α)
    (hu : LocallyIntegrable u volume)
    (hx : x ∈ closedCenteredAxisCube x₀ (R / 8))
    (hdecay : CenteredCubeEssentialOscillationDecayOn u
      (centeredAxisCube x₀ R) α K) :
    Tendsto (dyadicCenteredCubeMeanSeq u (R / 8) x) atTop
      (𝓝 (dyadicCenteredCubeRepresentative u (R / 8) x)) :=
  (cauchySeq_dyadicCenteredCubeMeanSeq_of_essentialOscillation
    hR hα hu hx hdecay).tendsto_limUnder

/-- A local essential-oscillation decay estimate produces a precise Hölder
representative on a strictly interior closed cube. The displayed constant is
`K * 2 ^ α`; importantly, it has no factor growing like `1 / α`. -/
theorem euclideanHolderSeminormLE_dyadicRepresentative_of_essentialOscillation
    {u : Vec d → ℝ} {x₀ : Vec d} {R α K : ℝ}
    (hdecay : CenteredCubeEssentialOscillationDecayOn u
      (centeredAxisCube x₀ R) α K)
    (hR : 0 < R) (hα : 0 < α) (hK : 0 ≤ K)
    (hu : LocallyIntegrable u volume) :
    EuclideanHolderSeminormLE
      (closedCenteredAxisCube x₀ (R / 8)) (dyadicCenteredCubeRepresentative u (R / 8)) α
        (K * (2 : ℝ) ^ α) := by
  let representative : Vec d → ℝ :=
    dyadicCenteredCubeRepresentative u (R / 8)
  · apply supHolderSeminormLE_to_euclidean
    · intro x hx y hy
      by_cases hxy : x = y
      · subst y
        simp [Real.zero_rpow hα.ne']
      let r : ℝ := ‖x - y‖
      have hr : 0 < r := by
        dsimp [r]
        exact norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
      have hxnorm : ‖x - x₀‖ ≤ R / 8 :=
        norm_sub_le_of_mem_closedCenteredAxisCube
          (by positivity : 0 ≤ R / 8) hx
      have hynorm : ‖y - x₀‖ ≤ R / 8 :=
        norm_sub_le_of_mem_closedCenteredAxisCube
          (by positivity : 0 ≤ R / 8) hy
      have hrle : r ≤ R / 4 := by
        dsimp [r]
        calc
          ‖x - y‖ = ‖(x - x₀) + (x₀ - y)‖ := by
            congr 1
            abel
          _ ≤ ‖x - x₀‖ + ‖x₀ - y‖ := norm_add_le _ _
          _ = ‖x - x₀‖ + ‖y - x₀‖ :=
            congrArg (fun t : ℝ => ‖x - x₀‖ + t) (norm_sub_rev _ _)
          _ ≤ R / 4 := by linarith
      have hbigCube : centeredAxisCube x (2 * r) ⊆
          centeredAxisCube x₀ R := by
        apply centeredAxisCube_subset_of_norm_add_lt (by positivity) hR
        linarith
      obtain ⟨a, b, hRange, hab⟩ := hdecay x (2 * r) (by positivity) hbigCube
      have hxlim := tendsto_dyadicCenteredCubeMeanSeq_of_essentialOscillation
        hR hα hu hx hdecay
      have hylim := tendsto_dyadicCenteredCubeMeanSeq_of_essentialOscillation
        hR hα hu hy hdecay
      have hsmall : ∀ᶠ n in atTop, (R / 8) / (2 : ℝ) ^ n < r :=
        (tendsto_dyadicRadius (R / 8)).eventually
          (Iio_mem_nhds hr)
      have hxMem : representative x ∈ Set.Icc a b := by
        apply isClosed_Icc.mem_of_tendsto hxlim
        filter_upwards [hsmall] with n hn
        apply centeredCubeAverage_mem_Icc (dyadicRadius_pos (by positivity) n)
          (locallyIntegrable_integrableOn_centeredAxisCube
            hu x (dyadicRadius_pos (by positivity) n))
        apply hRange.mono
        exact centeredAxisCube_mono x (by linarith)
      have hyMem : representative y ∈ Set.Icc a b := by
        apply isClosed_Icc.mem_of_tendsto hylim
        filter_upwards [hsmall] with n hn
        apply centeredCubeAverage_mem_Icc (dyadicRadius_pos (by positivity) n)
          (locallyIntegrable_integrableOn_centeredAxisCube
            hu y (dyadicRadius_pos (by positivity) n))
        apply hRange.mono
        apply centeredAxisCube_subset_of_norm_add_lt
          (dyadicRadius_pos (by positivity) n) (by positivity)
        dsimp [r] at hn
        simpa only [norm_sub_rev] using (by linarith : ‖x - y‖ +
          (R / 8) / (2 : ℝ) ^ n < 2 * ‖x - y‖)
      calc
        |representative x - representative y| ≤ b - a := by
          apply abs_le.mpr
          constructor <;> linarith [hxMem.1, hxMem.2, hyMem.1, hyMem.2]
        _ ≤ K * (2 * r) ^ α := hab
        _ = (K * (2 : ℝ) ^ α) * ‖x - y‖ ^ α := by
          dsimp [r]
          rw [Real.mul_rpow (by norm_num) (norm_nonneg _)]
          ring
    · exact hα.le
    · exact mul_nonneg hK (Real.rpow_nonneg (by norm_num) _)

end

end PDE.DGNMHolder
