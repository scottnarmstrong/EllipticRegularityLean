module

public import EllipticRegularity.DeGiorgi.Holder.CubeRepresentative
public import PDEFoundation.Geometry.EuclideanBall.Interior
public import PDEFoundation.Measure.AxisBoxVolume
public import PDEFoundation.Regularity.Holder

/-!
# A global Hölder representative from ball oscillation decay

Real analysis only.  A locally integrable function on `ℝ^d` whose essential
oscillation on every small Euclidean ball centred near the origin decays like
`K r ^ α`, and which is essentially bounded by `M` near every point of
`B_{1/2}`, has a representative on `B_{1/2}` which is bounded by `M` and Hölder
of exponent `α` with an explicit constant.
-/

@[expose] public section

namespace PDE.DGNMHolder

open PDE Filter MeasureTheory Topology

variable {d : ℕ}

/-- **Hölder representative from oscillation decay.**  With `κ = 2 √d`, the
representative satisfies `|v| ≤ M` and the Hölder seminorm bound with constant
`2 κ K + 128 κ M`. -/
theorem exists_holderRepresentative_of_oscillationDecay
    {u : Vec d → ℝ} (hd : 0 < d) (hu : LocallyIntegrable u volume)
    {α K M : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hsup : ∀ x ∈ euclideanBall (0 : Vec d) (1 / 2),
      EssentialRangeBoundsOn u (euclideanBall x (1 / 4)) (-M) M)
    (hdec : ∀ z ∈ euclideanBall (0 : Vec d) (5 / 8), ∀ r : ℝ, 0 < r → r ≤ 1 / 8 →
      HasEssentialOscillationLEOn u (euclideanBall z r) (K * r ^ α)) :
    ∃ v : Vec d → ℝ, v =ᵐ[volumeOn (euclideanBall (0 : Vec d) (1 / 2))] u ∧
      (∀ x ∈ euclideanBall (0 : Vec d) (1 / 2), |v x| ≤ M) ∧
      EuclideanHolderSeminormLE (euclideanBall (0 : Vec d) (1 / 2)) v α
        ((2 * (2 * Real.sqrt d)) * K + (128 * (2 * Real.sqrt d)) * M) := by
  set κ : ℝ := 2 * Real.sqrt d with hκdef
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hsqrt1 : 1 ≤ Real.sqrt d := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hd1
  have hκ2 : 2 ≤ κ := by rw [hκdef]; linarith
  have hκ0 : 0 < κ := by linarith
  set R : ℝ := 1 / (8 * κ) with hRdef
  have hR0 : 0 < R := by positivity
  have hκR : κ * R = 1 / 8 := by rw [hRdef]; field_simp
  have hRle : R ≤ 1 / 16 := by
    rw [hRdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  -- cubes sit inside round balls
  have hcubeBall : ∀ (z : Vec d) {r : ℝ}, 0 < r → centeredAxisCube z r ⊆ euclideanBall z (κ * r) := by
    intro z r hr
    have := centeredAxisCube_subset_euclideanBall hd z hr
    simpa [hκdef, mul_assoc] using this
  -- oscillation decay on cubes
  have hcubedec : ∀ x₀ ∈ euclideanBall (0 : Vec d) (1 / 2),
      CenteredCubeEssentialOscillationDecayOn u (centeredAxisCube x₀ R) α (K * κ ^ α) := by
    intro x₀ hx₀ z r hr hsub
    have hzmem : z ∈ centeredAxisCube z r := by
      rw [centeredAxisCube_eq_metric_ball z hr]; exact Metric.mem_ball_self hr
    have hzR : z ∈ euclideanBall x₀ (κ * R) := hcubeBall x₀ hR0 (hsub hzmem)
    have hrR : r ≤ R := by
      have hvol := measure_mono (μ := (volume : Measure (Vec d))) hsub
      rw [volume_centeredAxisCube z hr.le, volume_centeredAxisCube x₀ hR0.le] at hvol
      have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hvol
      have h2 : 2 * r ≤ 2 * R :=
        le_of_pow_le_pow_left₀ hd.ne' (by positivity) this
      linarith
    have hz58 : z ∈ euclideanBall (0 : Vec d) (5 / 8) := by
      rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)]
      rw [hκR, mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)] at hzR
      rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)] at hx₀
      simp only [sub_zero] at hx₀ ⊢
      calc vecEuclideanNorm z = vecEuclideanNorm ((z - x₀) + x₀) := by congr 1; abel
        _ ≤ vecEuclideanNorm (z - x₀) + vecEuclideanNorm x₀ := vecEuclideanNorm_add_le _ _
        _ < 5 / 8 := by linarith
    obtain ⟨a, b, hrange, hab⟩ := hdec z hz58 (κ * r) (by positivity) (by nlinarith)
    refine ⟨a, b, hrange.mono (hcubeBall z hr), ?_⟩
    calc b - a ≤ K * (κ * r) ^ α := hab
      _ = K * κ ^ α * r ^ α := by
        rw [Real.mul_rpow hκ0.le hr.le]; ring
  set v : Vec d → ℝ := dyadicCenteredCubeRepresentative u (R / 8) with hvdef
  have hKκ : 0 ≤ K * κ ^ α := by positivity
  have hHold : ∀ x₀ ∈ euclideanBall (0 : Vec d) (1 / 2),
      EuclideanHolderSeminormLE (closedCenteredAxisCube x₀ (R / 8)) v α
        (K * κ ^ α * (2 : ℝ) ^ α) := fun x₀ hx₀ =>
    euclideanHolderSeminormLE_dyadicRepresentative_of_essentialOscillation
      (hcubedec x₀ hx₀) hR0 hα hKκ hu
  have hbound : ∀ x ∈ euclideanBall (0 : Vec d) (1 / 2), |v x| ≤ M := by
    intro x hx
    have hxmem : x ∈ closedCenteredAxisCube x (R / 8) := by
      rw [closedCenteredAxisCube_eq_metric_closedBall x (by positivity)]
      exact Metric.mem_closedBall_self (by positivity)
    have hlim := tendsto_dyadicCenteredCubeMeanSeq_of_essentialOscillation hR0 hα hu hxmem
      (hcubedec x hx)
    have hmem : ∀ n : ℕ, dyadicCenteredCubeMeanSeq u (R / 8) x n ∈ Set.Icc (-M) M := by
      intro n
      have hrn : 0 < (R / 8) / (2 : ℝ) ^ n := by positivity
      have hle : (R / 8) / (2 : ℝ) ^ n ≤ R / 8 := by
        apply div_le_self (by positivity)
        exact one_le_pow₀ (by norm_num)
      apply centeredCubeAverage_mem_Icc hrn
        (locallyIntegrable_integrableOn_centeredAxisCube hu x hrn)
      apply (hsup x hx).mono
      refine (hcubeBall x hrn).trans (euclideanBall_mono (by positivity) ?_)
      have : κ * ((R / 8) / (2 : ℝ) ^ n) ≤ κ * (R / 8) := by
        apply mul_le_mul_of_nonneg_left hle hκ0.le
      nlinarith
    have hvmem : v x ∈ Set.Icc (-M) M :=
      isClosed_Icc.mem_of_tendsto hlim (Eventually.of_forall hmem)
    exact abs_le.2 ⟨hvmem.1, hvmem.2⟩
  refine ⟨v, ?_, hbound, ?_⟩
  · exact ae_restrict_of_ae (dyadicCenteredCubeRepresentative_ae_eq hu (by positivity))
  · -- Hölder
    intro x hx y hy
    set e : ℝ := vecEuclideanNorm (x - y) with hedef
    have he0 : 0 ≤ e := vecEuclideanNorm_nonneg _
    have hepow : 0 ≤ e ^ α := Real.rpow_nonneg he0 _
    have hK2 : 0 ≤ (2 * κ) * K := by positivity
    have hM2 : 0 ≤ (128 * κ) * M := by positivity
    by_cases hnear : ‖x - y‖ ≤ R / 8
    · have hyc : y ∈ closedCenteredAxisCube x (R / 8) := by
        rw [closedCenteredAxisCube_eq_metric_closedBall x (by positivity), Metric.mem_closedBall,
          dist_eq_norm, norm_sub_rev]
        exact hnear
      have hxc : x ∈ closedCenteredAxisCube x (R / 8) := by
        rw [closedCenteredAxisCube_eq_metric_closedBall x (by positivity)]
        exact Metric.mem_closedBall_self (by positivity)
      have h1 := hHold x hx x hxc y hyc
      have hκα : κ ^ α ≤ κ := by
        calc κ ^ α ≤ κ ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hα1
          _ = κ := Real.rpow_one _
      have h2α : (2 : ℝ) ^ α ≤ 2 := by
        calc (2 : ℝ) ^ α ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1
          _ = 2 := Real.rpow_one _
      have hcoef : K * κ ^ α * (2 : ℝ) ^ α ≤ (2 * κ) * K := by
        calc K * κ ^ α * (2 : ℝ) ^ α ≤ K * κ * 2 := by
              apply mul_le_mul (mul_le_mul_of_nonneg_left hκα hK) h2α (by positivity) (by positivity)
          _ = (2 * κ) * K := by ring
      calc |v x - v y| ≤ K * κ ^ α * (2 : ℝ) ^ α * e ^ α := h1
        _ ≤ (2 * κ) * K * e ^ α := mul_le_mul_of_nonneg_right hcoef hepow
        _ ≤ ((2 * κ) * K + (128 * κ) * M) * e ^ α :=
          mul_le_mul_of_nonneg_right (by linarith) hepow
    · push Not at hnear
      have hεge : R / 8 < e := lt_of_lt_of_le hnear (norm_le_vecEuclideanNorm _)
      have hdiff : |v x - v y| ≤ 2 * M := by
        have := hbound x hx
        have := hbound y hy
        calc |v x - v y| ≤ |v x| + |v y| := abs_sub _ _
          _ ≤ 2 * M := by linarith
      have hratio : 1 ≤ (8 / R) := by
        rw [le_div_iff₀ hR0]; linarith
      have h8R : 8 / R = 64 * κ := by rw [hRdef]; field_simp; ring
      have hone : 1 ≤ (8 / R) ^ α * e ^ α := by
        rw [← Real.mul_rpow (by positivity) he0]
        apply Real.one_le_rpow _ hα.le
        rw [div_mul_eq_mul_div, le_div_iff₀ hR0]; linarith
      have hbig : (8 / R) ^ α ≤ 64 * κ := by
        calc (8 / R) ^ α ≤ (8 / R) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hratio hα1
          _ = 64 * κ := by rw [Real.rpow_one, h8R]
      calc |v x - v y| ≤ 2 * M := hdiff
        _ ≤ 2 * M * ((8 / R) ^ α * e ^ α) := by nlinarith
        _ ≤ 2 * M * (64 * κ * e ^ α) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_right hbig hepow
        _ = (128 * κ) * M * e ^ α := by ring
        _ ≤ ((2 * κ) * K + (128 * κ) * M) * e ^ α :=
            mul_le_mul_of_nonneg_right (by linarith) hepow

end PDE.DGNMHolder
