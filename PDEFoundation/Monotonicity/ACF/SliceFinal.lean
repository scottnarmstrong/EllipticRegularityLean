module

public import PDEFoundation.Monotonicity.ACF.SliceFinalAux

/-!
# ACF-S2: Rayleigh inequality on a.e. sphere for a continuous nonnegative `H¹` function

For `u ∈ H¹(B_R)` continuous and nonnegative and almost every `r ∈ (0, R)`, with
`Ω(r) = {ω | 0 < u (r ω)}`,
`∫_{S} (∇u(rω)·ω)² + λ(Ω(r)) r⁻² ∫_{S} u(rω)² ≤ ∫_{S} |∇u(rω)|²`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace PDE

noncomputable section

variable {d : ℕ}

theorem vecNormSq_indicator_apply (S : Set (Vec d)) (g : Vec d → Vec d) (x : Vec d) :
    vecNormSq (S.indicator g x) = S.indicator (fun y => vecNormSq (g y)) x := by
  by_cases hx : x ∈ S
  · simp [indicator_of_mem hx]
  · simp [indicator_of_notMem hx, vecNormSq, vecDot]

theorem vecDot_sq_indicator_apply (S : Set (Vec d)) (g : Vec d → Vec d) (x : Vec d) :
    vecDot (S.indicator g x) (unitDir x) ^ 2 =
      S.indicator (fun y => vecDot (g y) (unitDir y) ^ 2) x := by
  by_cases hx : x ∈ S
  · simp [indicator_of_mem hx]
  · simp [indicator_of_notMem hx, vecDot]

theorem sliceIntegrable_of_continuous {G : Vec d → ℝ} (hG : Continuous G) (r : ℝ) :
    SliceIntegrable G r :=
  integrable_sphere_comp hG.continuousOn

/-- The truncation levels `δₖ = 1 / (k + 1)`. -/
def truncLevel (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

theorem truncLevel_pos (k : ℕ) : 0 < truncLevel k := by
  unfold truncLevel; positivity

theorem tendsto_truncLevel : Tendsto truncLevel atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem tendsto_indicator_truncLevel (u F : Vec d → ℝ) (x : Vec d) :
    Tendsto (fun k => {y | truncLevel k < u y}.indicator F x) atTop
      (𝓝 ({y | 0 < u y}.indicator F x)) := by
  by_cases hx : 0 < u x
  · have hev : ∀ᶠ k in atTop, truncLevel k < u x := (tendsto_order.1 tendsto_truncLevel).2 _ hx
    rw [indicator_of_mem (show x ∈ {y | 0 < u y} from hx)]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with k hk
    rw [indicator_of_mem (show x ∈ {y | truncLevel k < u y} from hk)]
  · have : ∀ k, x ∉ {y | truncLevel k < u y} := fun k hk =>
      hx (lt_trans (truncLevel_pos k) hk)
    simp only [indicator_of_notMem (show x ∉ {y | 0 < u y} from hx), indicator_of_notMem (this _)]
    exact tendsto_const_nhds

theorem tendsto_sliceIntegral_indicator_truncLevel {u F : Vec d → ℝ} (hF0 : ∀ x, 0 ≤ F x)
    {r : ℝ} (hF : SliceIntegrable F r)
    (hm : ∀ k, SliceIntegrable ({y | truncLevel k < u y}.indicator F) r) :
    Tendsto (fun k => sliceIntegral ({y | truncLevel k < u y}.indicator F) r) atTop
      (𝓝 (sliceIntegral ({y | 0 < u y}.indicator F) r)) := by
  refine tendsto_sliceIntegral_of_dominated hF hm (fun k x => ?_)
    (tendsto_indicator_truncLevel u F)
  rw [abs_of_nonneg (indicator_nonneg (fun y _ => hF0 y) x)]
  exact indicator_le_self' (fun y _ => hF0 y) x

theorem sliceIntegral_pos_indicator_eq {u F : Vec d → ℝ} {r : ℝ} (hF : SliceIntegrable F r)
    (h0 : SliceIntegrable ({y | u y ≤ 0}.indicator F) r)
    (h0z : sliceIntegral ({y | u y ≤ 0}.indicator F) r = 0) :
    sliceIntegral ({y | 0 < u y}.indicator F) r = sliceIntegral F r := by
  have hfun : {y | 0 < u y}.indicator F =
      fun x => F x - {y | u y ≤ 0}.indicator F x := by
    funext x
    by_cases hx : 0 < u x
    · have : x ∉ {y | u y ≤ 0} := fun h => absurd h (not_le.2 hx)
      simp [indicator_of_mem (show x ∈ {y | 0 < u y} from hx), indicator_of_notMem this]
    · have : x ∈ {y | u y ≤ 0} := not_lt.1 hx
      simp [indicator_of_notMem (show x ∉ {y | 0 < u y} from hx), indicator_of_mem this]
  rw [hfun, SliceIntegrable.sliceIntegral_sub hF h0, h0z, sub_zero]

theorem vecNormSq_zero' : vecNormSq (0 : Vec d) = 0 := by simp [vecNormSq, vecDot]

/-- **ACF-S2.** For `u ∈ H¹(B_R)` continuous and nonnegative and almost every `r ∈ (0, R)`, the
slice integrals of `u.grad` are defined and
`∫ (∇u·ω)² + λ(Ω(r)) r⁻² ∫ u² ≤ ∫ |∇u|²`, with `Ω(r) = {y | 0 < u (r y)}`. -/
theorem acf_slice_rayleigh_ae [NeZero d] {R : ℝ} (hR : 0 < R)
    (u : H1Function (euclideanBall (0 : Vec d) R)) (hu : Continuous u.toFun)
    (hnn : ∀ x, 0 ≤ u.toFun x) :
    ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R)),
      SliceIntegrable (fun x => vecNormSq (u.grad x)) r ∧
      SliceIntegrable (fun x => vecDot (u.grad x) (unitDir x) ^ 2) r ∧
      sliceIntegral (fun x => vecDot (u.grad x) (unitDir x) ^ 2) r +
          (sphereDirichletEigenvalue d {y | 0 < u.toFun (r • y)}).toReal * r⁻¹ ^ 2 *
            sliceIntegral (fun x => u.toFun x ^ 2) r ≤
        sliceIntegral (fun x => vecNormSq (u.grad x)) r := by
  have hU := isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) hR
  have hB : MeasurableSet (euclideanBall (0 : Vec d) R) := measurableSet_euclideanBall_zero R
  set F : Vec d → ℝ := fun x => vecNormSq (u.grad x) with hFdef
  set K : Vec d → ℝ := fun x => vecDot (u.grad x) (unitDir x) ^ 2 with hKdef
  have hF0 : ∀ x, 0 ≤ F x := fun x => vecNormSq_nonneg _
  have hK0 : ∀ x, 0 ≤ K x := fun x => sq_nonneg _
  have hFint : Integrable F (volume.restrict (euclideanBall (0 : Vec d) R)) :=
    integrable_vecNormSq_of_coord fun i => u.gradMemL2 i
  have hKint : Integrable K (volume.restrict (euclideanBall (0 : Vec d) R)) :=
    hFint.mono' ((aestronglyMeasurable_vecDot_unitDir
      (fun i => (u.gradMemL2 i).aestronglyMeasurable)).pow 2)
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hK0 x)]; exact sq_vecDot_unitDir_le _ _)
  have hIF : Integrable ((euclideanBall (0 : Vec d) R).indicator F) :=
    (integrable_indicator_iff hB).2 hFint
  have hIK : Integrable ((euclideanBall (0 : Vec d) R).indicator K) :=
    (integrable_indicator_iff hB).2 hKint
  have hsub : ∀ {P : ℝ → Prop}, (∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), P r) →
      ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R)), P r := fun h =>
    ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioi_self : Ioo (0 : ℝ) R ⊆ Ioi (0 : ℝ)) h
  have haeF := hsub (polar_slices hIF).1
  have haeK := hsub (polar_slices hIK).1
  have hgz : ∀ᵐ x, x ∈ euclideanBall (0 : Vec d) R → u.toFun x = 0 → u.grad x = 0 :=
    (ae_restrict_iff' hB).1 (H1Function.grad_ae_zero_on_level_set hU u 0)
  have hzF : (euclideanBall (0 : Vec d) R).indicator ({y | u.toFun y ≤ 0}.indicator F) =ᵐ[volume] 0 := by
    filter_upwards [hgz] with x hx
    by_cases hxB : x ∈ euclideanBall (0 : Vec d) R
    · by_cases hxu : u.toFun x ≤ 0
      · have := hx hxB (le_antisymm hxu (hnn x))
        simp [indicator_of_mem hxB, indicator_of_mem (show x ∈ {y | u.toFun y ≤ 0} from hxu),
          hFdef, this, vecNormSq_zero']
      · simp [indicator_of_mem hxB, indicator_of_notMem (show x ∉ {y | u.toFun y ≤ 0} from hxu)]
    · simp [indicator_of_notMem hxB]
  have hzK : (euclideanBall (0 : Vec d) R).indicator ({y | u.toFun y ≤ 0}.indicator K) =ᵐ[volume] 0 := by
    filter_upwards [hgz] with x hx
    by_cases hxB : x ∈ euclideanBall (0 : Vec d) R
    · by_cases hxu : u.toFun x ≤ 0
      · have := hx hxB (le_antisymm hxu (hnn x))
        simp [indicator_of_mem hxB, indicator_of_mem (show x ∈ {y | u.toFun y ≤ 0} from hxu),
          hKdef, this, vecDot]
      · simp [indicator_of_mem hxB, indicator_of_notMem (show x ∉ {y | u.toFun y ≤ 0} from hxu)]
    · simp [indicator_of_notMem hxB]
  have haeZF := hsub (ae_sliceIntegral_eq_zero hzF)
  have haeZK := hsub (ae_sliceIntegral_eq_zero hzK)
  have haeT : ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R)), ∀ k : ℕ,
      SliceIntegrable (fun x => vecNormSq (({y | truncLevel k < u.toFun y}.indicator u.grad) x)) r ∧
      SliceIntegrable (fun x => max (u.toFun x - truncLevel k) 0 ^ 2) r ∧
      SliceIntegrable (fun x => vecDot (({y | truncLevel k < u.toFun y}.indicator u.grad) x)
        (unitDir x) ^ 2) r ∧
      sliceIntegral (fun x => vecDot (({y | truncLevel k < u.toFun y}.indicator u.grad) x)
          (unitDir x) ^ 2) r +
        (sphereDirichletEigenvalue d {y | 0 < u.toFun (r • y)}).toReal * r⁻¹ ^ 2 *
          sliceIntegral (fun x => max (u.toFun x - truncLevel k) 0 ^ 2) r ≤
      sliceIntegral (fun x => vecNormSq (({y | truncLevel k < u.toFun y}.indicator u.grad) x)) r :=
    ae_all_iff.2 fun k => ae_rayleigh_truncation hR u hu (truncLevel_pos k)
  have hmem : ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R)), r ∈ Ioo (0 : ℝ) R :=
    ae_restrict_mem measurableSet_Ioo
  filter_upwards [haeF, haeK, haeZF, haeZK, haeT, hmem] with r hrF hrK hrZF hrZK hrT hr
  have hF1 : SliceIntegrable F r := (SliceIntegrable.indicator_ball_iff hr F).1 hrF
  have hK1 : SliceIntegrable K r := (SliceIntegrable.indicator_ball_iff hr K).1 hrK
  have hZF1 : SliceIntegrable ({y | u.toFun y ≤ 0}.indicator F) r ∧
      sliceIntegral ({y | u.toFun y ≤ 0}.indicator F) r = 0 := by
    obtain ⟨h1, h2⟩ := hrZF
    exact ⟨(SliceIntegrable.indicator_ball_iff hr _).1 h1, by
      rwa [sliceIntegral_indicator_ball hr] at h2⟩
  have hZK1 : SliceIntegrable ({y | u.toFun y ≤ 0}.indicator K) r ∧
      sliceIntegral ({y | u.toFun y ≤ 0}.indicator K) r = 0 := by
    obtain ⟨h1, h2⟩ := hrZK
    exact ⟨(SliceIntegrable.indicator_ball_iff hr _).1 h1, by
      rwa [sliceIntegral_indicator_ball hr] at h2⟩
  refine ⟨hF1, hK1, ?_⟩
  have hFk : ∀ k, (fun x => vecNormSq (({y | truncLevel k < u.toFun y}.indicator u.grad) x)) =
      {y | truncLevel k < u.toFun y}.indicator F := fun k => by
    funext x; exact vecNormSq_indicator_apply _ _ _
  have hKk : ∀ k, (fun x => vecDot (({y | truncLevel k < u.toFun y}.indicator u.grad) x)
        (unitDir x) ^ 2) = {y | truncLevel k < u.toFun y}.indicator K := fun k => by
    funext x; exact vecDot_sq_indicator_apply _ _ _
  have hTF := tendsto_sliceIntegral_indicator_truncLevel (u := u.toFun) hF0 hF1
    (fun k => by simpa only [hFk k] using (hrT k).1)
  have hTK := tendsto_sliceIntegral_indicator_truncLevel (u := u.toFun) hK0 hK1
    (fun k => by simpa only [hKk k] using (hrT k).2.2.1)
  have hTV : Tendsto (fun k => sliceIntegral (fun x => max (u.toFun x - truncLevel k) 0 ^ 2) r)
      atTop (𝓝 (sliceIntegral (fun x => u.toFun x ^ 2) r)) := by
    refine tendsto_sliceIntegral_of_dominated (H := fun x => u.toFun x ^ 2)
      (sliceIntegrable_of_continuous (hu.pow 2) r) (fun k => (hrT k).2.1) (fun k x => ?_)
      (fun x => ?_)
    · have h1 := hnn x
      have h2 := truncLevel_pos k
      rw [abs_of_nonneg (sq_nonneg _)]
      have : max (u.toFun x - truncLevel k) 0 ≤ u.toFun x := max_le (by linarith) h1
      exact pow_le_pow_left₀ (le_max_right _ _) this 2
    · have := (((tendsto_const_nhds : Tendsto (fun _ : ℕ => u.toFun x) atTop (𝓝 (u.toFun x))).sub
        tendsto_truncLevel).max
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))).pow 2
      simpa [max_eq_left (hnn x)] using this
  have hlim := hTK.add (hTV.const_mul
    ((sphereDirichletEigenvalue d {y | 0 < u.toFun (r • y)}).toReal * r⁻¹ ^ 2))
  have hineq := le_of_tendsto_of_tendsto' hlim hTF fun k => by
    have := (hrT k).2.2.2
    simpa only [hFk k, hKk k, mul_assoc] using this
  rw [sliceIntegral_pos_indicator_eq hF1 hZF1.1 hZF1.2,
    sliceIntegral_pos_indicator_eq hK1 hZK1.1 hZK1.2] at hineq
  simpa only [mul_assoc] using hineq

end

end PDE
