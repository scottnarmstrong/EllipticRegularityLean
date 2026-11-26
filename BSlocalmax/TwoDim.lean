module

public import Mathlib
public import BSlocalmax.CubeBasics
public import BSlocalmax.FaceInequalities
public import BSlocalmax.HighDim
public import BSlocalmax.ShellSmoothing
public import PDEFoundation.Sobolev.H1.ZeroGradient

/-!
# The case d = 2: trace-free maximum principle and good radii

This file collects the following pieces, in dependency order: CacciCube, ProfileE, ProfileE2, ProfileE3, MaxPrinciple2A, MaxPrinciple2B, MaxPrinciple2, AEFace, FaceInt, Face1D, GoodRadii, GoodMarkov, Dim2, Dim2Main.
-/

-- ==== from CacciCube.lean ====
-- Caccioppoli inequality for arbitrary Euclidean-Lipschitz cutoffs `η` (cube cutoff).


@[expose] public section

open MeasureTheory Set Filter PDE PDE.Ch4Infra

namespace PDE.BSlocalmax

variable {n : ℕ}

set_option maxHeartbeats 1600000 in
/-- `∫_{Q_ρ} |∇(u-k)₊|² ≤ 10 Λ ∫_{Q_1} (u-k)₊² |∇η|²` for every Lipschitz cutoff `η`
with `η = 1` on `Q_ρ` and `η = 0` outside `Q_σ`, `σ < 1`. -/
theorem caccioppoli_cube {Λ ρ σ k K : ℝ} {a : CoeffField (n + 1)} (hρσ : ρ < σ) (hσ : σ < 1)
    (hρ0 : 0 ≤ ρ)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn (Metric.ball (0 : Vec (n + 1)) 1)))
    (hEll : ∀ x ∈ Metric.ball (0 : Vec (n + 1)) 1, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function (Metric.ball (0 : Vec (n + 1)) 1)}
    (hsub : IsWeakDivergenceFormSubharmonicOn a (Metric.ball (0 : Vec (n + 1)) 1) u)
    {η : Vec (n + 1) → ℝ} (hη : EucLip K η) (hK0 : 0 ≤ K)
    (h01 : ∀ x, η x ∈ Icc (0 : ℝ) 1) (h1 : ∀ x, ‖x‖ ≤ ρ → η x = 1)
    (h0 : ∀ x, σ ≤ ‖x‖ → η x = 0) :
    ∫ x in Metric.ball (0 : Vec (n + 1)) ρ,
        vecNormSq ({y | k < u.toFun y}.indicator u.grad x) ≤
      10 * Λ * ∫ x in Metric.ball (0 : Vec (n + 1)) 1,
        (max (u.toFun x - k) 0) ^ 2 * vecNormSq (classicalGradient η x) := by
  have hU : IsOpen (Metric.ball (0 : Vec (n + 1)) 1) := Metric.isOpen_ball
  have hfin : volume (Metric.ball (0 : Vec (n + 1)) 1) ≠ ⊤ :=
    Metric.isBounded_ball.measure_lt_top.ne
  have hM : ∀ x, |η x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (h01 x).1]; exact (h01 x).2
  have hηsub : Function.support η ⊆ Metric.closedBall (0 : Vec (n + 1)) σ := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hc'
    exact hx (h0 x (le_of_lt (not_le.1 hc')))
  have hηc : HasCompactSupport η :=
    HasCompactSupport.intro (isCompact_closedBall _ _) (fun x hx => by
      by_contra hx0
      exact hx (hηsub hx0))
  have hηU : tsupport η ⊆ Metric.ball (0 : Vec (n + 1)) 1 :=
    (closure_minimal hηsub Metric.isClosed_closedBall).trans
      (Metric.closedBall_subset_ball hσ)
  have hcacc := caccioppoli_energy_positivePart_ten_open hU hfin ha hEll hsub k hη hK0 hM hηc hηU
  have hηcont : Continuous η := hη.continuous hK0
  have hwL2 : MemL2On (Metric.ball (0 : Vec (n + 1)) 1) (fun x => max (u.toFun x - k) 0) :=
    memL2On_positivePart_of_finite u hfin k
  have hξL2 : MemVectorL2On (Metric.ball (0 : Vec (n + 1)) 1)
      (fun x => {y | k < u.toFun y}.indicator u.grad x) := posPartGrad_gradMemL2 u k
  have hA : MemVectorL2On (Metric.ball (0 : Vec (n + 1)) 1)
      (fun x => η x • {y | k < u.toFun y}.indicator u.grad x) := fun i => by
    simpa only [Pi.smul_apply, smul_eq_mul] using memL2On_mul_bounded (hξL2 i) hηcont hM
  have hB : MemVectorL2On (Metric.ball (0 : Vec (n + 1)) 1)
      (fun x => max (u.toFun x - k) 0 • classicalGradient η x) := fun i => by
    simpa only [Pi.smul_apply, smul_eq_mul, classicalGradient] using
      memL2On_mul_partialDeriv hη hK0 hwL2 i
  have hABsq := integrableOn_vecNormSq_of_memVectorL2On (fun i => (hA i).add (hB i))
  have hin : ∫ x in Metric.ball (0 : Vec (n + 1)) ρ,
        vecNormSq ({y | k < u.toFun y}.indicator u.grad x) =
      ∫ x in Metric.ball (0 : Vec (n + 1)) ρ,
        vecNormSq (η x • {y | k < u.toFun y}.indicator u.grad x +
          max (u.toFun x - k) 0 • classicalGradient η x) := by
    refine setIntegral_congr_fun Metric.isOpen_ball.measurableSet (fun x hx => ?_)
    have hxn : ‖x‖ < ρ := by simpa using hx
    have hev : ∀ᶠ y in nhds x, η y = 1 :=
      Filter.mem_of_superset ((isOpen_lt continuous_norm continuous_const).mem_nhds hxn)
        (fun y hy => h1 y (le_of_lt hy))
    have h0' := classicalGradient_eq_zero_of_eventually hev
    simp only [h1 x hxn.le, h0', one_smul, smul_zero, add_zero]
  have hmono : ∫ x in Metric.ball (0 : Vec (n + 1)) ρ,
        vecNormSq (η x • {y | k < u.toFun y}.indicator u.grad x +
          max (u.toFun x - k) 0 • classicalGradient η x) ≤
      ∫ x in Metric.ball (0 : Vec (n + 1)) 1,
        vecNormSq (η x • {y | k < u.toFun y}.indicator u.grad x +
          max (u.toFun x - k) 0 • classicalGradient η x) :=
    setIntegral_mono_set hABsq (Filter.Eventually.of_forall (fun x => vecNormSq_nonneg' _))
      (HasSubset.Subset.eventuallyLE (Metric.ball_subset_ball (by linarith)))
  exact hin.le.trans (hmono.trans hcacc)

end PDE.BSlocalmax
end

-- ==== from ProfileE.lean ====
-- Cutoff profile `φ(r) = 1 - |E ∩ (-∞,r]| / |E|` with `φ' = -1_E/|E|` almost everywhere:
-- gives `∫ g |∇η|² = 0` if the boundary integral of `g` vanishes on `E`.


@[expose] public section

open MeasureTheory Set Filter Topology PDE PDE.Ch4Infra

namespace PDE.BSlocalmax

variable {n : ℕ}

/-- Distribution function of the measure `1_E dr`. -/
noncomputable def Fprof (E : Set ℝ) (r : ℝ) : ℝ := (volume (E ∩ Iic r)).toReal

lemma Fprof_sub {E : Set ℝ} (hE : MeasurableSet E) (hfin : volume E ≠ ⊤) {r s : ℝ}
    (hrs : r ≤ s) : Fprof E s - Fprof E r = (volume (E ∩ Ioc r s)).toReal := by
  have hsplit : E ∩ Iic s = (E ∩ Iic r) ∪ (E ∩ Ioc r s) := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_union, mem_Ioc]
    constructor
    · rintro ⟨hx, hxs⟩
      by_cases h : x ≤ r
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, not_le.1 h, hxs⟩
    · rintro (⟨hx, h⟩ | ⟨hx, _, h⟩)
      · exact ⟨hx, h.trans hrs⟩
      · exact ⟨hx, h⟩
  have hdisj : Disjoint (E ∩ Iic r) (E ∩ Ioc r s) := by
    rw [Set.disjoint_left]
    rintro x ⟨_, h1⟩ ⟨_, h2, _⟩
    exact absurd (mem_Iic.1 h1) (not_le.2 h2)
  have hfin1 : volume (E ∩ Iic r) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (measure_mono inter_subset_left)
  have hfin2 : volume (E ∩ Ioc r s) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (measure_mono inter_subset_left)
  unfold Fprof
  rw [hsplit, measure_union hdisj (hE.inter measurableSet_Ioc), ENNReal.toReal_add hfin1 hfin2]
  ring

lemma vol_Ioc_inter_le {E : Set ℝ} {r s : ℝ} (hrs : r ≤ s) :
    (volume (E ∩ Ioc r s)).toReal ≤ s - r := by
  have h1 : volume (E ∩ Ioc r s) ≤ ENNReal.ofReal (s - r) := by
    calc volume (E ∩ Ioc r s) ≤ volume (Ioc r s) := measure_mono inter_subset_right
      _ = ENNReal.ofReal (s - r) := Real.volume_Ioc
  calc (volume (E ∩ Ioc r s)).toReal ≤ (ENNReal.ofReal (s - r)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    _ = s - r := ENNReal.toReal_ofReal (by linarith)

lemma Fprof_lipschitz {E : Set ℝ} (hE : MeasurableSet E) (hfin : volume E ≠ ⊤) :
    LipschitzWith 1 (Fprof E) := by
  refine LipschitzWith.of_dist_le_mul fun r s => ?_
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  rcases le_total r s with h | h
  · have h1 := Fprof_sub hE hfin h
    have h2 := vol_Ioc_inter_le (E := E) h
    have h3 : 0 ≤ (volume (E ∩ Ioc r s)).toReal := ENNReal.toReal_nonneg
    have h4 : |r - s| = s - r := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    rw [h4, abs_le]
    constructor <;> linarith
  · have h1 := Fprof_sub hE hfin h
    have h2 := vol_Ioc_inter_le (E := E) h
    have h3 : 0 ≤ (volume (E ∩ Ioc s r)).toReal := ENNReal.toReal_nonneg
    have h4 : |r - s| = r - s := abs_of_nonneg (by linarith)
    rw [h4, abs_le]
    constructor <;> linarith

lemma Fprof_nonneg (E : Set ℝ) (r : ℝ) : 0 ≤ Fprof E r := ENNReal.toReal_nonneg

lemma Fprof_le_vol {E : Set ℝ} (hfin : volume E ≠ ⊤) (r : ℝ) :
    Fprof E r ≤ (volume E).toReal :=
  ENNReal.toReal_mono hfin (measure_mono inter_subset_left)

/-- Lebesgue density: `Fprof E` has derivative `0` at almost every `r ∉ E`. -/
lemma ae_hasDerivAt_Fprof {E : Set ℝ} (hE : MeasurableSet E) (hfin : volume E ≠ ⊤) :
    ∀ᵐ r ∂(volume : Measure ℝ), r ∉ E → HasDerivAt (Fprof E) 0 r := by
  have h := IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div (volume : Measure ℝ) Eᶜ 1
  rw [ae_restrict_iff' hE.compl] at h
  filter_upwards [h] with x hx hxE
  have hxc : x ∈ Eᶜ := hxE
  have hT := hx hxc (ι := ℝ) (l := 𝓝[>] (0 : ℝ)) (fun _ => x) id tendsto_id (by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    simp only [id, one_mul, Metric.mem_closedBall, dist_self]
    exact le_of_lt hδ)
  -- Real version
  have hsum : ∀ δ : ℝ, 0 < δ →
      (volume (E ∩ Metric.closedBall x δ)).toReal +
        (volume (Eᶜ ∩ Metric.closedBall x δ)).toReal = 2 * δ := by
    intro δ hδ
    have h1 := measure_inter_add_sdiff (μ := (volume : Measure ℝ)) (Metric.closedBall x δ) hE
    have hfinb : volume (Metric.closedBall x δ) ≠ ⊤ := by
      rw [Real.volume_closedBall]; exact ENNReal.ofReal_ne_top
    have h2 : volume (Metric.closedBall x δ ∩ E) ≠ ⊤ :=
      ne_top_of_le_ne_top hfinb (measure_mono inter_subset_left)
    have h3 : volume (Metric.closedBall x δ \ E) ≠ ⊤ :=
      ne_top_of_le_ne_top hfinb (measure_mono diff_subset)
    have h4 := congrArg ENNReal.toReal h1
    rw [ENNReal.toReal_add h2 h3, Real.volume_closedBall, ENNReal.toReal_ofReal (by linarith)]
      at h4
    rw [inter_comm E, inter_comm Eᶜ, ← Set.diff_eq]
    exact h4
  have hT' : Tendsto (fun δ : ℝ => (volume (Eᶜ ∩ Metric.closedBall x δ)).toReal / (2 * δ))
      (𝓝[>] 0) (𝓝 1) := by
    have := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp hT
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    simp only [Function.comp, id, Real.volume_closedBall]
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (by linarith [mem_Ioi.1 hδ])]
  have hA : Tendsto (fun δ : ℝ => (volume (E ∩ Metric.closedBall x δ)).toReal / (2 * δ))
      (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun δ : ℝ => 1 - (volume (Eᶜ ∩ Metric.closedBall x δ)).toReal / (2 * δ))
        (𝓝[>] 0) (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hT'
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ' : 0 < δ := hδ
    have := hsum δ hδ'
    field_simp
    linarith
  have hev : ∀ c : ℝ, 0 < c → ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (volume (E ∩ Metric.closedBall x δ)).toReal ≤ c * δ := by
    intro c hc
    have := (hA.eventually (gt_mem_nhds (show (0 : ℝ) < c / 2 by positivity)))
    filter_upwards [this, self_mem_nhdsWithin] with δ h1 hδ
    have hδ' : 0 < δ := hδ
    rw [div_lt_iff₀ (by linarith)] at h1
    linarith
  rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨ε, hε, hεP⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hev c hc)
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with h hh
  simp only [smul_zero, sub_zero, Real.norm_eq_abs]
  rcases eq_or_ne h 0 with rfl | hne
  · simp
  have hδ : |h| ∈ Ioo (0 : ℝ) ε := ⟨abs_pos.2 hne, by simpa using hh⟩
  have hb : (volume (E ∩ Metric.closedBall x |h|)).toReal ≤ c * |h| := hεP hδ
  have hfin' : ∀ S : Set ℝ, volume (E ∩ S) ≠ ⊤ := fun S =>
    ne_top_of_le_ne_top hfin (measure_mono inter_subset_left)
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have h1 := Fprof_sub hE hfin (show x + h ≤ x by linarith)
    have h2 : (volume (E ∩ Ioc (x + h) x)).toReal ≤
        (volume (E ∩ Metric.closedBall x |h|)).toReal :=
      ENNReal.toReal_mono (hfin' _) (measure_mono (inter_subset_inter_right _ (fun y hy => by
        rw [Metric.mem_closedBall, Real.dist_eq, abs_of_neg hneg]
        exact abs_le.2 ⟨by linarith [hy.1], by linarith [hy.2]⟩)))
    rw [abs_sub_comm, abs_of_nonneg (by rw [h1]; exact ENNReal.toReal_nonneg)]
    linarith
  · have h1 := Fprof_sub hE hfin (show x ≤ x + h by linarith)
    have h2 : (volume (E ∩ Ioc x (x + h))).toReal ≤
        (volume (E ∩ Metric.closedBall x |h|)).toReal :=
      ENNReal.toReal_mono (hfin' _) (measure_mono (inter_subset_inter_right _ (fun y hy => by
        rw [Metric.mem_closedBall, Real.dist_eq, abs_of_pos hpos]
        exact abs_le.2 ⟨by linarith [hy.1], by linarith [hy.2]⟩)))
    rw [abs_of_nonneg (by rw [h1]; exact ENNReal.toReal_nonneg)]
    linarith

end PDE.BSlocalmax
end

-- ==== from ProfileE2.lean ====
-- Cutoff with `∫ g |∇η|² = 0` if the boundary integral of `g` vanishes on a
-- set `E` of positive measure.


@[expose] public section

open MeasureTheory Set Filter Topology PDE PDE.Ch4Infra

namespace PDE.BSlocalmax

variable {n : ℕ}

lemma vecNormSq_zero_vec {d : ℕ} : vecNormSq (0 : Vec d) = 0 := by
  have := vecNormSq_smul (0 : ℝ) (0 : Vec d)
  simpa using this

/-- The preimage of a null set under the sup norm is a null set. -/
lemma volume_preimage_norm_null {N : Set ℝ} (hN : volume N = 0) :
    volume {x : Vec (n + 1) | ‖x‖ ∈ N} = 0 := by
  obtain ⟨N', hNN', hN'm, hN'0⟩ : ∃ N', N ⊆ N' ∧ MeasurableSet N' ∧ volume N' = 0 :=
    ⟨toMeasurable volume N, subset_toMeasurable _ _, measurableSet_toMeasurable _ _, by
      rw [measure_toMeasurable]; exact hN⟩
  set P : Set (Vec (n + 1)) := {x | ‖x‖ ∈ N'} with hP
  refine measure_mono_null (fun x hx => (hNN' hx : ‖x‖ ∈ N')) ?_
  set c : ℝ → ℝ := N'.indicator (fun _ => (1 : ℝ)) with hc
  have hcm : Measurable c := measurable_const.indicator hN'm
  have hcae : ∀ᵐ r ∂(volume : Measure ℝ), c r = 0 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN'0] with r hr
    simp [hc, hr]
  have hS : ∀ j : ℕ, volume ({x : Vec (n + 1) | 1 / ((j : ℝ) + 1) < ‖x‖ ∧ ‖x‖ < (j : ℝ) + 1} ∩ P)
      = 0 := by
    intro j
    set S : Set (Vec (n + 1)) := {x | 1 / ((j : ℝ) + 1) < ‖x‖ ∧ ‖x‖ < (j : ℝ) + 1} with hSdef
    have hSm : MeasurableSet S :=
      (measurableSet_lt measurable_const measurable_norm).inter
        (measurableSet_lt measurable_norm measurable_const)
    have hρ : 0 < 1 / ((j : ℝ) + 1) := by positivity
    have hSsub : S ⊆ Metric.ball (0 : Vec (n + 1)) ((j : ℝ) + 1) := fun x hx => by
      rw [Metric.mem_ball, dist_zero_right]; exact hx.2
    have hSfin : volume S ≠ ⊤ :=
      ne_top_of_le_ne_top (Metric.isBounded_ball.measure_lt_top.ne) (measure_mono hSsub)
    set f : Vec (n + 1) → ℝ := fun x => (fun _ : Vec (n + 1) => (1 : ℝ)) x * c ‖x‖ with hf
    have hfm : Measurable f := measurable_const.mul (hcm.comp measurable_norm)
    have hfint : IntegrableOn f S := by
      refine Measure.integrableOn_of_bounded (M := 1) hSfin hfm.aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall fun x => ?_
      simp only [hf, hc, one_mul, Real.norm_eq_abs]
      by_cases h : ‖x‖ ∈ N' <;> simp [h]
    have hint := integral_shell_eq_boundaryIntegral (n := n) hρ (σ := (j : ℝ) + 1) hfint
    have hI : ∫ r in Ioo (1 / ((j : ℝ) + 1)) ((j : ℝ) + 1),
        cubeBoundaryIntegral r f = 0 := by
      refine integral_eq_zero_of_ae ?_
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
      filter_upwards [hcae] with r hr hrI
      have hr0 : 0 ≤ r := by linarith [hrI.1]
      have := cubeBoundaryIntegral_mul_norm (n := n) hr0 (fun _ => (1 : ℝ)) c
      simp only [Pi.zero_apply]
      rw [show cubeBoundaryIntegral r f = _ from this, hr, mul_zero]
    have hzero : ∫ x in S, f x = 0 := by
      rw [hSdef]; rw [hint]; exact hI
    have hnn : ∀ x, 0 ≤ f x := fun x => by
      simp only [hf, hc, one_mul]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have hae := (integral_eq_zero_iff_of_nonneg hnn hfint).1 hzero
    rw [Filter.EventuallyEq, ae_restrict_iff' hSm] at hae
    refine measure_mono_null (fun x hx => ?_) (ae_iff.1 hae)
    simp only [mem_setOf_eq, not_imp, Pi.zero_apply]
    refine ⟨hx.1, ?_⟩
    have : c ‖x‖ = 1 := by simp [hc, show ‖x‖ ∈ N' from hx.2]
    simp [hf, this]
  have hsub : P ⊆ {x : Vec (n + 1) | ‖x - 0‖ = 0} ∪
      ⋃ j : ℕ, ({x : Vec (n + 1) | 1 / ((j : ℝ) + 1) < ‖x‖ ∧ ‖x‖ < (j : ℝ) + 1} ∩ P) := by
    intro x hx
    by_cases h0 : ‖x‖ = 0
    · exact Or.inl (by simpa using h0)
    · right
      have hpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      obtain ⟨j, hj⟩ := exists_nat_gt (max ‖x‖ (1 / ‖x‖))
      have hj1 : ‖x‖ < j := lt_of_le_of_lt (le_max_left _ _) hj
      have hj2 : 1 / ‖x‖ < j := lt_of_le_of_lt (le_max_right _ _) hj
      refine mem_iUnion.2 ⟨j, ⟨⟨?_, by linarith⟩, hx⟩⟩
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hpos] at hj2
      nlinarith
  refine measure_mono_null hsub (measure_union_null (volume_supNorm_sphere (0 : Vec (n + 1)) 0)
    (measure_iUnion_null hS))

end PDE.BSlocalmax
end

-- ==== from ProfileE3.lean ====
-- Cutoff `η = φ(‖x‖_∞)` with `∫ g |∇η|² = 0` when the boundary integral vanishes on `E`.


@[expose] public section

open MeasureTheory Set Filter Topology PDE PDE.Ch4Infra

namespace PDE.BSlocalmax

variable {n : ℕ}

set_option maxHeartbeats 1600000 in
theorem exists_profile_cutoff {a σ : ℝ} (ha : 0 < a) (hσ : σ ≤ 1) {E : Set ℝ}
    (hE : MeasurableSet E) (hEs : E ⊆ Ioo a σ) (hpos : 0 < volume E)
    {g : Vec (n + 1) → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (hg : IntegrableOn g (Metric.ball (0 : Vec (n + 1)) 1))
    (hzero : ∀ r ∈ E, cubeBoundaryIntegral r g = 0) :
    ∃ (K : ℝ) (η : Vec (n + 1) → ℝ), 0 ≤ K ∧ EucLip K η ∧ (∀ x, η x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x, ‖x‖ ≤ a → η x = 1) ∧ (∀ x, σ ≤ ‖x‖ → η x = 0) ∧
      ∫ x in Metric.ball (0 : Vec (n + 1)) 1, g x * vecNormSq (classicalGradient η x) = 0 := by
  have hfin : volume E ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
      (measure_mono hEs)
  set m : ℝ := (volume E).toReal with hm
  have hm0 : 0 < m := ENNReal.toReal_pos hpos.ne' hfin
  set φ : ℝ → ℝ := fun r => 1 - Fprof E r / m with hφ
  have hφlip : LipschitzWith ⟨1 / m, by positivity⟩ φ := by
    refine LipschitzWith.of_dist_le_mul fun r s => ?_
    show dist (φ r) (φ s) ≤ 1 / m * dist r s
    have h1 := (Fprof_lipschitz hE hfin).dist_le_mul r s
    simp only [NNReal.coe_one, one_mul] at h1
    have e : dist (φ r) (φ s) = dist (Fprof E r) (Fprof E s) / m := by
      simp only [hφ, Real.dist_eq]
      rw [show 1 - Fprof E r / m - (1 - Fprof E s / m) = -(Fprof E r - Fprof E s) / m by ring,
        abs_div, abs_neg, abs_of_pos hm0]
    rw [e, div_eq_mul_inv, mul_comm, one_div]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hK0 : (0 : ℝ) ≤ 1 / m := by positivity
  have hη : EucLip (1 / m) (fun x : Vec (n + 1) => φ ‖x‖) :=
    eucLip_comp_norm (d := n + 1) hφlip
  have hF0 : ∀ r, r ≤ a → Fprof E r = 0 := fun r hr => by
    have : E ∩ Iic r = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_empty_iff_false, iff_false, not_and]
      intro hx hxr
      have := (hEs hx).1
      linarith
    simp [Fprof, this]
  have hFm : ∀ r, σ ≤ r → Fprof E r = m := fun r hr => by
    have : E ∩ Iic r = E := by
      ext x
      simp only [mem_inter_iff, mem_Iic, and_iff_left_iff_imp]
      intro hx
      have := (hEs hx).2
      linarith
    simp [Fprof, this, hm]
  refine ⟨1 / m, fun x => φ ‖x‖, hK0, hη, fun x => ?_, fun x hx => ?_, fun x hx => ?_, ?_⟩
  · have h1 := Fprof_nonneg E ‖x‖
    have h2 := Fprof_le_vol hfin ‖x‖
    refine ⟨?_, ?_⟩
    · simp only [hφ]
      have : Fprof E ‖x‖ / m ≤ 1 := by rw [div_le_one hm0]; exact h2
      linarith
    · simp only [hφ]
      have : 0 ≤ Fprof E ‖x‖ / m := by positivity
      linarith
  · simp [hφ, hF0 _ hx]
  · simp [hφ, hFm _ hx, hm0.ne']
  -- Main part
  set Nbad : Set ℝ := {r | ¬ (r ∉ E → HasDerivAt (Fprof E) 0 r)} with hNbad
  have hN0 : volume Nbad = 0 := ae_iff.1 (ae_hasDerivAt_Fprof hE hfin)
  have hshell_sub : {x : Vec (n + 1) | a < ‖x‖ ∧ ‖x‖ < σ} ⊆ Metric.ball (0 : Vec (n + 1)) 1 :=
    fun x hx => by
      rw [Metric.mem_ball, dist_zero_right]; exact lt_of_lt_of_le hx.2 hσ
  have hshell_m : MeasurableSet {x : Vec (n + 1) | a < ‖x‖ ∧ ‖x‖ < σ} :=
    (measurableSet_lt measurable_const measurable_norm).inter
      (measurableSet_lt measurable_norm measurable_const)
  set c : ℝ → ℝ := E.indicator (fun _ => (1 : ℝ)) with hc
  have hcm : Measurable c := measurable_const.indicator hE
  set f : Vec (n + 1) → ℝ := fun x => g x * c ‖x‖ with hf
  have hfint : IntegrableOn f {x : Vec (n + 1) | a < ‖x‖ ∧ ‖x‖ < σ} := by
    refine Integrable.mono' (hg.mono_set hshell_sub) ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (hg.mono_set hshell_sub).aestronglyMeasurable.mul
        (hcm.comp measurable_norm).aestronglyMeasurable
    · simp only [hf, hc, Real.norm_eq_abs]
      by_cases h : ‖x‖ ∈ E
      · simp [h, abs_of_nonneg (hg0 x)]
      · simp [h, hg0 x]
  have hintf := integral_shell_eq_boundaryIntegral (n := n) ha hfint
  have hzf : ∫ x in {x : Vec (n + 1) | a < ‖x‖ ∧ ‖x‖ < σ}, f x = 0 := by
    rw [hintf]
    refine setIntegral_eq_zero_of_forall_eq_zero (fun r hr => ?_)
    have hr0 : 0 ≤ r := by linarith [hr.1]
    have := cubeBoundaryIntegral_mul_norm (n := n) hr0 g c
    rw [show cubeBoundaryIntegral r f = _ from this]
    by_cases h : r ∈ E
    · rw [hzero r h, zero_mul]
    · simp [hc, h]
  have hfnn : ∀ x, 0 ≤ f x := fun x => mul_nonneg (hg0 x)
    (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  have hD := (integral_eq_zero_iff_of_nonneg hfnn hfint).1 hzf
  rw [Filter.EventuallyEq, ae_restrict_iff' hshell_m] at hD
  have hB : ∀ᵐ x ∂(volume : Measure (Vec (n + 1))), DifferentiableAt ℝ (fun y : Vec (n + 1) => ‖y‖) x := by
    have := (eucLip_supNorm_center (0 : Vec (n + 1))).ae_differentiableAt zero_le_one
    filter_upwards [this] with x hx
    simpa using hx
  have hC : ∀ᵐ x ∂(volume : Measure (Vec (n + 1))), ‖x‖ ∉ Nbad :=
    measure_eq_zero_iff_ae_notMem.1 (volume_preimage_norm_null (n := n) hN0)
  refine integral_eq_zero_of_ae (ae_restrict_of_ae ?_)
  filter_upwards [hB, hC, hD] with x hxB hxC hxD
  show g x * vecNormSq (classicalGradient (fun y : Vec (n + 1) => φ ‖y‖) x) = 0
  by_cases hr : ‖x‖ ∈ E
  · have hx : x ∈ {x : Vec (n + 1) | a < ‖x‖ ∧ ‖x‖ < σ} := ⟨(hEs hr).1, (hEs hr).2⟩
    have := hxD hx
    simp only [hf, hc, Pi.zero_apply, Set.indicator_of_mem hr, mul_one] at this
    simp [this]
  · have hgood : HasDerivAt (Fprof E) 0 ‖x‖ := by
      by_contra hcon
      exact hxC (fun h => absurd (h hr) hcon)
    have hφd : HasDerivAt φ 0 ‖x‖ := by
      have := (hgood.div_const m).const_sub 1
      simpa using this
    have hc' : HasFDerivAt (fun y : Vec (n + 1) => φ ‖y‖)
        ((0 : ℝ) • fderiv ℝ (fun y : Vec (n + 1) => ‖y‖) x) x :=
      hφd.comp_hasFDerivAt x hxB.hasFDerivAt
    have hgrad : classicalGradient (fun y : Vec (n + 1) => φ ‖y‖) x = 0 := by
      funext j
      rw [classicalGradient_apply, hc'.fderiv]
      simp
    rw [hgrad, vecNormSq_zero_vec, mul_zero]

end PDE.BSlocalmax
end

-- ==== from MaxPrinciple2A.lean ====
-- An `H¹` function on a cube with almost everywhere vanishing gradient is constant.


@[expose] public section

open MeasureTheory Set Filter PDE PDE.Ch4Infra

namespace PDE.BSlocalmax

theorem exists_const_of_grad_ae_zero {d : ℕ} {t : ℝ} (ht : 0 < t)
    (w : H1Function (Metric.ball (0 : Vec d) t))
    (hg : ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : Vec d) t)), w.grad x = 0) :
    ∃ c : ℝ, ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : Vec d) t)), w.toFun x = c := by
  have ht2 : (0 : ℝ) < 2 * t := by linarith
  have hV' : Metric.ball (0 : Vec d) t = axisCube (fun _ : Fin d => -t) (2 * t) :=
    (ball_zero_eq_pi_Ioo ht).trans (axisCube_eq_pi_Ioo t).symm
  have hVc := isOpenBoundedConvexDomain_axisCube (fun _ : Fin d => -t) (2 * t)
  have hne := axisCube_nonempty (fun _ : Fin d => -t) ht2
  have hD := hasEuclideanDiameterLE_axisCube (fun _ : Fin d => -t) ht2.le
  rw [← hV'] at hVc hne hD
  let v : H1Function (Metric.ball (0 : Vec d) t) :=
    { toFun := w.toFun
      grad := 0
      memL2 := w.memL2
      gradMemL2 := by
        intro i
        refine (w.gradMemL2 i).ae_eq ?_
        filter_upwards [hg] with x hx
        simp [hx]
      hasWeakGradient := by
        intro i
        rw [hasWeakPartialDerivOn_iff_forall_testFunction]
        intro φ
        have h := (hasWeakPartialDerivOn_iff_forall_testFunction.1 (w.hasWeakGradient i)) φ
        rw [h]
        congr 1
        refine integral_congr_ae ?_
        filter_upwards [hg] with x hx
        simp [hx] }
  have hv := H1Function.ae_eq_integralAverage_of_grad_eq_zero hVc hD (by positivity) hne v rfl
  exact ⟨_, hv⟩

end PDE.BSlocalmax
end

-- ==== from MaxPrinciple2B.lean ====
-- Splitting of `E`, and "a constant with trace 0 is 0".


@[expose] public section

open MeasureTheory Set Filter Topology PDE PDE.Ch4Infra

namespace PDE.BSlocalmax

variable {n : ℕ}

lemma exists_split {E : Set ℝ} {a σ : ℝ} (hE : MeasurableSet E) (hEs : E ⊆ Ioo a σ)
    (hpos : 0 < volume E) :
    ∃ s ∈ Ioo a σ, 0 < volume (E ∩ Ioo a s) ∧ 0 < volume (E ∩ Ioo s σ) := by
  have hfin : volume E ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
      (measure_mono hEs)
  set m : ℝ := (volume E).toReal with hm
  have hm0 : 0 < m := ENNReal.toReal_pos hpos.ne' hfin
  have hcont : Continuous (Fprof E) := (Fprof_lipschitz hE hfin).continuous
  have hF0 : ∀ r, r ≤ a → Fprof E r = 0 := fun r hr => by
    have : E ∩ Iic r = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_empty_iff_false, iff_false, not_and]
      intro hx hxr
      have := (hEs hx).1
      linarith
    simp [Fprof, this]
  have hFm : ∀ r, σ ≤ r → Fprof E r = m := fun r hr => by
    have : E ∩ Iic r = E := by
      ext x
      simp only [mem_inter_iff, mem_Iic, and_iff_left_iff_imp]
      intro hx
      have := (hEs hx).2
      linarith
    simp [Fprof, this, hm]
  obtain ⟨x0, hx0⟩ := nonempty_of_measure_ne_zero hpos.ne'
  have haσ : a ≤ σ := by
    have := hEs hx0
    linarith [this.1, this.2]
  obtain ⟨s, hs, hsv⟩ := intermediate_value_Icc haσ hcont.continuousOn
    (show m / 2 ∈ Icc (Fprof E a) (Fprof E σ) by
      rw [hF0 a le_rfl, hFm σ le_rfl]; constructor <;> linarith)
  have hsa : a < s := by
    rcases hs.1.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h, hF0 a le_rfl] at hsv; linarith
  have hsσ : s < σ := by
    rcases hs.2.lt_or_eq with h | h
    · exact h
    · exfalso; rw [h, hFm σ le_rfl] at hsv; linarith
  refine ⟨s, ⟨hsa, hsσ⟩, ?_, ?_⟩
  · by_contra h
    have h0 : volume (E ∩ Ioo a s) = 0 := le_antisymm (not_lt.1 h) bot_le
    have hsub : E ∩ Iic s ⊆ (E ∩ Ioo a s) ∪ {s} := by
      rintro x ⟨hx, hxs⟩
      rcases (mem_Iic.1 hxs).lt_or_eq with h' | h'
      · exact Or.inl ⟨hx, (hEs hx).1, h'⟩
      · exact Or.inr h'
    have h00 : volume (E ∩ Iic s) = 0 :=
      measure_mono_null hsub (measure_union_null h0 Real.volume_singleton)
    have : Fprof E s = 0 := by simp [Fprof, h00]
    linarith
  · by_contra h
    have h0 : volume (E ∩ Ioo s σ) = 0 := le_antisymm (not_lt.1 h) bot_le
    have hsub : E ⊆ (E ∩ Iic s) ∪ (E ∩ Ioo s σ) := by
      intro x hx
      by_cases hxs : x ≤ s
      · exact Or.inl ⟨hx, hxs⟩
      · exact Or.inr ⟨hx, not_le.1 hxs, (hEs hx).2⟩
    have hle : volume E ≤ volume (E ∩ Iic s) :=
      (measure_mono hsub).trans ((measure_union_le _ _).trans (by rw [h0, add_zero]))
    have hfin2 : volume (E ∩ Iic s) ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono inter_subset_left)
    have := ENNReal.toReal_mono hfin2 hle
    have e : Fprof E s = (volume (E ∩ Iic s)).toReal := rfl
    linarith

lemma cBI_one {r : ℝ} (hr : 0 ≤ r) :
    cubeBoundaryIntegral (n := n) r (fun _ => (1 : ℝ)) = 2 * ((n : ℝ) + 1) * (2 * r) ^ n := by
  have h1 := cubeBoundaryIntegral_lin (n := n) (f := fun _ : Vec (n + 1) => (0 : ℝ))
    continuous_const hr 0 1
  simp only [zero_mul, zero_add, mul_one, mul_zero] at h1
  rw [h1]

lemma const_zero_of_trace {a s : ℝ} (ha : 0 < a) (has : a < s) {E1 : Set ℝ}
    (hE1 : MeasurableSet E1) (hE1s : E1 ⊆ Ioo a s) (hpos : 0 < volume E1)
    {w : Vec (n + 1) → ℝ} {c : ℝ}
    (hwc : ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : Vec (n + 1)) s)), w x = c)
    (hw2 : IntegrableOn (fun x => w x ^ 2) (Metric.ball (0 : Vec (n + 1)) s))
    (hzero : ∀ r ∈ E1, cubeBoundaryIntegral r (fun x => w x ^ 2) = 0) : c = 0 := by
  set S : Set (Vec (n + 1)) := {x | a < ‖x‖ ∧ ‖x‖ < s} with hS
  have hSsub : S ⊆ Metric.ball (0 : Vec (n + 1)) s := fun x hx => by
    simpa using hx.2
  have hSmeas : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_norm).inter
      (measurableSet_lt measurable_norm measurable_const)
  set ind : ℝ → ℝ := E1.indicator (fun _ => (1 : ℝ)) with hind
  have hind_meas : Measurable ind := measurable_const.indicator hE1
  have hind01 : ∀ r, |ind r| ≤ 1 := fun r => by
    by_cases h : r ∈ E1 <;> simp [hind, h]
  -- A
  have hf1int : IntegrableOn (fun x : Vec (n + 1) => w x ^ 2 * ind ‖x‖) S := by
    refine Integrable.mono' (hw2.mono_set hSsub) ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (hw2.mono_set hSsub).aestronglyMeasurable.mul
        (hind_meas.comp measurable_norm).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul]
      calc |w x ^ 2| * |ind ‖x‖| ≤ |w x ^ 2| * 1 :=
            mul_le_mul_of_nonneg_left (hind01 _) (abs_nonneg _)
        _ = w x ^ 2 := by rw [mul_one, abs_of_nonneg (sq_nonneg _)]
  have hA : ∫ x in S, w x ^ 2 * ind ‖x‖ = 0 := by
    rw [hS, integral_shell_eq_boundaryIntegral ha hf1int]
    refine setIntegral_eq_zero_of_forall_eq_zero fun r hr => ?_
    have hr0 : 0 ≤ r := by linarith [hr.1]
    rw [cubeBoundaryIntegral_mul_norm hr0 (fun x => w x ^ 2) ind]
    by_cases h : r ∈ E1
    · rw [hzero r h]; ring
    · simp [hind, h]
  -- B
  have hB : ∫ x in S, w x ^ 2 * ind ‖x‖ = c ^ 2 * ∫ x in S, ind ‖x‖ := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    have := ae_restrict_of_ae_restrict_of_subset hSsub hwc
    filter_upwards [this] with x hx
    rw [hx]
  -- C
  have hCint : IntegrableOn (fun x : Vec (n + 1) => ind ‖x‖) S := by
    refine Integrable.mono' (g := fun _ => (1 : ℝ)) ?_ ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact integrableOn_const (measure_mono hSsub |>.trans_lt
        Metric.isBounded_ball.measure_lt_top |>.ne)
    · exact (hind_meas.comp measurable_norm).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact hind01 _
  have hC : ∫ x in S, ind ‖x‖ = ∫ r in Ioo a s, (2 * ((n : ℝ) + 1) * (2 * r) ^ n) * ind r := by
    have := integral_shell_eq_boundaryIntegral (n := n) ha (σ := s)
      (f := fun x : Vec (n + 1) => ind ‖x‖) hCint
    rw [hS, this]
    refine setIntegral_congr_fun measurableSet_Ioo fun r hr => ?_
    have hr0 : 0 ≤ r := by linarith [hr.1]
    have h := cubeBoundaryIntegral_mul_norm (n := n) hr0 (fun _ => (1 : ℝ)) ind
    simp only [one_mul] at h
    rw [h, cBI_one hr0]
  have hCpos : 0 < ∫ x in S, ind ‖x‖ := by
    rw [hC]
    set F : ℝ → ℝ := fun r => 2 * ((n : ℝ) + 1) * (2 * r) ^ n with hF
    have hFc : Continuous F := by simp only [hF]; fun_prop
    have hrw : ∫ r in Ioo a s, F r * ind r = ∫ r in E1, F r := by
      have h1 : ∀ r, F r * ind r = E1.indicator F r := fun r => by
        by_cases h : r ∈ E1 <;> simp [hind, h]
      simp_rw [h1]
      rw [setIntegral_indicator hE1, inter_eq_right.2 hE1s]
    rw [hrw]
    have hfinE : volume E1 ≠ ⊤ :=
      ne_top_of_le_ne_top (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
        (measure_mono hE1s)
    have hE1Icc : E1 ⊆ Icc a s := hE1s.trans Ioo_subset_Icc_self
    have hFi : IntegrableOn F E1 := (hFc.integrableOn_Icc (a := a) (b := s)).mono_set hE1Icc
    have hF0 : (0 : ℝ) < 2 * ((n : ℝ) + 1) * (2 * a) ^ n := by positivity
    have hci : IntegrableOn (fun _ : ℝ => 2 * ((n : ℝ) + 1) * (2 * a) ^ n) E1 :=
      integrableOn_const hfinE
    have hmono : ∫ r in E1, 2 * ((n : ℝ) + 1) * (2 * a) ^ n ≤ ∫ r in E1, F r := by
      refine setIntegral_mono_on hci hFi hE1 fun r hr => ?_
      have hra : a ≤ r := (hE1s hr).1.le
      simp only [hF]
      have : (2 * a) ^ n ≤ (2 * r) ^ n :=
        pow_le_pow_left₀ (by linarith) (by linarith) n
      have hn : (0 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by positivity
      exact mul_le_mul_of_nonneg_left this hn
    have hlow : 0 < ∫ r in E1, 2 * ((n : ℝ) + 1) * (2 * a) ^ n := by
      rw [setIntegral_const, smul_eq_mul]
      have : 0 < volume.real E1 := ENNReal.toReal_pos hpos.ne' hfinE
      positivity
    exact lt_of_lt_of_le hlow hmono
  have hc2 : c ^ 2 * ∫ x in S, ind ‖x‖ = 0 := by rw [← hB]; exact hA
  have : c ^ 2 = 0 := by
    rcases mul_eq_zero.1 hc2 with h | h
    · exact h
    · exact absurd h hCpos.ne'
  exact pow_eq_zero_iff (by norm_num) |>.1 this

end PDE.BSlocalmax
end

-- ==== from MaxPrinciple2.lean ====
-- Trace-free maximum principle (d = 2 route): if the trace of `(u-k)₊` vanishes on a
-- set `E` of good radii of positive measure, then `(u-k)₊ = 0` almost everywhere on `Q_a`.


@[expose] public section

open MeasureTheory Set Filter Topology PDE PDE.Ch4Infra

namespace PDE.BSlocalmax

variable {n : ℕ}

set_option maxHeartbeats 1600000 in
theorem maxPrinciple_trace {Λ a σ k : ℝ} {coeff : CoeffField (n + 1)} (ha0 : 0 < a) (hσ : σ < 1)
    (hco : ∀ i j, AEMeasurable (fun x => coeff x i j)
      (volumeOn (Metric.ball (0 : Vec (n + 1)) 1)))
    (hEll : ∀ x ∈ Metric.ball (0 : Vec (n + 1)) 1, IsEllipticMatrix 1 Λ (coeff x))
    {u : H1Function (Metric.ball (0 : Vec (n + 1)) 1)}
    (hsub : IsWeakDivergenceFormSubharmonicOn coeff (Metric.ball (0 : Vec (n + 1)) 1) u)
    {E : Set ℝ} (hE : MeasurableSet E) (hEs : E ⊆ Ioo a σ) (hpos : 0 < volume E)
    (hzero : ∀ r ∈ E, cubeBoundaryIntegral r (fun x => (max (u.toFun x - k) 0) ^ 2) = 0) :
    ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : Vec (n + 1)) a)), max (u.toFun x - k) 0 = 0 := by
  obtain ⟨s, hs, hE1, hE2⟩ := exists_split hE hEs hpos
  have hfin : volume (Metric.ball (0 : Vec (n + 1)) 1) ≠ ⊤ :=
    Metric.isBounded_ball.measure_lt_top.ne
  have hwL2 : MemL2On (Metric.ball (0 : Vec (n + 1)) 1) (fun x => max (u.toFun x - k) 0) :=
    memL2On_positivePart_of_finite u hfin k
  have hg : IntegrableOn (fun x => (max (u.toFun x - k) 0) ^ 2)
      (Metric.ball (0 : Vec (n + 1)) 1) := by
    simpa only [pow_two] using integrableOn_mul_of_memL2On hwL2 hwL2
  have hs0 : 0 < s := ha0.trans hs.1
  -- Cutoff with derivative only on `E ∩ (s, σ)`
  obtain ⟨K, η, hK0, hη, h01, h1, h0, hint⟩ := exists_profile_cutoff (n := n) hs0 hσ.le
    (E := E ∩ Ioo s σ) (hE.inter measurableSet_Ioo) inter_subset_right hE2
    (g := fun x => (max (u.toFun x - k) 0) ^ 2) (fun x => sq_nonneg _) hg
    (fun r hr => hzero r hr.1)
  have hcacc := caccioppoli_cube (k := k) (Λ := Λ) hs.2 hσ hs0.le hco hEll hsub hη hK0 h01 h1 h0
  rw [hint, mul_zero] at hcacc
  have hs1 : s < 1 := hs.2.trans hσ
  have hsub1 : Metric.ball (0 : Vec (n + 1)) s ⊆ Metric.ball 0 1 := Metric.ball_subset_ball hs1.le
  have hξ : MemVectorL2On (Metric.ball (0 : Vec (n + 1)) 1)
      (fun x => {y | k < u.toFun y}.indicator u.grad x) := posPartGrad_gradMemL2 u k
  have hξint := (integrableOn_vecNormSq_of_memVectorL2On hξ).mono_set hsub1
  have hnn : ∀ x : Vec (n + 1), 0 ≤ vecNormSq ({y | k < u.toFun y}.indicator u.grad x) :=
    fun x => vecNormSq_nonneg _
  have h0' : ∫ x in Metric.ball (0 : Vec (n + 1)) s,
      vecNormSq ({y | k < u.toFun y}.indicator u.grad x) = 0 :=
    le_antisymm hcacc (integral_nonneg hnn)
  have hae := (integral_eq_zero_iff_of_nonneg hnn hξint).1 h0'
  -- H¹ function on Q_s
  have hconv : IsOpenBoundedConvexDomain (Metric.ball (0 : Vec (n + 1)) s) := by
    have ht2 : (0 : ℝ) < 2 * s := by linarith
    have hV' : Metric.ball (0 : Vec (n + 1)) s = axisCube (fun _ : Fin (n + 1) => -s) (2 * s) :=
      (ball_zero_eq_pi_Ioo hs0).trans (axisCube_eq_pi_Ioo s).symm
    rw [hV']
    exact isOpenBoundedConvexDomain_axisCube _ _
  set w : H1Function (Metric.ball (0 : Vec (n + 1)) s) :=
    (u.restrict Metric.isOpen_ball hsub1).positivePartSubConst hconv k with hw
  have hwgrad : ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : Vec (n + 1)) s)), w.grad x = 0 := by
    filter_upwards [hae] with x hx
    have hx' : vecNormSq ({y | k < u.toFun y}.indicator u.grad x) = 0 := hx
    have := vecNormSq_eq_zero hx'
    simpa [hw, H1Function.positivePartSubConst_grad, H1Function.restrict_grad,
      H1Function.restrict_toFun] using this
  obtain ⟨c, hc⟩ := exists_const_of_grad_ae_zero hs0 w hwgrad
  have hwfun : w.toFun = fun x => max (u.toFun x - k) 0 := rfl
  rw [hwfun] at hc
  have hc0 : c = 0 := by
    refine const_zero_of_trace ha0 hs.1 (E1 := E ∩ Ioo a s) (hE.inter measurableSet_Ioo)
      inter_subset_right hE1 (w := fun x => max (u.toFun x - k) 0) hc
      (hg.mono_set hsub1) (fun r hr => hzero r hr.1)
  subst hc0
  exact ae_restrict_of_ae_restrict_of_subset (Metric.ball_subset_ball hs.1.le) hc

end PDE.BSlocalmax
end

-- ==== from AEFace.lean ====
-- Almost every face section of an integrable function on a cube shell is integrable.
-- (Complement to `integral_face`: needed to avoid junk values of the Bochner integral.)


@[expose] public section

open MeasureTheory Set Filter

namespace PDE.BSlocalmax

variable {n : ℕ}

/-- For `f` integrable on the shell, the section of `f` on the face `{x i = s r}` is integrable
over `[-r,r]^n` for almost every `r ∈ (ρ, σ)`. -/
theorem ae_integrableOn_face {ρ σ : ℝ} (hρ : 0 < ρ) (i : Fin (n + 1)) {s : ℝ} (hs : |s| = 1)
    {f : Vec (n + 1) → ℝ} (hf : IntegrableOn f {x | ρ < ‖x‖ ∧ ‖x‖ < σ}) :
    ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioo ρ σ →
      IntegrableOn (fun y : Fin n → ℝ => f (Fin.insertNth i (s * r) y))
        (Set.pi Set.univ (fun _ : Fin n => Icc (-r) r)) := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  have hss : s * s = 1 := by rw [← abs_mul_abs_self, hs]; norm_num
  let e : ℝ × (Fin n → ℝ) ≃ᵐ Vec (n + 1) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
  have hem : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm _
  have he_apply : ∀ p : ℝ × (Fin n → ℝ), e p = Fin.insertNth i p.1 p.2 := fun p => by
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  set R : Set (Vec (n + 1)) := {x | ρ < ‖x‖ ∧ ‖x‖ < σ ∧ s * x i = ‖x‖} with hR
  have hRm : MeasurableSet R := measurableSet_face i s ρ σ
  set T : Set (ℝ × (Fin n → ℝ)) := e ⁻¹' R with hT
  have hTm : MeasurableSet T := e.measurable hRm
  have hTmem : ∀ a y, (a, y) ∈ T ↔ (s * a ∈ Ioo ρ σ ∧ ∀ j, |y j| ≤ s * a) := by
    intro a y
    rw [hT, mem_preimage, he_apply]
    exact mem_face_iff i hs hρ a y
  set g : ℝ × (Fin n → ℝ) → ℝ := fun p => f (e p) with hg
  have hgint : IntegrableOn g T := by
    have h1 : IntegrableOn f R := hf.mono_set (fun x hx => ⟨hx.1, hx.2.1⟩)
    exact (hem.integrableOn_comp_preimage e.measurableEmbedding).2 h1
  have hint : Integrable (T.indicator g) (volume.prod volume) := by
    have := (integrable_indicator_iff hTm).2 hgint
    rwa [Measure.volume_eq_prod] at this
  have hae : ∀ᵐ a ∂(volume : Measure ℝ), Integrable (fun y => T.indicator g (a, y)) :=
    hint.prod_right_ae
  -- the statement for the parameter `a`, with `r = s * a`
  set Q : ℝ → Prop := fun r => r ∈ Ioo ρ σ →
      IntegrableOn (fun y : Fin n → ℝ => f (Fin.insertNth i (s * r) y))
        (Set.pi Set.univ (fun _ : Fin n => Icc (-r) r)) with hQ
  have hQa : ∀ᵐ a ∂(volume : Measure ℝ), Q (s * a) := by
    filter_upwards [hae] with a ha hsa
    have hsa' : s * (s * a) = a := by rw [← mul_assoc, hss, one_mul]
    have hcube : MeasurableSet
        (Set.pi Set.univ (fun _ : Fin n => Icc (-(s * a)) (s * a))) :=
      MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
    have hset : ∀ y, T.indicator g (a, y) =
        (Set.pi Set.univ (fun _ : Fin n => Icc (-(s * a)) (s * a))).indicator
          (fun y => f (Fin.insertNth i (s * (s * a)) y)) y := by
      intro y
      have hy : (a, y) ∈ T ↔ y ∈ Set.pi Set.univ (fun _ : Fin n => Icc (-(s * a)) (s * a)) := by
        rw [hTmem, mem_univ_pi]
        exact ⟨fun ⟨_, h⟩ j => abs_le.1 (h j), fun h => ⟨hsa, fun j => abs_le.2 (h j)⟩⟩
      by_cases hy' : y ∈ Set.pi Set.univ (fun _ : Fin n => Icc (-(s * a)) (s * a))
      · rw [indicator_of_mem (hy.2 hy'), indicator_of_mem hy']
        simp only [hg, he_apply, hsa']
      · rw [indicator_of_notMem (fun h => hy' (hy.1 h)), indicator_of_notMem hy']
    have h2 : Integrable ((Set.pi Set.univ (fun _ : Fin n => Icc (-(s * a)) (s * a))).indicator
          (fun y => f (Fin.insertNth i (s * (s * a)) y))) := by
      refine ha.congr (Filter.Eventually.of_forall (fun y => ?_))
      exact hset y
    have h3 := (integrable_indicator_iff hcube).1 h2
    simpa only [hsa'] using h3
  -- transfer from `a` to `r = s * a`
  have hnull : volume {a : ℝ | ¬ Q (s * a)} = 0 := ae_iff.1 hQa
  have hpre : {r : ℝ | ¬ Q r} = (fun a => s * a) ⁻¹' {a : ℝ | ¬ Q (s * a)} := by
    ext r
    simp only [mem_setOf_eq, mem_preimage]
    rw [show s * (s * r) = r by rw [← mul_assoc, hss, one_mul]]
  have : volume {r : ℝ | ¬ Q r} = 0 := by
    rw [hpre, Real.volume_preimage_mul_left hs0, hnull, mul_zero]
  exact ae_iff.2 this

end PDE.BSlocalmax
end

-- ==== from FaceInt.lean ====
-- Face integrability and comparison of boundary integrals on cube boundaries.


@[expose] public section

open MeasureTheory Set Filter PDE

namespace PDE.BSlocalmax

variable {n : ℕ}

/-- All face sections of `F` at radius `r` are integrable over the face cube `[-r,r]^n`. -/
def FaceInt (n : ℕ) (r : ℝ) (F : Vec (n + 1) → ℝ) : Prop :=
  ∀ i : Fin (n + 1), ∀ s ∈ ({-1, 1} : Finset ℝ),
    IntegrableOn (fun y : Fin n → ℝ => F (Fin.insertNth i (s * r) y))
      (Set.pi Set.univ (fun _ : Fin n => Icc (-r) r))

theorem ae_faceInt {ρ σ : ℝ} (hρ : 0 < ρ) {F : Vec (n + 1) → ℝ}
    (hF : IntegrableOn F {x | ρ < ‖x‖ ∧ ‖x‖ < σ}) :
    ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioo ρ σ → FaceInt n r F := by
  have h1 : ∀ᵐ r ∂(volume : Measure ℝ), ∀ i : Fin (n + 1), r ∈ Ioo ρ σ →
      IntegrableOn (fun y : Fin n → ℝ => F (Fin.insertNth i ((1 : ℝ) * r) y))
        (Set.pi Set.univ (fun _ : Fin n => Icc (-r) r)) :=
    ae_all_iff.2 (fun i => ae_integrableOn_face hρ i (s := 1) (by norm_num) hF)
  have h2 : ∀ᵐ r ∂(volume : Measure ℝ), ∀ i : Fin (n + 1), r ∈ Ioo ρ σ →
      IntegrableOn (fun y : Fin n → ℝ => F (Fin.insertNth i ((-1 : ℝ) * r) y))
        (Set.pi Set.univ (fun _ : Fin n => Icc (-r) r)) :=
    ae_all_iff.2 (fun i => ae_integrableOn_face hρ i (s := -1) (by norm_num) hF)
  filter_upwards [h1, h2] with r hr1 hr2 hr i s hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl
  · exact hr2 i hr
  · exact hr1 i hr

lemma faceInt_of_continuous {F : Vec (n + 1) → ℝ} (hF : Continuous F) (r : ℝ) :
    FaceInt n r F := by
  intro i s _
  have hcubec : IsCompact (Set.pi Set.univ (fun _ : Fin n => Icc (-r) r)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  exact (hF.comp (Continuous.finInsertNth i continuous_const continuous_id)).continuousOn.integrableOn_compact
    hcubec

lemma faceIntegral_nonneg' {F : Vec (n + 1) → ℝ} (hF : ∀ x, 0 ≤ F x) (i : Fin (n + 1))
    (s r : ℝ) : 0 ≤ faceIntegral i s r F :=
  integral_nonneg (fun _ => hF _)

lemma faceIntegral_le_comb {f g1 g2 : Vec (n + 1) → ℝ} {c1 c2 : ℝ} (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hf0 : ∀ x, 0 ≤ f x) (hfg : ∀ x, f x ≤ c1 * g1 x + c2 * g2 x) {i : Fin (n + 1)} {s r : ℝ}
    (h1 : IntegrableOn (fun y : Fin n → ℝ => g1 (Fin.insertNth i (s * r) y))
      (Set.pi Set.univ (fun _ : Fin n => Icc (-r) r)))
    (h2 : IntegrableOn (fun y : Fin n → ℝ => g2 (Fin.insertNth i (s * r) y))
      (Set.pi Set.univ (fun _ : Fin n => Icc (-r) r))) :
    faceIntegral i s r f ≤ c1 * faceIntegral i s r g1 + c2 * faceIntegral i s r g2 := by
  unfold faceIntegral
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (h1.const_mul c1) (h2.const_mul c2)]
  exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => hf0 _)
    ((h1.const_mul c1).add (h2.const_mul c2)) (Filter.Eventually.of_forall fun y => hfg _)

lemma cubeBoundaryIntegral_le_comb {f g1 g2 : Vec (n + 1) → ℝ} {c1 c2 r : ℝ} (hc1 : 0 ≤ c1)
    (hc2 : 0 ≤ c2) (hf0 : ∀ x, 0 ≤ f x) (hfg : ∀ x, f x ≤ c1 * g1 x + c2 * g2 x)
    (h1 : FaceInt n r g1) (h2 : FaceInt n r g2) :
    cubeBoundaryIntegral r f ≤ c1 * cubeBoundaryIntegral r g1 + c2 * cubeBoundaryIntegral r g2 := by
  unfold cubeBoundaryIntegral
  calc ∑ i : Fin (n + 1), ∑ s ∈ ({-1, 1} : Finset ℝ), faceIntegral i s r f
      ≤ ∑ i : Fin (n + 1), ∑ s ∈ ({-1, 1} : Finset ℝ),
          (c1 * faceIntegral i s r g1 + c2 * faceIntegral i s r g2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun s hs =>
          faceIntegral_le_comb hc1 hc2 hf0 hfg (h1 i s hs) (h2 i s hs)
    _ = c1 * ∑ i : Fin (n + 1), ∑ s ∈ ({-1, 1} : Finset ℝ), faceIntegral i s r g1 +
        c2 * ∑ i : Fin (n + 1), ∑ s ∈ ({-1, 1} : Finset ℝ), faceIntegral i s r g2 := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]

lemma sq_add_le_three (a b : ℝ) : (a + b) ^ 2 ≤ 3 / 2 * a ^ 2 + 3 * b ^ 2 := by
  nlinarith [sq_nonneg (a - 2 * b)]

lemma vecNormSq_add_le' {d : ℕ} (x y : Vec d) :
    vecNormSq (x + y) ≤ 3 / 2 * vecNormSq x + 3 * vecNormSq y := by
  unfold vecNormSq vecDot
  simp only [Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  nlinarith [sq_nonneg (x i - 2 * y i)]

end PDE.BSlocalmax
end

-- ==== from Face1D.lean ====
-- One-dimensional interpolation on the faces of a square (the case `d = 2`, `n = 1`):
--   `f(y)² ≤ (1/ℓ + λ) ∫ f² + λ⁻¹ ∫ f'²`  on an interval of length `ℓ`,
-- and the resulting criterion for `(w - k)₊` to vanish on the boundary of a square.


@[expose] public section

open MeasureTheory Set PDE

namespace PDE.BSlocalmax

/-- 1D interpolation inequality: for `C¹` `f` on `[a,b]`, every `λ > 0` and every `y ∈ [a,b]`,
`f(y)² ≤ ((b-a)⁻¹ + λ) ∫ f² + λ⁻¹ ∫ f'²`. -/
lemma sq_le_of_c1 {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {a b : ℝ} (hab : a < b) {l : ℝ}
    (hl : 0 < l) {y : ℝ} (hy : y ∈ Icc a b) :
    f y ^ 2 ≤ ((b - a)⁻¹ + l) * (∫ t in a..b, f t ^ 2) +
      l⁻¹ * (∫ t in a..b, (deriv f t) ^ 2) := by
  have hd : ∀ x, HasDerivAt f (deriv f x) x := fun x =>
    ((hf.differentiable (by norm_num)) x).hasDerivAt
  have hcf : Continuous f := hf.continuous
  have hcd : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have hfi : IntervalIntegrable (fun t => f t ^ 2) volume a b :=
    (hcf.pow 2).intervalIntegrable _ _
  have hdi : IntervalIntegrable (fun t => (deriv f t) ^ 2) volume a b :=
    (hcd.pow 2).intervalIntegrable _ _
  set A := ∫ t in a..b, f t ^ 2 with hA
  set D := ∫ t in a..b, (deriv f t) ^ 2 with hD
  set H : ℝ → ℝ := fun t => l * f t ^ 2 + l⁻¹ * (deriv f t) ^ 2 with hH
  have hHc : Continuous H := by
    simp only [hH]
    exact (continuous_const.mul (hcf.pow 2)).add (continuous_const.mul (hcd.pow 2))
  have hHi : IntervalIntegrable H volume a b := hHc.intervalIntegrable _ _
  have hHint : ∫ t in a..b, H t = l * A + l⁻¹ * D := by
    simp only [hH]
    rw [intervalIntegral.integral_add (hfi.const_mul l) (hdi.const_mul l⁻¹),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hHnn : ∀ t, 0 ≤ H t := fun t => by
    simp only [hH]; positivity
  -- pointwise bound `|2 f f'| ≤ H`
  have hpt : ∀ t, |2 * f t * deriv f t| ≤ H t := by
    intro t
    set p := f t
    set q := deriv f t
    have e1 : l⁻¹ * (l * p - q) ^ 2 = l * p ^ 2 - 2 * p * q + l⁻¹ * q ^ 2 := by
      field_simp; ring
    have e2 : l⁻¹ * (l * p + q) ^ 2 = l * p ^ 2 + 2 * p * q + l⁻¹ * q ^ 2 := by
      field_simp; ring
    have h1 : 0 ≤ l⁻¹ * (l * p - q) ^ 2 := by positivity
    have h2 : 0 ≤ l⁻¹ * (l * p + q) ^ 2 := by positivity
    rw [abs_le]
    simp only [hH]
    constructor <;> nlinarith
  have hsq : ∀ t, HasDerivAt (fun t => f t ^ 2) (2 * f t * deriv f t) t := fun t => by
    convert (hd t).mul (hd t) using 1
    · funext x; simp [sq]
    · ring
  have hdiffc : Continuous (fun t => 2 * f t * deriv f t) := by
    exact (continuous_const.mul hcf).mul hcd
  have hdiffi : IntervalIntegrable (fun t => 2 * f t * deriv f t) volume a b :=
    hdiffc.intervalIntegrable _ _
  -- the increment estimate
  have key : ∀ x z, a ≤ x → x ≤ z → z ≤ b → |f z ^ 2 - f x ^ 2| ≤ l * A + l⁻¹ * D := by
    intro x z hax hxz hzb
    have hftc : ∫ t in x..z, 2 * f t * deriv f t = f z ^ 2 - f x ^ 2 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hsq t)
        (hdiffc.intervalIntegrable _ _)
    rw [← hftc]
    calc |∫ t in x..z, 2 * f t * deriv f t|
        ≤ ∫ t in x..z, |2 * f t * deriv f t| :=
          intervalIntegral.abs_integral_le_integral_abs hxz
      _ ≤ ∫ t in x..z, H t :=
          intervalIntegral.integral_mono_on hxz (hdiffc.abs.intervalIntegrable _ _)
            (hHc.intervalIntegrable _ _) (fun t _ => hpt t)
      _ ≤ ∫ t in a..b, H t :=
          intervalIntegral.integral_mono_interval hax hxz hzb
            (Filter.Eventually.of_forall hHnn) hHi
      _ = l * A + l⁻¹ * D := hHint
  have hbound : ∀ x ∈ Icc a b, f y ^ 2 ≤ f x ^ 2 + (l * A + l⁻¹ * D) := by
    intro x hx
    rcases le_total x y with hxy | hyx
    · have := key x y hx.1 hxy hy.2
      have := (abs_le.1 this).2
      linarith
    · have := key y x hy.1 hyx hx.2
      have := (abs_le.1 this).1
      linarith
  have hint1 : ∫ x in a..b, f y ^ 2 ≤ ∫ x in a..b, (f x ^ 2 + (l * A + l⁻¹ * D)) :=
    intervalIntegral.integral_mono_on hab.le intervalIntegrable_const
      (hfi.add intervalIntegrable_const) hbound
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add hfi intervalIntegrable_const,
    intervalIntegral.integral_const] at hint1
  simp only [smul_eq_mul] at hint1
  have hba : 0 < b - a := sub_pos.2 hab
  have : f y ^ 2 ≤ (b - a)⁻¹ * A + (l * A + l⁻¹ * D) := by
    have h2 : (b - a) * f y ^ 2 ≤ A + (b - a) * (l * A + l⁻¹ * D) := hint1
    have h3 : f y ^ 2 ≤ (A + (b - a) * (l * A + l⁻¹ * D)) / (b - a) :=
      (le_div_iff₀ hba).2 (by linarith)
    calc f y ^ 2 ≤ _ := h3
      _ = (b - a)⁻¹ * A + (l * A + l⁻¹ * D) := by field_simp
  calc f y ^ 2 ≤ (b - a)⁻¹ * A + (l * A + l⁻¹ * D) := this
    _ = ((b - a)⁻¹ + l) * A + l⁻¹ * D := by ring
    _ = ((b - a)⁻¹ + l) * (∫ t in a..b, f t ^ 2) + l⁻¹ * (∫ t in a..b, (deriv f t) ^ 2) := rfl

/-- The face `{x i = s r}` of the square, parametrised by `t ↦ s r e_i + t e_j`. -/
lemma faceIntegral_one (i : Fin 2) (s r : ℝ) (hr : 0 ≤ r) (f : Vec 2 → ℝ) :
    faceIntegral (n := 1) i s r f =
      ∫ t in (-r)..r, f ((s * r) • basisVec i + t • basisVec (i.succAbove 0)) := by
  unfold faceIntegral
  have e1 : ∀ y : Fin 1 → ℝ, (Fin.insertNth i (s * r) y : Vec 2) =
      (s * r) • basisVec i + (y 0) • basisVec (i.succAbove 0) := by
    intro y
    rw [insertNth_eq_sum]
    simp [Fin.sum_univ_one]
  have hpre : Set.pi Set.univ (fun _ : Fin 1 => Icc (-r) r) =
      (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' (Icc (-r) r) := by
    ext y
    constructor
    · intro h
      have := h 0 (mem_univ _)
      simpa [MeasurableEquiv.funUnique, Fin.default_eq_zero] using this
    · intro h j _
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      simpa [MeasurableEquiv.funUnique, Fin.default_eq_zero] using h
  rw [hpre]
  have hF : ∀ y : Fin 1 → ℝ, f (Fin.insertNth i (s * r) y) =
      (fun t : ℝ => f ((s * r) • basisVec i + t • basisVec (i.succAbove 0)))
        (MeasurableEquiv.funUnique (Fin 1) ℝ y) := by
    intro y
    rw [e1]
    simp [MeasurableEquiv.funUnique, Fin.default_eq_zero]
  simp_rw [hF]
  refine ((volume_preserving_funUnique (Fin 1) ℝ).setIntegral_preimage_emb
    (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding
    (fun t : ℝ => f ((s * r) • basisVec i + t • basisVec (i.succAbove 0))) (Icc (-r) r)).trans ?_
  rw [intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]

lemma hasDerivAt_face {w : Vec 2 → ℝ} (hw : ContDiff ℝ 1 w) (i : Fin 2) (c t : ℝ) :
    HasDerivAt (fun t : ℝ => w (c • basisVec i + t • basisVec (i.succAbove 0)))
      (classicalGradient w (c • basisVec i + t • basisVec (i.succAbove 0)) (i.succAbove 0)) t := by
  have hγ : HasDerivAt (fun t : ℝ => c • basisVec i + t • basisVec (i.succAbove 0))
      (basisVec (i.succAbove 0)) t := by
    simpa using ((hasDerivAt_id t).smul_const (basisVec (i.succAbove 0))).const_add (c • basisVec i)
  have hwd : HasFDerivAt w (fderiv ℝ w (c • basisVec i + t • basisVec (i.succAbove 0)))
      (c • basisVec i + t • basisVec (i.succAbove 0)) :=
    ((hw.differentiable (by norm_num)) _).hasFDerivAt
  exact hwd.comp_hasDerivAt t hγ

lemma contDiff_face {w : Vec 2 → ℝ} (hw : ContDiff ℝ 1 w) (i : Fin 2) (c : ℝ) :
    ContDiff ℝ 1 (fun t : ℝ => w (c • basisVec i + t • basisVec (i.succAbove 0))) :=
  hw.comp (contDiff_const.add (contDiff_id.smul contDiff_const))

/-- Pointwise face bound for smooth `w`. -/
lemma face_sup_sq {w : Vec 2 → ℝ} (hw : ContDiff ℝ 1 w) (i : Fin 2) {s r : ℝ} (hr : 0 < r)
    {l : ℝ} (hl : 0 < l) {t : ℝ} (ht : t ∈ Icc (-r) r) :
    w ((s * r) • basisVec i + t • basisVec (i.succAbove 0)) ^ 2 ≤
      ((2 * r)⁻¹ + l) * faceIntegral (n := 1) i s r (fun x => w x ^ 2) +
        l⁻¹ * faceIntegral (n := 1) i s r (fun x => vecNormSq (classicalGradient w x)) := by
  set φ : ℝ → ℝ := fun t => w ((s * r) • basisVec i + t • basisVec (i.succAbove 0)) with hφ
  have hφc : ContDiff ℝ 1 φ := contDiff_face hw i (s * r)
  have hder : ∀ t, deriv φ t =
      classicalGradient w ((s * r) • basisVec i + t • basisVec (i.succAbove 0))
        (i.succAbove 0) := fun t => (hasDerivAt_face hw i (s * r) t).deriv
  have h1 := sq_le_of_c1 hφc (show -r < r by linarith) hl ht
  have hcg : Continuous (fun x : Vec 2 => vecNormSq (classicalGradient w x)) :=
    continuous_vecNormSq_grad hw
  have hpath : Continuous (fun t : ℝ => (s * r) • basisVec i + t • basisVec (i.succAbove 0)) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hI2 : ∫ t in (-r)..r, (deriv φ t) ^ 2 ≤
      faceIntegral (n := 1) i s r (fun x => vecNormSq (classicalGradient w x)) := by
    rw [faceIntegral_one i s r hr.le]
    refine intervalIntegral.integral_mono_on (by linarith)
      ((hφc.continuous_deriv (by norm_num)).pow 2 |>.intervalIntegrable _ _)
      ((hcg.comp hpath).intervalIntegrable _ _) (fun t _ => ?_)
    rw [hder t]
    unfold vecNormSq vecDot
    have := Finset.single_le_sum (f := fun j => classicalGradient w
      ((s * r) • basisVec i + t • basisVec (i.succAbove 0)) j *
        classicalGradient w ((s * r) • basisVec i + t • basisVec (i.succAbove 0)) j)
      (fun j _ => mul_self_nonneg _) (Finset.mem_univ (i.succAbove 0))
    simpa [pow_two] using this
  have hI1 : ∫ t in (-r)..r, φ t ^ 2 =
      faceIntegral (n := 1) i s r (fun x => w x ^ 2) := by
    rw [faceIntegral_one i s r hr.le]
  have hsub : r - -r = 2 * r := by ring
  rw [hsub] at h1
  rw [← hI1]
  calc φ t ^ 2 ≤ ((2 * r)⁻¹ + l) * (∫ t in (-r)..r, φ t ^ 2) +
        l⁻¹ * (∫ t in (-r)..r, (deriv φ t) ^ 2) := h1
    _ ≤ _ := add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hI2 (inv_nonneg.2 hl.le))

lemma faceIntegral_le_cubeBoundaryIntegral {n : ℕ} {f : Vec (n + 1) → ℝ} (hf : ∀ x, 0 ≤ f x)
    (i : Fin (n + 1)) {s : ℝ} (hs : s ∈ ({-1, 1} : Finset ℝ)) (r : ℝ) :
    faceIntegral i s r f ≤ cubeBoundaryIntegral r f := by
  have hnn : ∀ i' s', 0 ≤ faceIntegral i' s' r f := fun i' s' =>
    integral_nonneg (fun y => hf _)
  unfold cubeBoundaryIntegral
  calc faceIntegral i s r f
      ≤ ∑ s' ∈ ({-1, 1} : Finset ℝ), faceIntegral i s' r f :=
        Finset.single_le_sum (f := fun s' => faceIntegral i s' r f) (fun s' _ => hnn i s') hs
    _ ≤ ∑ i' : Fin (n + 1), ∑ s' ∈ ({-1, 1} : Finset ℝ), faceIntegral i' s' r f :=
        Finset.single_le_sum (f := fun i' => ∑ s' ∈ ({-1, 1} : Finset ℝ), faceIntegral i' s' r f)
          (fun i' _ => Finset.sum_nonneg (fun s' _ => hnn i' s')) (Finset.mem_univ i)

/-- If the interpolation bound is below `k²`, then `(w - k)₊` vanishes on `∂Q_r`. -/
lemma cubeBoundaryIntegral_trunc_eq_zero {w : Vec 2 → ℝ} (hw : ContDiff ℝ 1 w) {r : ℝ}
    (hr : 0 < r) {l : ℝ} (hl : 0 < l) {k : ℝ} (hk0 : 0 ≤ k)
    (hk : ((2 * r)⁻¹ + l) * cubeBoundaryIntegral (n := 1) r (fun x => w x ^ 2) +
        l⁻¹ * cubeBoundaryIntegral (n := 1) r (fun x => vecNormSq (classicalGradient w x))
        < k ^ 2) :
    cubeBoundaryIntegral (n := 1) r (fun x => (max (w x - k) 0) ^ 2) = 0 := by
  unfold cubeBoundaryIntegral
  refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun s hs => ?_))
  rw [faceIntegral_one i s r hr.le]
  have hz : ∀ t ∈ uIcc (-r) r,
      (max (w ((s * r) • basisVec i + t • basisVec (i.succAbove 0)) - k) 0) ^ 2 = 0 := by
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    have hsup := face_sup_sq hw i (s := s) hr hl ht
    have hA := faceIntegral_le_cubeBoundaryIntegral (f := fun x : Vec 2 => w x ^ 2)
      (fun x => sq_nonneg _) i hs r
    have hD := faceIntegral_le_cubeBoundaryIntegral
      (f := fun x : Vec 2 => vecNormSq (classicalGradient w x)) (fun x => vecNormSq_nonneg' _) i hs r
    have hc1 : 0 ≤ (2 * r)⁻¹ + l := by positivity
    have hc2 : 0 ≤ l⁻¹ := by positivity
    have h1 := mul_le_mul_of_nonneg_left hA hc1
    have h2 := mul_le_mul_of_nonneg_left hD hc2
    have hlt : w ((s * r) • basisVec i + t • basisVec (i.succAbove 0)) ^ 2 < k ^ 2 := by
      linarith
    have hlt' : w ((s * r) • basisVec i + t • basisVec (i.succAbove 0)) < k :=
      (le_abs_self _).trans_lt (abs_lt_of_sq_lt_sq hlt hk0)
    rw [max_eq_right (by linarith)]
    ring
  rw [intervalIntegral.integral_congr hz]
  simp

end PDE.BSlocalmax
end

-- ==== from GoodRadii.lean ====
-- Limit passage for good radii (d = 2): trace-vanishing of `(V - k)₊` on almost every cube boundary
-- from the smooth approximants, via an a.e. convergent subsequence of boundary integrals.


@[expose] public section

open MeasureTheory Set Filter Topology PDE

namespace PDE.BSlocalmax

/-- Nonnegative integrable functions with integrals tending to `0` have an a.e. convergent
subsequence. -/
lemma ae_subseq_of_integral_tendsto {μ : Measure ℝ} {F : ℕ → ℝ → ℝ}
    (hint : ∀ m, Integrable (F m) μ) (h0 : ∀ m r, 0 ≤ F m r)
    (ht : Tendsto (fun m => ∫ r, F m r ∂μ) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ r ∂μ, Tendsto (fun k => F (φ k) r) atTop (𝓝 0) := by
  have h1 : ∀ m, eLpNorm (F m - (0 : ℝ → ℝ)) 1 μ = ENNReal.ofReal (∫ r, F m r ∂μ) := by
    intro m
    rw [sub_zero, eLpNorm_one_eq_lintegral_enorm (by simpa using (hint m).aestronglyMeasurable),
      ← ofReal_integral_norm_eq_lintegral_enorm (hint m)]
    have hnn : ∫ r, ‖F m r‖ ∂μ = ∫ r, F m r ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun r => Real.norm_of_nonneg (h0 m r))
    rw [hnn]
  have hT : Tendsto (fun m => eLpNorm (F m - (0 : ℝ → ℝ)) 1 μ) atTop (𝓝 0) := by
    simp only [h1]
    simpa using ENNReal.tendsto_ofReal ht
  have hm := tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero
    hT
  obtain ⟨φ, hφ, hae⟩ := hm.exists_seq_tendsto_ae
  exact ⟨φ, hφ, hae⟩

lemma integrableOn_cBI {ρ σ : ℝ} (hρ : 0 < ρ) {f : Vec (1 + 1) → ℝ}
    (hf : IntegrableOn f {x | ρ < ‖x‖ ∧ ‖x‖ < σ}) :
    IntegrableOn (fun r => cubeBoundaryIntegral r f) (Ioo ρ σ) := by
  unfold cubeBoundaryIntegral
  refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun s hs => ?_
  have hs1 : |s| = 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl <;> simp
  exact (integral_face hρ i hs1 hf).1

lemma sq_max_le (p q d k : ℝ) (hd : |p - q| ≤ d) :
    (max (p - k) 0) ^ 2 ≤ 2 * (max (q - k) 0) ^ 2 + 2 * d ^ 2 := by
  have h0 : 0 ≤ max (q - k) 0 := le_max_right _ _
  have h1 : 0 ≤ d := (abs_nonneg _).trans hd
  have h2 : max (p - k) 0 ≤ max (q - k) 0 + d := by
    refine max_le ?_ (by linarith)
    have := (abs_le.1 hd).2
    have h3 : q - k ≤ max (q - k) 0 := le_max_left _ _
    linarith
  have h3 : 0 ≤ max (p - k) 0 := le_max_right _ _
  nlinarith [sq_nonneg (max (q - k) 0 - d), mul_self_le_mul_self h3 h2]

/-- **Good radii (d = 2).** If `w m → V` and `∇ w m → g` in the sense of the hypotheses (with
`G = |g|²`), then for a.e. radius `r`, the strict inequality
`2((2r)⁻¹+λ) ∫_{∂Q_r} V² + 2λ⁻¹ ∫_{∂Q_r} G < k²` forces `(V-k)₊` to vanish on `∂Q_r`. -/
theorem trace_zero_of_approx {ρ σ : ℝ} (hρ : 0 < ρ) {V G : Vec 2 → ℝ} {w P : ℕ → Vec 2 → ℝ}
    (hw : ∀ m, ContDiff ℝ 1 (w m))
    (hV : IntegrableOn (fun x => V x ^ 2) {x | ρ < ‖x‖ ∧ ‖x‖ < σ})
    (hG : IntegrableOn G {x | ρ < ‖x‖ ∧ ‖x‖ < σ})
    (hE : ∀ m, IntegrableOn (fun x => (w m x - V x) ^ 2) {x | ρ < ‖x‖ ∧ ‖x‖ < σ})
    (hP : ∀ m, IntegrableOn (P m) {x | ρ < ‖x‖ ∧ ‖x‖ < σ})
    (hP0 : ∀ m x, 0 ≤ P m x)
    (hD : ∀ m x, vecNormSq (classicalGradient (w m) x) ≤ 2 * G x + 2 * P m x)
    (hEt : Tendsto (fun m => ∫ x in {x : Vec 2 | ρ < ‖x‖ ∧ ‖x‖ < σ}, (w m x - V x) ^ 2)
      atTop (𝓝 0))
    (hPt : Tendsto (fun m => ∫ x in {x : Vec 2 | ρ < ‖x‖ ∧ ‖x‖ < σ}, P m x) atTop (𝓝 0))
    {l k : ℝ} (hl : 0 < l) (hk : 0 ≤ k) :
    ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioo ρ σ →
      2 * ((2 * r)⁻¹ + l) * cubeBoundaryIntegral (n := 1) r (fun x => V x ^ 2) +
        2 * l⁻¹ * cubeBoundaryIntegral (n := 1) r G < k ^ 2 →
      cubeBoundaryIntegral (n := 1) r (fun x => (max (V x - k) 0) ^ 2) = 0 := by
  set S : Set (Vec 2) := {x | ρ < ‖x‖ ∧ ‖x‖ < σ} with hS
  set μ : Measure ℝ := volume.restrict (Ioo ρ σ) with hμ
  set e : ℕ → ℝ → ℝ := fun m r => cubeBoundaryIntegral (n := 1) r (fun x => (w m x - V x) ^ 2)
    with he
  set f : ℕ → ℝ → ℝ := fun m r => cubeBoundaryIntegral (n := 1) r (P m) with hf
  set F : ℕ → ℝ → ℝ := fun m r => e m r + f m r with hF
  have hen : ∀ m r, 0 ≤ e m r := fun m r => cubeBoundaryIntegral_nonneg (fun x => sq_nonneg _) r
  have hfn : ∀ m r, 0 ≤ f m r := fun m r => cubeBoundaryIntegral_nonneg (hP0 m) r
  have hFn : ∀ m r, 0 ≤ F m r := fun m r => add_nonneg (hen m r) (hfn m r)
  have heI : ∀ m, Integrable (e m) μ := fun m => integrableOn_cBI hρ (hE m)
  have hfI : ∀ m, Integrable (f m) μ := fun m => integrableOn_cBI hρ (hP m)
  have hFI : ∀ m, Integrable (F m) μ := fun m => (heI m).add (hfI m)
  have hFt : Tendsto (fun m => ∫ r, F m r ∂μ) atTop (𝓝 0) := by
    have : ∀ m, ∫ r, F m r ∂μ =
        (∫ x in S, (w m x - V x) ^ 2) + ∫ x in S, P m x := by
      intro m
      rw [hF, integral_add (heI m) (hfI m)]
      simp only [he, hf, hμ]
      rw [← integral_shell_eq_boundaryIntegral hρ (hE m),
        ← integral_shell_eq_boundaryIntegral hρ (hP m)]
    simp only [this]
    simpa using hEt.add hPt
  obtain ⟨φ, hφ, hae⟩ := ae_subseq_of_integral_tendsto hFI hFn hFt
  have hae' : ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioo ρ σ →
      Tendsto (fun j => F (φ j) r) atTop (𝓝 0) := by
    rw [hμ, ae_restrict_iff' measurableSet_Ioo] at hae
    exact hae
  have hfV := ae_faceInt hρ hV
  have hfG := ae_faceInt hρ hG
  have hfE : ∀ᵐ r ∂(volume : Measure ℝ), ∀ m, r ∈ Ioo ρ σ →
      FaceInt 1 r (fun x => (w m x - V x) ^ 2) := ae_all_iff.2 fun m => ae_faceInt hρ (hE m)
  have hfP : ∀ᵐ r ∂(volume : Measure ℝ), ∀ m, r ∈ Ioo ρ σ → FaceInt 1 r (P m) :=
    ae_all_iff.2 fun m => ae_faceInt hρ (hP m)
  filter_upwards [hae', hfV, hfG, hfE, hfP] with r hr hV' hG' hE' hP' hrm hineq
  have hr0 : 0 < r := hρ.trans hrm.1
  have hFV := hV' hrm
  have hFG := hG' hrm
  have hlim := hr hrm
  set A := cubeBoundaryIntegral (n := 1) r (fun x => V x ^ 2) with hA
  set B := cubeBoundaryIntegral (n := 1) r G with hB
  set c1 : ℝ := (2 * r)⁻¹ + l with hc1
  have hc1p : 0 < c1 := by positivity
  have hc2p : 0 < l⁻¹ := inv_pos.2 hl
  set gap : ℝ := k ^ 2 - (2 * c1 * A + 2 * l⁻¹ * B) with hgap
  have hgap0 : 0 < gap := by
    have : 2 * c1 * A + 2 * l⁻¹ * B < k ^ 2 := by
      simpa [hc1, hA, hB] using hineq
    linarith
  -- eventually the combined error is small
  have hev : ∀ᶠ j in atTop, F (φ j) r < gap / (2 * c1 + 2 * l⁻¹) :=
    hlim.eventually (gt_mem_nhds (by positivity))
  -- bound for the truncation
  have hbound : ∀ j, cubeBoundaryIntegral (n := 1) r (fun x => (max (V x - k) 0) ^ 2) ≤
      2 * cubeBoundaryIntegral (n := 1) r (fun x => (max (w (φ j) x - k) 0) ^ 2) +
        2 * e (φ j) r := by
    intro j
    have := cubeBoundaryIntegral_le_comb (n := 1) (r := r) (f := fun x => (max (V x - k) 0) ^ 2)
      (g1 := fun x => (max (w (φ j) x - k) 0) ^ 2) (g2 := fun x => (w (φ j) x - V x) ^ 2)
      (c1 := 2) (c2 := 2) (by norm_num) (by norm_num) (fun x => sq_nonneg _)
      (fun x => by
        have := sq_max_le (V x) (w (φ j) x) (|w (φ j) x - V x|) k
          (le_of_eq (abs_sub_comm _ _))
        simpa [sq_abs] using this)
      (faceInt_of_continuous
        (((hw (φ j)).continuous.sub continuous_const).max continuous_const |>.pow 2) r)
      (hE' (φ j) hrm)
    exact this
  have hzero : ∀ᶠ j in atTop,
      cubeBoundaryIntegral (n := 1) r (fun x => (max (w (φ j) x - k) 0) ^ 2) = 0 := by
    filter_upwards [hev] with j hj
    refine cubeBoundaryIntegral_trunc_eq_zero (hw (φ j)) hr0 hl hk ?_
    have hw2 := cubeBoundaryIntegral_le_comb (n := 1) (r := r) (f := fun x => w (φ j) x ^ 2)
      (g1 := fun x => V x ^ 2) (g2 := fun x => (w (φ j) x - V x) ^ 2) (c1 := 2) (c2 := 2)
      (by norm_num) (by norm_num) (fun x => sq_nonneg _)
      (fun x => by nlinarith [sq_nonneg (w (φ j) x - 2 * V x)]) hFV (hE' (φ j) hrm)
    have hD2 := cubeBoundaryIntegral_le_comb (n := 1) (r := r)
      (f := fun x => vecNormSq (classicalGradient (w (φ j)) x)) (g1 := G) (g2 := P (φ j))
      (c1 := 2) (c2 := 2) (by norm_num) (by norm_num) (fun x => vecNormSq_nonneg _)
      (hD (φ j)) hFG (hP' (φ j) hrm)
    have hef : e (φ j) r + f (φ j) r < gap / (2 * c1 + 2 * l⁻¹) := hj
    have hen' := hen (φ j) r
    have hfn' := hfn (φ j) r
    have hmul : (2 * c1 + 2 * l⁻¹) * (e (φ j) r + f (φ j) r) < gap := by
      have := (lt_div_iff₀ (by positivity : 0 < 2 * c1 + 2 * l⁻¹)).1 hef
      linarith
    have hs1 : c1 * cubeBoundaryIntegral (n := 1) r (fun x => w (φ j) x ^ 2) ≤
        c1 * (2 * A + 2 * e (φ j) r) := mul_le_mul_of_nonneg_left hw2 hc1p.le
    have hs2 : l⁻¹ * cubeBoundaryIntegral (n := 1) r
        (fun x => vecNormSq (classicalGradient (w (φ j)) x)) ≤
        l⁻¹ * (2 * B + 2 * f (φ j) r) := mul_le_mul_of_nonneg_left hD2 hc2p.le
    have hfin : c1 * (2 * A + 2 * e (φ j) r) + l⁻¹ * (2 * B + 2 * f (φ j) r) < k ^ 2 := by
      nlinarith [hmul, hgap, hen', hfn', hc1p, hc2p]
    exact lt_of_le_of_lt (add_le_add hs1 hs2) hfin
  have hlim2 : Tendsto (fun j => 2 * (0 : ℝ) + 2 * e (φ j) r) atTop (𝓝 0) := by
    have he0 : Tendsto (fun j => e (φ j) r) atTop (𝓝 0) :=
      squeeze_zero (fun j => hen _ _) (fun j => by simp only [hF]; linarith [hfn (φ j) r])
        hlim
    simpa using he0.const_mul 2
  have hle : cubeBoundaryIntegral (n := 1) r (fun x => (max (V x - k) 0) ^ 2) ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim2 (by
      filter_upwards [hzero] with j hj
      have := hbound j
      rw [hj] at this
      simpa using this)
  exact le_antisymm hle (cubeBoundaryIntegral_nonneg (fun x => sq_nonneg _) r)

end PDE.BSlocalmax
end

-- ==== from GoodMarkov.lean ====
-- Markov argument: a nonnegative integrable function with small mean on an interval is below
-- a given threshold on a measurable set of positive measure.


@[expose] public section

open MeasureTheory Set Filter

namespace PDE.BSlocalmax

lemma exists_measurable_good {a σ T : ℝ} (haσ : a < σ) (hT : 0 < T) {X : ℝ → ℝ}
    (hX : IntegrableOn X (Ioo a σ)) (hX0 : ∀ r, 0 ≤ X r)
    (hint : ∫ r in Ioo a σ, X r ≤ T * (σ - a) / 2) :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Ioo a σ ∧ 0 < volume E ∧ ∀ r ∈ E, X r < T := by
  set μ : Measure ℝ := volume.restrict (Ioo a σ) with hμ
  have hμuniv : μ univ = ENNReal.ofReal (σ - a) := by
    rw [hμ, Measure.restrict_apply_univ, Real.volume_Ioo]
  haveI : IsFiniteMeasure μ := ⟨by rw [hμuniv]; exact ENNReal.ofReal_lt_top⟩
  have hXi : Integrable X μ := hX
  have hmark := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hX0) hXi T
  set S : Set ℝ := {x | T ≤ X x} with hSdef
  have hSreal : μ.real S ≤ (σ - a) / 2 := by
    have h1 : T * μ.real S ≤ T * ((σ - a) / 2) := by
      calc T * μ.real S ≤ ∫ r, X r ∂μ := hmark
        _ ≤ T * (σ - a) / 2 := hint
        _ = T * ((σ - a) / 2) := by ring
    exact le_of_mul_le_mul_left h1 hT
  have hS : μ S ≤ ENNReal.ofReal ((σ - a) / 2) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ S)]
    exact ENNReal.ofReal_le_ofReal hSreal
  have hpos : 0 < μ Sᶜ := by
    by_contra h0
    have h0' : μ Sᶜ = 0 := by simpa using h0
    have h2 : μ univ ≤ μ S + μ Sᶜ := by
      calc μ univ = μ (S ∪ Sᶜ) := by rw [union_compl_self]
        _ ≤ _ := measure_union_le _ _
    rw [h0', add_zero, hμuniv] at h2
    have h3 := h2.trans hS
    rw [ENNReal.ofReal_le_ofReal_iff (by linarith)] at h3
    linarith
  have hSc : Sᶜ = {x | X x < T} := by ext x; simp [hSdef]
  have hnm : NullMeasurableSet Sᶜ μ := by
    rw [hSc]
    exact nullMeasurableSet_lt hX.aemeasurable aemeasurable_const
  obtain ⟨t, hts, htm, hteq⟩ := hnm.exists_measurable_subset_ae_eq
  refine ⟨t ∩ Ioo a σ, htm.inter measurableSet_Ioo, inter_subset_right, ?_, ?_⟩
  · have : volume (t ∩ Ioo a σ) = μ t := (Measure.restrict_apply htm).symm
    rw [this, measure_congr hteq]
    exact hpos
  · intro r hr
    have := hts hr.1
    rw [hSc] at this
    exact this

/-- Good radii: the same with an a.e. implication to a conclusion `Q`. -/
lemma exists_good_radii {a σ T : ℝ} (haσ : a < σ) (hT : 0 < T) {X : ℝ → ℝ}
    (hX : IntegrableOn X (Ioo a σ)) (hX0 : ∀ r, 0 ≤ X r)
    (hint : ∫ r in Ioo a σ, X r ≤ T * (σ - a) / 2) {Q : ℝ → Prop}
    (hQ : ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioo a σ → X r < T → Q r) :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Ioo a σ ∧ 0 < volume E ∧ ∀ r ∈ E, Q r := by
  obtain ⟨E0, hE0m, hE0s, hE0pos, hE0X⟩ := exists_measurable_good haσ hT hX hX0 hint
  have hN : volume {r | ¬ (r ∈ Ioo a σ → X r < T → Q r)} = 0 := ae_iff.1 hQ
  obtain ⟨N, hNs, hNm, hN0⟩ := exists_measurable_superset_of_null hN
  refine ⟨E0 \ N, hE0m.diff hNm, diff_subset.trans hE0s, ?_, ?_⟩
  · rw [measure_diff_null hN0]; exact hE0pos
  · intro r hr
    by_contra hQr
    exact hr.2 (hNs (fun h => hQr (h (hE0s hr.1) (hE0X r hr.1))))

end PDE.BSlocalmax
end

-- ==== from Dim2.lean ====
-- The case `d = 2` of Proposition 1 (Bella–Schäffner / Schäffner): the local maximum principle with
-- the sharp exponent `Λ^{1/4}`, via the trace-free maximum principle and the face interpolation.


@[expose] public section

open MeasureTheory Set Filter Topology PDE PDE.Ch4Infra

namespace PDE.BSlocalmax

lemma vecNormSq_add_le2 {d : ℕ} (x y : Vec d) :
    vecNormSq (x + y) ≤ 2 * vecNormSq x + 2 * vecNormSq y := by
  unfold vecNormSq vecDot
  simp only [Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  nlinarith [sq_nonneg (x i - y i)]

lemma max_max_sub_zero (t k : ℝ) (hk : 0 ≤ k) :
    max (max (t - 0) 0 - k) 0 = max (t - k) 0 := by
  rw [sub_zero]
  rcases le_total t 0 with h | h
  · rw [max_eq_right h, max_eq_right (by linarith : (0 : ℝ) - k ≤ 0),
      max_eq_right (by linarith : t - k ≤ 0)]
  · rw [max_eq_left h]

set_option maxHeartbeats 1600000 in
/-- Key step for `d = 2`: for every `k > 0` with `8 K₀ √Λ M ≤ k²`, `u ≤ k` a.e. on `Q_{1/2}`. -/
theorem two_dim_key {C0 : ℝ} (hC0 : 0 < C0)
    (hI : ∀ {Λ : ℝ} {a : CoeffField (1 + 1)},
      (∀ i j, AEMeasurable (fun x => a x i j) (volumeOn (Metric.ball (0 : Vec (1 + 1)) 1))) →
      (∀ x ∈ Metric.ball (0 : Vec (1 + 1)) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ {u : H1Function (Metric.ball (0 : Vec (1 + 1)) 1)},
        IsWeakDivergenceFormSubharmonicOn a (Metric.ball (0 : Vec (1 + 1)) 1) u →
        Eng u 0 (3 / 4) ≤ C0 * Λ * ∫ x in Metric.ball (0 : Vec (1 + 1)) 1, (u.toFun x) ^ 2)
    {Λ : ℝ} {a : CoeffField (1 + 1)}
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn (Metric.ball (0 : Vec (1 + 1)) 1)))
    (hEll : ∀ x ∈ Metric.ball (0 : Vec (1 + 1)) 1, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function (Metric.ball (0 : Vec (1 + 1)) 1)}
    (hsub : IsWeakDivergenceFormSubharmonicOn a (Metric.ball (0 : Vec (1 + 1)) 1) u)
    {k : ℝ} (hk : 0 < k)
    (hkM : 8 * (4 + 2 * C0) * Real.sqrt Λ * ∫ x in Metric.ball (0 : Vec (1 + 1)) 1,
      (u.toFun x) ^ 2 ≤ k ^ 2) :
    ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : Vec (1 + 1)) (1 / 2))), max (u.toFun x - k) 0 = 0 := by
  have hΛ : 1 ≤ Λ := (hEll 0 (Metric.mem_ball_self one_pos)).lam_le_Lam
  have hΛ0 : 0 < Λ := by linarith
  set l : ℝ := Real.sqrt Λ with hl
  have hl0 : 0 < l := Real.sqrt_pos.2 hΛ0
  have hll : l * l = Λ := Real.mul_self_sqrt hΛ0.le
  have hl1 : 1 ≤ l := by
    by_contra h
    push_neg at h
    nlinarith
  set M : ℝ := ∫ x in Metric.ball (0 : Vec (1 + 1)) 1, (u.toFun x) ^ 2 with hM
  have hM0 : 0 ≤ M := integral_nonneg fun x => sq_nonneg _
  have hEng := hI ha hEll hsub
  have hu2 : IntegrableOn (fun x => (u.toFun x) ^ 2) (Metric.ball (0 : Vec (1 + 1)) 1) := by
    simpa only [pow_two] using integrableOn_mul_of_memL2On u.memL2 u.memL2
  -- shell and approximations
  obtain ⟨w, hwC, hVint, hGint, -, -, hE, hP, hEt, hPt⟩ := exists_smooth_approx_cube u 0
  set S : Set (Vec (1 + 1)) := {x | 1 / 2 < ‖x‖ ∧ ‖x‖ < 3 / 4} with hS
  have hSball : S ⊆ Metric.ball (0 : Vec (1 + 1)) 1 := fun x hx => by
    rw [Metric.mem_ball, dist_zero_right]; linarith [hx.2]
  have hSball34 : S ⊆ Metric.ball (0 : Vec (1 + 1)) (3 / 4) := fun x hx => by
    rw [Metric.mem_ball, dist_zero_right]; exact hx.2
  have hV' : IntegrableOn (fun x => (max (u.toFun x - 0) 0) ^ 2) S := hVint.mono_set hSball
  have hG' : IntegrableOn (fun x => vecNormSq ({y | 0 < u.toFun y}.indicator u.grad x)) S :=
    hGint.mono_set hSball
  have hE' : ∀ m, IntegrableOn (fun x => (w m x - max (u.toFun x - 0) 0) ^ 2) S :=
    fun m => (hE m).mono_set hSball
  have hP' : ∀ m, IntegrableOn (fun x => vecNormSq (classicalGradient (w m) x -
      {y | 0 < u.toFun y}.indicator u.grad x)) S := fun m => (hP m).mono_set hSball
  have hD : ∀ m x, vecNormSq (classicalGradient (w m) x) ≤
      2 * vecNormSq ({y | 0 < u.toFun y}.indicator u.grad x) +
        2 * vecNormSq (classicalGradient (w m) x - {y | 0 < u.toFun y}.indicator u.grad x) := by
    intro m x
    have := vecNormSq_add_le2 ({y | 0 < u.toFun y}.indicator u.grad x)
      (classicalGradient (w m) x - {y | 0 < u.toFun y}.indicator u.grad x)
    rw [add_sub_cancel] at this
    exact this
  have hEt' : Tendsto (fun m => ∫ x in S, (w m x - max (u.toFun x - 0) 0) ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun m => integral_nonneg fun x => sq_nonneg _)
      (fun m => setIntegral_mono_set (hE m) (Filter.Eventually.of_forall fun x => sq_nonneg _)
        (HasSubset.Subset.eventuallyLE hSball)) hEt
  have hPt' : Tendsto (fun m => ∫ x in S, vecNormSq (classicalGradient (w m) x -
      {y | 0 < u.toFun y}.indicator u.grad x)) atTop (𝓝 0) :=
    squeeze_zero (fun m => integral_nonneg fun x => vecNormSq_nonneg' _)
      (fun m => setIntegral_mono_set (hP m)
        (Filter.Eventually.of_forall fun x => vecNormSq_nonneg' _)
        (HasSubset.Subset.eventuallyLE hSball)) hPt
  have hae := trace_zero_of_approx (ρ := 1 / 2) (σ := 3 / 4) (by norm_num)
    (V := fun x => max (u.toFun x - 0) 0)
    (G := fun x => vecNormSq ({y | 0 < u.toFun y}.indicator u.grad x))
    (w := w) (P := fun m x => vecNormSq (classicalGradient (w m) x -
      {y | 0 < u.toFun y}.indicator u.grad x))
    hwC hV' hG' hE' hP' (fun m x => vecNormSq_nonneg' _) hD hEt' hPt' hl0 hk.le
  -- integrals of the boundary quantities
  have hA : IntegrableOn (fun r => cubeBoundaryIntegral (n := 1) r
      (fun x => (max (u.toFun x - 0) 0) ^ 2)) (Ioo (1 / 2) (3 / 4)) :=
    integrableOn_cBI (by norm_num) hV'
  have hB : IntegrableOn (fun r => cubeBoundaryIntegral (n := 1) r
      (fun x => vecNormSq ({y | 0 < u.toFun y}.indicator u.grad x))) (Ioo (1 / 2) (3 / 4)) :=
    integrableOn_cBI (by norm_num) hG'
  have hA0 : ∀ r, 0 ≤ cubeBoundaryIntegral (n := 1) r (fun x => (max (u.toFun x - 0) 0) ^ 2) :=
    fun r => cubeBoundaryIntegral_nonneg (fun x => sq_nonneg _) r
  have hB0 : ∀ r, 0 ≤ cubeBoundaryIntegral (n := 1) r
      (fun x => vecNormSq ({y | 0 < u.toFun y}.indicator u.grad x)) :=
    fun r => cubeBoundaryIntegral_nonneg (fun x => vecNormSq_nonneg' _) r
  set X : ℝ → ℝ := fun r => 2 * (1 + l) * cubeBoundaryIntegral (n := 1) r
      (fun x => (max (u.toFun x - 0) 0) ^ 2) +
    2 * l⁻¹ * cubeBoundaryIntegral (n := 1) r
      (fun x => vecNormSq ({y | 0 < u.toFun y}.indicator u.grad x)) with hX
  have hXi : IntegrableOn X (Ioo (1 / 2) (3 / 4)) := (hA.const_mul _).add (hB.const_mul _)
  have hX0 : ∀ r, 0 ≤ X r := fun r =>
    add_nonneg (mul_nonneg (by positivity) (hA0 r)) (mul_nonneg (by positivity) (hB0 r))
  -- bounds
  have hAb : ∫ x in S, (max (u.toFun x - 0) 0) ^ 2 ≤ M := by
    calc ∫ x in S, (max (u.toFun x - 0) 0) ^ 2 ≤ ∫ x in S, (u.toFun x) ^ 2 := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _)
            (hu2.mono_set hSball) (Filter.Eventually.of_forall fun x => ?_)
          beta_reduce
          rw [sub_zero]
          rcases le_total (u.toFun x) 0 with h | h
          · rw [max_eq_right h]; nlinarith [sq_nonneg (u.toFun x)]
          · rw [max_eq_left h]
      _ ≤ M := setIntegral_mono_set hu2 (Filter.Eventually.of_forall fun x => sq_nonneg _)
          (HasSubset.Subset.eventuallyLE hSball)
  have hZint : IntegrableOn (fun x => (max (u.toFun x - 0) 0) ^ 2 +
      vecNormSq ({y | 0 < u.toFun y}.indicator u.grad x)) (Metric.ball (0 : Vec (1 + 1)) (3 / 4)) :=
    eng_integrand_integrable u 0 (by norm_num)
  have hBb : ∫ x in S, vecNormSq ({y | 0 < u.toFun y}.indicator u.grad x) ≤ C0 * Λ * M := by
    calc ∫ x in S, vecNormSq ({y | 0 < u.toFun y}.indicator u.grad x)
        ≤ ∫ x in S, ((max (u.toFun x - 0) 0) ^ 2 +
            vecNormSq ({y | 0 < u.toFun y}.indicator u.grad x)) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x =>
            vecNormSq_nonneg' _) (hZint.mono_set hSball34)
            (Filter.Eventually.of_forall fun x => ?_)
          beta_reduce
          nlinarith [sq_nonneg (max (u.toFun x - 0) 0)]
      _ ≤ Eng u 0 (3 / 4) :=
          setIntegral_mono_set hZint (Filter.Eventually.of_forall fun x => eng_integrand_nonneg u 0 x)
            (HasSubset.Subset.eventuallyLE hSball34)
      _ ≤ C0 * Λ * M := hEng
  have hIX : ∫ r in Ioo (1 / 2 : ℝ) (3 / 4), X r =
      2 * (1 + l) * (∫ x in S, (max (u.toFun x - 0) 0) ^ 2) +
        2 * l⁻¹ * ∫ x in S, vecNormSq ({y | 0 < u.toFun y}.indicator u.grad x) := by
    rw [hX]
    simp only
    rw [integral_add (hA.const_mul _) (hB.const_mul _), integral_const_mul, integral_const_mul,
      ← integral_shell_eq_boundaryIntegral (by norm_num : (0 : ℝ) < 1 / 2) (σ := 3 / 4) hV',
      ← integral_shell_eq_boundaryIntegral (by norm_num : (0 : ℝ) < 1 / 2) (σ := 3 / 4) hG']
  have hint : ∫ r in Ioo (1 / 2 : ℝ) (3 / 4), X r ≤ k ^ 2 * (3 / 4 - 1 / 2) / 2 := by
    rw [hIX]
    have e1 : l⁻¹ * (C0 * Λ * M) = C0 * l * M := by
      rw [← hll]; field_simp
    have h1 : 2 * (1 + l) * (∫ x in S, (max (u.toFun x - 0) 0) ^ 2) ≤ 4 * l * M := by
      calc _ ≤ 2 * (1 + l) * M := mul_le_mul_of_nonneg_left hAb (by positivity)
        _ ≤ 4 * l * M := by nlinarith
    have h2 : 2 * l⁻¹ * (∫ x in S, vecNormSq ({y | 0 < u.toFun y}.indicator u.grad x)) ≤
        2 * (C0 * l * M) := by
      calc _ ≤ 2 * l⁻¹ * (C0 * Λ * M) := mul_le_mul_of_nonneg_left hBb (by positivity)
        _ = 2 * (l⁻¹ * (C0 * Λ * M)) := by ring
        _ = _ := by rw [e1]
    nlinarith [hkM]
  have hQ : ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioo (1 / 2 : ℝ) (3 / 4) → X r < k ^ 2 →
      cubeBoundaryIntegral (n := 1) r (fun x => (max (max (u.toFun x - 0) 0 - k) 0) ^ 2) = 0 := by
    filter_upwards [hae] with r hr hrI hXr
    refine hr hrI ?_
    have hr2 : (2 * r)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [hrI.1])
    have := mul_nonneg (sub_nonneg.2 hr2) (hA0 r)
    have hXr' : 2 * (1 + l) * cubeBoundaryIntegral (n := 1) r
      (fun x => (max (u.toFun x - 0) 0) ^ 2) + 2 * l⁻¹ * cubeBoundaryIntegral (n := 1) r
      (fun x => vecNormSq ({y | 0 < u.toFun y}.indicator u.grad x)) < k ^ 2 := hXr
    nlinarith [this]
  obtain ⟨E, hEm, hEs, hEpos, hEQ⟩ := exists_good_radii (a := 1 / 2) (σ := 3 / 4) (T := k ^ 2)
    (by norm_num) (by positivity) hXi hX0 hint hQ
  refine maxPrinciple_trace (n := 1) (Λ := Λ) (a := 1 / 2) (σ := 3 / 4) (k := k) (coeff := a)
    (by norm_num) (by norm_num) ha hEll hsub hEm hEs hEpos ?_
  intro r hr
  have := hEQ r hr
  have hfun : (fun x : Vec (1 + 1) => (max (max (u.toFun x - 0) 0 - k) 0) ^ 2) =
      fun x => (max (u.toFun x - k) 0) ^ 2 := by
    funext x
    rw [max_max_sub_zero _ _ hk.le]
  rw [hfun] at this
  exact this

end PDE.BSlocalmax
end

-- ==== from Dim2Main.lean ====
-- Main theorem for `d = 2`: sharp local maximum principle with exponent `Λ^{1/4}`.


@[expose] public section

open MeasureTheory Set Filter Topology PDE PDE.Ch4Infra

namespace PDE.BSlocalmax

set_option maxHeartbeats 1600000 in
/-- **Proposition 1 for `d = 2`** (cube version): `sup_{Q_{1/2}} u ≤ C Λ^{1/4} ‖u‖_{L²(Q_1)}`. -/
theorem exists_sharpLocalMax_constant_cube_two :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (a : CoeffField 2),
      (∀ i j : Fin 2, AEMeasurable (fun x => a x i j) (volumeOn (Metric.ball (0 : Vec 2) 1))) →
      (∀ x ∈ Metric.ball (0 : Vec 2) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (Metric.ball (0 : Vec 2) 1),
      IsWeakDivergenceFormSubharmonicOn a (Metric.ball (0 : Vec 2) 1) u →
        essSup (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (Metric.ball (0 : Vec 2) (1 / 2))) ≤
          ENNReal.ofReal (C * Λ ^ ((1 : ℝ) / 4)) *
            eLpNorm u.toFun 2 (volumeOn (Metric.ball (0 : Vec 2) 1)) := by
  obtain ⟨C0, hC0, hI⟩ := initial_energy_gen (n := 1)
  set K0 : ℝ := 4 + 2 * C0 with hK0
  have hK0p : 0 < K0 := by rw [hK0]; positivity
  refine ⟨Real.sqrt (8 * K0), by positivity, ?_⟩
  intro Λ a ha hEll u hsub
  have hΛ : 1 ≤ Λ := (hEll 0 (Metric.mem_ball_self one_pos)).lam_le_Lam
  have hΛ0 : 0 < Λ := by linarith
  have hmem : MemLp u.toFun 2 (volumeOn (Metric.ball (0 : Vec 2) 1)) := u.memL2
  set E0 : ℝ := (eLpNorm u.toFun 2 (volumeOn (Metric.ball (0 : Vec 2) 1))).toReal with hE0
  have hE0n : 0 ≤ E0 := ENNReal.toReal_nonneg
  have hE0sq : E0 ^ 2 = ∫ x in Metric.ball (0 : Vec 2) 1, (u.toFun x) ^ 2 :=
    toReal_eLpNorm_two_sq_eq_integral_sq hmem
  have hfin : eLpNorm u.toFun 2 (volumeOn (Metric.ball (0 : Vec 2) 1)) ≠ ⊤ :=
    hmem.eLpNorm_ne_top
  set k0 : ℝ := Real.sqrt (8 * K0) * Λ ^ ((1 : ℝ) / 4) * E0 with hk0
  have hk0n : 0 ≤ k0 := by positivity
  have hq : (Λ ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt Λ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hΛ0.le, Real.sqrt_eq_rpow]
    norm_num
  have hk0sq : k0 ^ 2 = 8 * K0 * Real.sqrt Λ * ∫ x in Metric.ball (0 : Vec 2) 1, (u.toFun x) ^ 2 := by
    rw [hk0, mul_pow, mul_pow, Real.sq_sqrt (by positivity), hq, hE0sq]
  have hrhs : ENNReal.ofReal (Real.sqrt (8 * K0) * Λ ^ ((1 : ℝ) / 4)) *
      eLpNorm u.toFun 2 (volumeOn (Metric.ball (0 : Vec 2) 1)) = ENNReal.ofReal k0 := by
    have hE0e : ENNReal.ofReal E0 =
        eLpNorm u.toFun 2 (volumeOn (Metric.ball (0 : Vec 2) 1)) := by
      rw [hE0, ENNReal.ofReal_toReal hfin]
    rw [hk0, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ Real.sqrt (8 * K0) * Λ ^ ((1 : ℝ) / 4)),
      hE0e]
  rw [hrhs]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hεr : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have hk : 0 < k0 + (ε : ℝ) := by linarith
  have hkM : 8 * (4 + 2 * C0) * Real.sqrt Λ * ∫ x in Metric.ball (0 : Vec 2) 1, (u.toFun x) ^ 2 ≤
      (k0 + (ε : ℝ)) ^ 2 := by
    have := hk0sq
    rw [hK0] at this
    nlinarith [this, hk0n, hεr]
  have hae := two_dim_key hC0 hI ha hEll hsub hk hkM
  have hess : essSup (fun x => ENNReal.ofReal (u.toFun x))
      (volumeOn (Metric.ball (0 : Vec 2) (1 / 2))) ≤ ENNReal.ofReal (k0 + (ε : ℝ)) := by
    refine essSup_le_of_ae_le _ ?_
    filter_upwards [hae] with x hx
    have h3 : u.toFun x - (k0 + (ε : ℝ)) ≤ 0 := hx ▸ le_max_left _ _
    exact ENNReal.ofReal_le_ofReal (by linarith)
  calc _ ≤ ENNReal.ofReal (k0 + (ε : ℝ)) := hess
    _ = ENNReal.ofReal k0 + (ε : ENNReal) := by
        rw [ENNReal.ofReal_add hk0n hεr.le, ENNReal.ofReal_coe_nnreal]

end PDE.BSlocalmax
end
