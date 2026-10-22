module

public import EllipticRegularity.Ch4.GreenFunction.Setting
public import EllipticRegularity.Ch4.GreenFunction.Riesz

/-!
# Existence of the Green function (Step 2 of Proposition 4.40)

For each `ε ∈ (0, R]`, the Riesz representation theorem on `L²(B_R \ B_ε)` applied to the limit
functional `f ↦ lim ∫ Gₙ f` gives `G^{(ε)}`; these are compatible, and gluing them along
`ε_k = R / 2^{k+1}` gives a Green function.
-/

@[expose] public section

open scoped Topology ENNReal

namespace PDE.Ch4Green

open MeasureTheory PDE Filter

variable {d : ℕ}

/-- The limit property of `G` on a set `T`: `∫_T Gₙ f → ∫_T G f` for all `f ∈ L²(T)`. -/
def WeakLimitOn (Gn : ℕ → Vec d → ℝ) (T : Set (Vec d)) (G : Vec d → ℝ) : Prop :=
  ∀ f : Vec d → ℝ, MemL2On T f →
    Tendsto (fun n => ∫ x in T, Gn n x * f x) atTop (𝓝 (∫ x in T, G x * f x))

/-- Integrating against an indicator. -/
theorem integral_mul_indicator {T T' : Set (Vec d)} (hT : MeasurableSet T) (hTT' : T ⊆ T')
    (h f : Vec d → ℝ) :
    ∫ x in T', h x * T.indicator f x = ∫ x in T, h x * f x := by
  have : (fun x => h x * T.indicator f x) = T.indicator (fun x => h x * f x) := by
    funext x
    by_cases hx : x ∈ T <;> simp [hx]
  rw [this, integral_indicator hT, Measure.restrict_restrict hT, Set.inter_eq_left.2 hTT']

theorem memL2On_indicator {T T' : Set (Vec d)} (hT : MeasurableSet T) (hTT' : T ⊆ T')
    {f : Vec d → ℝ} (hf : MemL2On T f) : MemL2On T' (T.indicator f) := by
  unfold MemL2On MemLpOn at *
  rw [memLp_indicator_iff_restrict hT, Measure.restrict_restrict hT, Set.inter_eq_left.2 hTT']
  exact hf

theorem eLpNorm_indicator_eq {T T' : Set (Vec d)} (hT : MeasurableSet T) (hTT' : T ⊆ T')
    (f : Vec d → ℝ) :
    eLpNorm (T.indicator f) 2 (volumeOn T') = eLpNorm f 2 (volumeOn T) := by
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hT, volumeOn, Measure.restrict_restrict hT,
    Set.inter_eq_left.2 hTT']

/-- The weak-limit property restricts to measurable subsets. -/
theorem WeakLimitOn.mono {Gn : ℕ → Vec d → ℝ} {T T' : Set (Vec d)} {G : Vec d → ℝ}
    (h : WeakLimitOn Gn T' G) (hT : MeasurableSet T) (hTT' : T ⊆ T') : WeakLimitOn Gn T G := by
  intro f hf
  have := h _ (memL2On_indicator hT hTT' hf)
  simpa only [integral_mul_indicator hT hTT'] using this

/-- Weak limits are unique a.e. -/
theorem WeakLimitOn.ae_eq {Gn : ℕ → Vec d → ℝ} {T : Set (Vec d)} {G G' : Vec d → ℝ}
    (h : WeakLimitOn Gn T G) (h' : WeakLimitOn Gn T G') (hG : MemL2On T G)
    (hG' : MemL2On T G') : G =ᵐ[volumeOn T] G' := by
  have hsub : (fun x => G x - G' x) =ᵐ[volumeOn T] 0 := by
    refine ae_eq_zero_of_integral_mul_eq_zero (hG.sub hG') fun f hf => ?_
    have heq := tendsto_nhds_unique (h f hf) (h' f hf)
    have hsplit : ∫ x in T, (G x - G' x) * f x =
        (∫ x in T, G x * f x) - ∫ x in T, G' x * f x := by
      have i1 : Integrable (fun x => G x * f x) (volumeOn T) :=
        MemLp.integrable_mul (p := 2) (q := 2) hG hf
      have i2 : Integrable (fun x => G' x * f x) (volumeOn T) :=
        MemLp.integrable_mul (p := 2) (q := 2) hG' hf
      rw [← integral_sub i1 i2]
      congr 1
      funext x
      ring
    change ∫ x in T, (G x - G' x) * f x = 0
    rw [hsplit, heq, sub_self]
  filter_upwards [hsub] with x hx
  simpa [sub_eq_zero] using hx

/-- If `g` vanishes a.e. on `B_ε`, integrals over `B_R` reduce to `B_R \ B_ε`. -/
theorem integral_eq_integral_diff_of_ae_zero {R ε : ℝ} {g : Vec d → ℝ}
    (hg : ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) ε)), g x = 0) (h : Vec d → ℝ) :
    ∫ x in euclideanBall (0 : Vec d) R, h x * g x =
      ∫ x in euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) ε, h x * g x := by
  refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (μ := volume)
    (f := fun x => h x * g x)
    (measurableSet_euclideanBall (0 : Vec d) R).nullMeasurableSet Set.sdiff_subset ?_
  have hg' := (ae_restrict_iff' (measurableSet_euclideanBall (0 : Vec d) ε)).1 hg
  filter_upwards [hg'] with x hx hxd
  have : x ∈ euclideanBall (0 : Vec d) ε := by
    by_contra hne
    exact hxd.2 ⟨hxd.1, hne⟩
  simp [hx this]

namespace ApproxSetting

variable {Λ R : ℝ} {a : CoeffField d}

/-- **Riesz step.**  For each `ε ∈ (0, R]`, the approximate Green functions have a weak limit
`G^{(ε)} ∈ L²(B_R \ B_ε)`. -/
theorem exists_weakLimit (S : ApproxSetting d Λ R a) (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (hεR : ε ≤ R) :
    ∃ G : Vec d → ℝ, StronglyMeasurable G ∧
      MemL2On (euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) ε) G ∧
      WeakLimitOn (fun n => (S.G n).toH1Function.toFun)
        (euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) ε) G := by
  set T := euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) ε with hTdef
  have hT : MeasurableSet T :=
    (measurableSet_euclideanBall _ _).diff (measurableSet_euclideanBall _ _)
  have hTB : T ⊆ euclideanBall (0 : Vec d) R := Set.sdiff_subset
  obtain ⟨C, -, hconv⟩ := S.exists_tendsto hd
  have hzero : ∀ f : Vec d → ℝ,
      ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) ε)), T.indicator f x = 0 := by
    intro f
    refine (ae_restrict_iff' (measurableSet_euclideanBall _ _)).2 (Eventually.of_forall ?_)
    intro x hx
    exact Set.indicator_of_notMem (fun h => h.2 hx) _
  obtain ⟨G, hGm, hGL, hGlim⟩ := exists_rep_of_tendsto_integral (μ := volume.restrict T)
    (Gn := fun n => (S.G n).toH1Function.toFun)
    (fun n => (S.G n).toH1Function.memL2.mono_measure (Measure.restrict_mono hTB le_rfl))
    (fun f hf => by
      obtain ⟨L, hL, -, -⟩ := hconv hε hεR (memL2On_indicator hT hTB hf) (hzero f)
      exact ⟨L, by simpa only [integral_mul_indicator hT hTB] using hL⟩)
    (K := poleConst C Λ ε S.E d)
    (fun f hf L hL => by
      obtain ⟨L', hL', hbd, -⟩ := hconv hε hεR (memL2On_indicator hT hTB hf) (hzero f)
      have hL'' := hL'
      simp only [integral_mul_indicator hT hTB] at hL''
      rw [tendsto_nhds_unique hL hL'']
      rwa [eLpNorm_indicator_eq hT hTB] at hbd)
  exact ⟨G, hGm, hGL, hGlim⟩

end ApproxSetting

/-- Dyadic radii `ε_k = R / 2^{k+1}`. -/
noncomputable def dyadicRadius (R : ℝ) (k : ℕ) : ℝ := R / 2 ^ (k + 1)

theorem dyadicRadius_pos {R : ℝ} (hR : 0 < R) (k : ℕ) : 0 < dyadicRadius R k := by
  unfold dyadicRadius; positivity

theorem dyadicRadius_le {R : ℝ} (hR : 0 < R) (k : ℕ) : dyadicRadius R k ≤ R := by
  unfold dyadicRadius
  rw [div_le_iff₀ (by positivity)]
  have : (1 : ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
  nlinarith

theorem dyadicRadius_anti {R : ℝ} (hR : 0 < R) {j k : ℕ} (hjk : j ≤ k) :
    dyadicRadius R k ≤ dyadicRadius R j := by
  unfold dyadicRadius
  apply div_le_div_of_nonneg_left hR.le (by positivity)
  exact pow_le_pow_right₀ (by norm_num) (by omega)

theorem exists_dyadicRadius_le {R : ℝ} (hR : 0 < R) {s : ℝ} (hs : 0 < s) :
    ∃ k : ℕ, dyadicRadius R k ≤ s := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hs hR) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨k, ?_⟩
  unfold dyadicRadius
  rw [div_le_iff₀ (by positivity)]
  rw [lt_div_iff₀ hR] at hk
  have h1 : (1 / 2 : ℝ) ^ k * R = R / 2 ^ k := by
    rw [one_div, inv_pow, inv_mul_eq_div]
  rw [h1, div_lt_iff₀ (by positivity)] at hk
  rw [pow_succ]
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) k]

/-- Membership in `B_R \ B_ε` through the Euclidean norm. -/
theorem mem_ballDiff_iff {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) {x : Vec d} :
    x ∈ euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) ε ↔
      vecEuclideanNorm x < R ∧ ε ≤ vecEuclideanNorm x := by
  rw [Set.mem_sdiff, mem_euclideanBall_iff_vecEuclideanNorm_lt hR,
    mem_euclideanBall_iff_vecEuclideanNorm_lt hε, sub_zero, not_lt]

namespace ApproxSetting

variable {Λ R : ℝ} {a : CoeffField d}

/-- **Existence of the Green function** (Step 2 of Proposition 4.40). -/
theorem exists_isGreenFunction (S : ApproxSetting d Λ R a) (hd : 3 ≤ d) :
    ∃ G : Vec d → ℝ, IsGreenFunction a R G := by
  classical
  have hR := S.hR
  set T : ℕ → Set (Vec d) := fun k =>
    euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) (dyadicRadius R k) with hTdef
  have hT : ∀ k, MeasurableSet (T k) := fun k =>
    (measurableSet_euclideanBall _ _).diff (measurableSet_euclideanBall _ _)
  have hTB : ∀ k, T k ⊆ euclideanBall (0 : Vec d) R := fun k => Set.sdiff_subset
  have hTmono : ∀ {j k : ℕ}, j ≤ k → T j ⊆ T k := by
    intro j k hjk x hx
    exact ⟨hx.1, fun h => hx.2 (euclideanBall_mono (dyadicRadius_pos hR k).le
      (dyadicRadius_anti hR hjk) h)⟩
  have hex : ∀ k, ∃ G : Vec d → ℝ, StronglyMeasurable G ∧ MemL2On (T k) G ∧
      WeakLimitOn (fun n => (S.G n).toH1Function.toFun) (T k) G := fun k =>
    S.exists_weakLimit hd (dyadicRadius_pos hR k) (dyadicRadius_le hR k)
  choose Gk hGkm hGkL hGklim using hex
  let p : ℕ → Vec d → Prop := fun k x => dyadicRadius R k ≤ vecEuclideanNorm x ∨ x = 0
  have hp : ∀ x, ∃ k, p k x := by
    intro x
    by_cases hx : x = 0
    · exact ⟨0, Or.inr hx⟩
    · obtain ⟨k, hk⟩ := exists_dyadicRadius_le hR (vecEuclideanNorm_pos_iff.mpr hx)
      exact ⟨k, Or.inl hk⟩
  have hpm : ∀ k, MeasurableSet {x | p k x} := by
    intro k
    have : {x | p k x} = {x : Vec d | dyadicRadius R k ≤ vecEuclideanNorm x} ∪ {0} := by
      ext x; simp [p, or_comm]
    rw [this]
    exact (measurableSet_le measurable_const continuous_vecEuclideanNorm.measurable).union
      (measurableSet_singleton 0)
  let G : Vec d → ℝ := fun x => Gk (Nat.find (hp x)) x
  have hGmeas : Measurable G := Measurable.find (fun k => (hGkm k).measurable) hpm hp
  have hcompat : ∀ j k, j ≤ k → Gk j =ᵐ[volumeOn (T j)] Gk k := fun j k hjk =>
    (hGklim j).ae_eq ((hGklim k).mono (hT j) (hTmono hjk)) (hGkL j)
      ((hGkL k).mono_measure (Measure.restrict_mono (hTmono hjk) le_rfl))
  have hGT : ∀ k, G =ᵐ[volumeOn (T k)] Gk k := by
    intro k
    have hall : ∀ᵐ x ∂volume, ∀ j, j ≤ k → x ∈ T j → Gk j x = Gk k x := by
      rw [ae_all_iff]
      intro j
      by_cases hjk : j ≤ k
      · have := (ae_restrict_iff' (hT j)).1 (hcompat j k hjk)
        filter_upwards [this] with x hx _ hxT using hx hxT
      · exact Eventually.of_forall fun x h => absurd h hjk
    refine (ae_restrict_iff' (hT k)).2 ?_
    filter_upwards [hall] with x hx hxT
    have hxk := (mem_ballDiff_iff hR (dyadicRadius_pos hR k)).1 hxT
    have hx0 : x ≠ 0 := by
      intro h
      rw [h, vecEuclideanNorm_eq_zero_iff.2 rfl] at hxk
      linarith [dyadicRadius_pos hR k]
    have hle : Nat.find (hp x) ≤ k := Nat.find_min' _ (Or.inl hxk.2)
    have hpj : p (Nat.find (hp x)) x := Nat.find_spec (hp x)
    have hxTj : x ∈ T (Nat.find (hp x)) := by
      refine (mem_ballDiff_iff hR (dyadicRadius_pos hR _)).2 ⟨hxk.1, ?_⟩
      rcases hpj with h | h
      · exact h
      · exact absurd h hx0
    exact hx _ hle hxTj
  obtain ⟨C, -, hconv⟩ := S.exists_tendsto hd
  refine ⟨G, hGmeas, ?_, ?_⟩
  · intro ε hε hεR
    obtain ⟨k, hk⟩ := exists_dyadicRadius_le hR hε
    have hsub : euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) ε ⊆ T k := by
      intro x hx
      exact ⟨hx.1, fun h => hx.2 (euclideanBall_mono (dyadicRadius_pos hR k).le hk h)⟩
    have : MemL2On (T k) G := (hGkL k).ae_eq (hGT k).symm
    exact this.mono_measure (Measure.restrict_mono hsub le_rfl)
  · intro ε hε hεR g hg2 hg v hv
    obtain ⟨k, hk⟩ := exists_dyadicRadius_le hR hε
    obtain ⟨L, hL, -, hvL⟩ := hconv hε hεR.le hg2 hg
    have hgk : ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) (dyadicRadius R k))), g x = 0 :=
      ae_restrict_of_ae_restrict_of_subset
        (euclideanBall_mono (dyadicRadius_pos hR k).le hk) hg
    have hL' : Tendsto (fun n => ∫ x in euclideanBall (0 : Vec d) R,
        (S.G n).toH1Function.toFun x * g x) atTop
        (𝓝 (∫ x in euclideanBall (0 : Vec d) R, G x * g x)) := by
      simp_rw [integral_eq_integral_diff_of_ae_zero hgk]
      have h1 := hGklim k g (hg2.mono_measure (Measure.restrict_mono (hTB k) le_rfl))
      have h2 : ∫ x in T k, Gk k x * g x = ∫ x in T k, G x * g x := by
        refine integral_congr_ae ?_
        filter_upwards [hGT k] with x hx
        rw [hx]
      rw [h2] at h1
      exact h1
    rw [← tendsto_nhds_unique hL hL']
    exact hvL v hv

end ApproxSetting

end PDE.Ch4Green
