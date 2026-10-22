module

public import EllipticRegularity.Parabolic.NashKernel.KernelDomain
public import EllipticRegularity.Parabolic.NashKernel.KernelLimitAE

/-!
# Representation on `L¹ ∩ L²` by the dyadic kernel

`kernel_representsD`: the analogue of `kernel_represents` for an operator that is only controlled on
`L¹ ∩ L²`.  After agreement on indicators (`agreeD_indicator_one`), the extension to `L¹ ∩ L²`
runs through `Integrable.induction` on the *truncations* `trunc N f = 1_{win N} · clamp_N f`, which
are bounded with finite-measure support (hence in the domain), and then lets `N → ∞` in `L¹`.
-/

@[expose] public section

namespace PDE.NashKernelExtend

open MeasureTheory Set Filter Topology PDE.NashKernelDyadic

variable {d : ℕ} {M : ℝ} {P : PDE.Vec d → PDE.Vec d → ℝ}
  {Tf : (PDE.Vec d → ℝ) → PDE.Vec d → ℝ}

/-- Clamping to `[-N, N]`. -/
def clampN (N : ℕ) (z : ℝ) : ℝ := max (-(N : ℝ)) (min z N)

theorem continuous_clampN (N : ℕ) : Continuous (clampN N) := by
  unfold clampN; fun_prop

theorem clampN_zero (N : ℕ) : clampN N 0 = 0 := by simp [clampN]

theorem abs_clampN_le (N : ℕ) (z : ℝ) : |clampN N z| ≤ N := by
  have h : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  unfold clampN
  rw [abs_le]
  refine ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

theorem abs_clampN_sub_le (N : ℕ) (a b : ℝ) : |clampN N a - clampN N b| ≤ |a - b| := by
  have h : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  unfold clampN
  rw [abs_le]
  have h1 := abs_le.mp (le_refl |a - b|)
  rcases le_total a b with hab | hab
  · have e1 : min a N ≤ min b N := min_le_min_right _ hab
    have e2 : max (-(N : ℝ)) (min a N) ≤ max (-(N : ℝ)) (min b N) := max_le_max le_rfl e1
    have e3 : min b N - min a N ≤ b - a := by
      rcases le_total b N with hb | hb
      · rw [min_eq_left hb, min_eq_left (hab.trans hb)]
      · rcases le_total a N with ha | ha
        · rw [min_eq_right hb, min_eq_left ha]; linarith
        · rw [min_eq_right hb, min_eq_right ha]; linarith
    have e4 : max (-(N : ℝ)) (min b N) - max (-(N : ℝ)) (min a N) ≤ min b N - min a N := by
      rcases le_total (min a N) (-(N : ℝ)) with ha | ha
      · rw [max_eq_left ha]
        rcases le_total (min b N) (-(N : ℝ)) with hb | hb
        · rw [max_eq_left hb]; linarith
        · rw [max_eq_right hb]; linarith
      · rw [max_eq_right ha, max_eq_right (ha.trans e1)]
    constructor <;> linarith [abs_nonneg (a - b), abs_of_nonpos (sub_nonpos.2 hab), neg_abs_le (a - b)]
  · have e1 : min b N ≤ min a N := min_le_min_right _ hab
    have e2 : max (-(N : ℝ)) (min b N) ≤ max (-(N : ℝ)) (min a N) := max_le_max le_rfl e1
    have e3 : min a N - min b N ≤ a - b := by
      rcases le_total a N with ha | ha
      · rw [min_eq_left ha, min_eq_left (hab.trans ha)]
      · rcases le_total b N with hb | hb
        · rw [min_eq_right ha, min_eq_left hb]; linarith
        · rw [min_eq_right ha, min_eq_right hb]; linarith
    have e4 : max (-(N : ℝ)) (min a N) - max (-(N : ℝ)) (min b N) ≤ min a N - min b N := by
      rcases le_total (min b N) (-(N : ℝ)) with hb | hb
      · rw [max_eq_left hb]
        rcases le_total (min a N) (-(N : ℝ)) with ha | ha
        · rw [max_eq_left ha]; linarith
        · rw [max_eq_right ha]; linarith
      · rw [max_eq_right hb, max_eq_right (hb.trans e1)]
    constructor <;> linarith [abs_nonneg (a - b), abs_of_nonneg (sub_nonneg.2 hab), le_abs_self (a - b)]

theorem abs_clampN_sub_self_le (N : ℕ) (z : ℝ) : |clampN N z - z| ≤ |z| := by
  have h : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h1 := le_abs_self z
  have h2 := neg_abs_le z
  rw [abs_le]
  unfold clampN
  rcases le_total z N with hz | hz
  · rw [min_eq_left hz]
    rcases le_total (-(N : ℝ)) z with hz' | hz'
    · rw [max_eq_right hz']; constructor <;> linarith
    · rw [max_eq_left hz']; constructor <;> linarith
  · rw [min_eq_right hz, max_eq_right (by linarith)]; constructor <;> linarith

theorem clampN_eq_self {N : ℕ} {z : ℝ} (h : |z| ≤ N) : clampN N z = z := by
  rw [abs_le] at h
  simp [clampN, min_eq_left h.2, max_eq_right h.1]

/-- The truncation of `f` to the window `box N` and the heights `[-N, N]`. -/
noncomputable def trunc (N : ℕ) (f : PDE.Vec d → ℝ) : PDE.Vec d → ℝ :=
  (win (box (d := d) N)).indicator fun y => clampN N (f y)

theorem dom_trunc (N : ℕ) {f : PDE.Vec d → ℝ} (hf : AEStronglyMeasurable f volume) :
    Dom (trunc N f) := by
  have hm : AEStronglyMeasurable (fun y => clampN N (f y)) volume :=
    (continuous_clampN N).comp_aestronglyMeasurable hf
  have : IsFiniteMeasure (volume.restrict (win (box (d := d) N))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact volume_win_lt_top _⟩
  have h2 : MemLp (trunc N f) 2 volume := by
    unfold trunc
    rw [memLp_indicator_iff_restrict (measurableSet_win _)]
    exact MemLp.of_bound (hm.restrict) (N : ℝ) (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs]; exact abs_clampN_le N _)
  refine ⟨?_, h2⟩
  have h1 : MemLp (trunc N f) 1 volume := by
    unfold trunc
    rw [memLp_indicator_iff_restrict (measurableSet_win _)]
    exact MemLp.of_bound (hm.restrict) (N : ℝ) (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs]; exact abs_clampN_le N _)
  exact memLp_one_iff_integrable.mp h1

theorem abs_trunc_sub_le (N : ℕ) (f g : PDE.Vec d → ℝ) (y : PDE.Vec d) :
    |trunc N f y - trunc N g y| ≤ |f y - g y| := by
  unfold trunc
  by_cases hy : y ∈ win (box (d := d) N)
  · simp only [Set.indicator_of_mem hy]
    exact abs_clampN_sub_le N _ _
  · simp [Set.indicator_of_notMem hy]

theorem abs_trunc_sub_self_le (N : ℕ) (f : PDE.Vec d → ℝ) (y : PDE.Vec d) :
    |trunc N f y - f y| ≤ |f y| := by
  unfold trunc
  by_cases hy : y ∈ win (box (d := d) N)
  · simp only [Set.indicator_of_mem hy]
    exact abs_clampN_sub_self_le N _
  · simp [Set.indicator_of_notMem hy]

theorem trunc_eventually_eq (f : PDE.Vec d → ℝ) (y : PDE.Vec d) :
    ∀ᶠ N : ℕ in atTop, trunc N f y = f y := by
  have hy : y ∈ ⋃ N, win (box (d := d) N) := by rw [iUnion_win_box]; trivial
  obtain ⟨N₀, hN₀⟩ := mem_iUnion.mp hy
  obtain ⟨N₁, hN₁⟩ := exists_nat_ge |f y|
  filter_upwards [eventually_ge_atTop (max N₀ N₁)] with N hN
  have hw : y ∈ win (box (d := d) N) := monotone_box ((le_max_left _ _).trans hN) hN₀
  have hb : |f y| ≤ N := hN₁.trans (by exact_mod_cast (le_max_right _ _).trans hN)
  unfold trunc
  rw [Set.indicator_of_mem hw]
  exact clampN_eq_self hb

variable {T : ℕ → (Fin d → ℤ) → PDE.Vec d → ℝ}

/-- **Representation by the dyadic kernel on `L¹ ∩ L²`.** -/
theorem kernel_representsD
    (hPm : Measurable (Function.uncurry P)) (hPb : ∀ x y, 0 ≤ P x y ∧ P x y ≤ M)
    (hL : LinearBoundedD M Tf)
    (hP : ∀ n k, ∀ᵐ x, ∫ y in cube n k, P x y = T n k x)
    (hcube : ∀ n k, Tf ((cube n k).indicator fun _ => (1 : ℝ)) =ᵐ[volume] T n k)
    {f : PDE.Vec d → ℝ} (hf : Dom f) :
    Tf f =ᵐ[volume] fun x => ∫ y, P x y * f y := by
  let C : (PDE.Vec d → ℝ) → Prop := fun g => ∀ N : ℕ, Agree P Tf (trunc N g)
  have h1 : ∀ (c : ℝ) ⦃s : Set (PDE.Vec d)⦄, MeasurableSet s → volume s < ⊤ →
      C (s.indicator fun _ => c) := by
    intro c s hs hfin N
    have e : trunc N (s.indicator fun _ => c) =
        clampN N c • (s ∩ win (box (d := d) N)).indicator fun _ => (1 : ℝ) := by
      funext y
      unfold trunc
      by_cases h1 : y ∈ s <;> by_cases h2 : y ∈ win (box (d := d) N) <;>
        simp [h1, h2, clampN_zero]
    rw [e]
    exact agreeD_smul hL _ (dom_indicator_one (hs.inter (measurableSet_win _))
      ((measure_mono inter_subset_right).trans_lt (volume_win_lt_top _)))
      (agreeD_inter_win hPm hPb hL hP hcube hs _)
  have h2 : ∀ ⦃f g : PDE.Vec d → ℝ⦄, Disjoint (Function.support f) (Function.support g) →
      Integrable f → Integrable g → C f → C g → C (f + g) := by
    intro f g hd hf hg a b N
    have e : trunc N (f + g) = trunc N f + trunc N g := by
      funext y
      unfold trunc
      by_cases hy : y ∈ win (box (d := d) N)
      · simp only [Set.indicator_of_mem hy, Pi.add_apply]
        have : f y = 0 ∨ g y = 0 := by
          by_contra hc
          push Not at hc
          exact Set.disjoint_left.mp hd hc.1 hc.2
        rcases this with h | h <;> simp [h, clampN_zero]
      · simp [Set.indicator_of_notMem hy]
    rw [e]
    exact agreeD_add hPm hPb hL (dom_trunc N hf.aestronglyMeasurable)
      (dom_trunc N hg.aestronglyMeasurable) (a N) (b N)
  have h3 : IsClosed {g : Lp ℝ 1 (volume : Measure (PDE.Vec d)) | C g} := by
    refine IsSeqClosed.isClosed fun u g hu hg => ?_
    intro N
    refine agreeD_of_tendsto hPm hPb hL (dom_trunc N (L1.integrable_coeFn g).aestronglyMeasurable)
      (fun n => dom_trunc N (L1.integrable_coeFn (u n)).aestronglyMeasurable) ?_ (fun n => hu n N)
    have hlim : Tendsto (fun n => ∫ y, |u n y - g y|) atTop (𝓝 0) := by
      refine (tendsto_iff_norm_sub_tendsto_zero.mp hg).congr fun n => ?_
      rw [L1.norm_eq_integral_norm]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub (u n) g] with y hy
      rw [hy, Real.norm_eq_abs]
      simp
    refine squeeze_zero (fun n => integral_nonneg fun y => abs_nonneg _) (fun n => ?_) hlim
    have hI : ∀ n, Integrable (fun y => |u n y - g y|) volume := fun n =>
      ((L1.integrable_coeFn (u n)).sub (L1.integrable_coeFn g)).abs
    refine integral_mono ?_ (hI n) (fun y => abs_trunc_sub_le N _ _ y)
    exact ((dom_trunc N (L1.integrable_coeFn (u n)).aestronglyMeasurable).1.sub
      (dom_trunc N (L1.integrable_coeFn g).aestronglyMeasurable).1).abs
  have h4 : ∀ ⦃f g : PDE.Vec d → ℝ⦄, f =ᵐ[volume] g → Integrable f → C f → C g := by
    intro f g hfg hf a N
    have hfg' : trunc N f =ᵐ[volume] trunc N g := by
      filter_upwards [hfg] with y hy
      unfold trunc
      by_cases hw : y ∈ win (box (d := d) N)
      · simp [Set.indicator_of_mem hw, hy]
      · simp [Set.indicator_of_notMem hw]
    exact agreeD_congr_ae hL hfg' (dom_trunc N hf.aestronglyMeasurable) (a N)
  have hC : C f := Integrable.induction C h1 h2 h3 h4 hf.1
  refine agreeD_of_tendsto hPm hPb hL hf (fun N => dom_trunc N hf.1.aestronglyMeasurable) ?_ hC
  have := tendsto_integral_of_dominated_convergence (μ := (volume : Measure (PDE.Vec d)))
    (F := fun N y => |trunc N f y - f y|) (f := fun _ => (0 : ℝ)) (fun y => |f y|)
    (fun N => ((dom_trunc N hf.1.aestronglyMeasurable).1.sub hf.1).abs.aestronglyMeasurable)
    hf.1.abs
    (fun N => ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_abs]; exact abs_trunc_sub_self_le N f y)
    (ae_of_all _ fun y => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [trunc_eventually_eq f y] with N hN
      simp [hN])
  simpa using this

/-- Abstract kernel and representation for an operator on `L¹ ∩ L²`. -/
theorem exists_kernel_representationD {M : ℝ} (hM : 0 ≤ M)
    {T : ℕ → (Fin d → ℤ) → PDE.Vec d → ℝ} (hT : ∀ n k, AEMeasurable (T n k) volume)
    (hbd : ∀ n k, ∀ᵐ x, 0 ≤ T n k x ∧ T n k x ≤ M * (volume (cube n k)).toReal)
    (hadd : ∀ n k, ∀ᵐ x, T n k x = ∑ ε : Fin d → Bool, T (n + 1) (child k ε) x)
    {Tf : (PDE.Vec d → ℝ) → PDE.Vec d → ℝ} (hL : LinearBoundedD M Tf)
    (hcube : ∀ n k, Tf ((cube n k).indicator fun _ => (1 : ℝ)) =ᵐ[volume] T n k) :
    ∃ P : PDE.Vec d → PDE.Vec d → ℝ, Measurable (Function.uncurry P) ∧
      (∀ x y, 0 ≤ P x y ∧ P x y ≤ M) ∧
      ∀ f : PDE.Vec d → ℝ, Dom f → Tf f =ᵐ[volume] fun x => ∫ y, P x y * f y := by
  obtain ⟨P, hPm, hPb, hP⟩ := PDE.NashKernelLimit.exists_kernel_of_aemeasurable hM hT hbd hadd
  exact ⟨P, hPm, hPb, fun f hf => kernel_representsD hPm hPb hL hP hcube hf⟩

end PDE.NashKernelExtend
