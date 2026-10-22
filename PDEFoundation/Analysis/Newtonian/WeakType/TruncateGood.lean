module

public import PDEFoundation.Analysis.Newtonian.WeakType.DecompositionGoodBadL1
public import PDEFoundation.Analysis.Newtonian.WeakType.MollifyConverge

/-!
# Truncating the Calderón–Zygmund decomposition to finitely many bad cubes

For a finite set `s` of stopping cubes put `g_s = F - ∑_{k ∈ s} b_k`.  It equals `g` on the cubes
of `s` and off all cubes, and equals `F` on the remaining cubes, so
`‖g_s‖₂² ≤ ‖g‖₂² + ‖F‖_∞² · |⋃_{k ∉ s} Q_k|`.
-/

@[expose] public section

open BoxIntegral MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PDE.NewtonWeakType

noncomputable section

variable {d : ℕ} {I : Box (Fin d)} {F : Vec d → Vec d} {lam : ℝ}

/-- The truncated good part `F - ∑_{k ∈ s} b_k`. -/
def czTrunc (S : CZStopping I F lam) (s : Finset S.ι) (x : Vec d) : Vec d :=
  F x - ∑ k ∈ s, czBad S k x

variable (S : CZStopping I F lam)

theorem vbdd_czBad (hF : VBdd F) (k : S.ι) : VBdd (czBad S k) := by
  intro i
  rw [czBad_coord_eq_indicator]
  obtain ⟨C, hC⟩ := (hF i).bdd
  obtain ⟨R, hR⟩ := ((S.cube k).isBounded_Icc).subset_closedBall (0 : Vec d)
  refine ⟨((hF i).meas.sub_const _).indicator (S.cube k).measurableSet_coe,
    ⟨C + |czAvg S k i|, fun x => ?_⟩, ⟨R + 1, fun x hx => ?_⟩⟩
  · by_cases hxc : x ∈ (S.cube k : Set (Vec d))
    · rw [Set.indicator_of_mem hxc]
      exact (abs_sub _ _).trans (add_le_add (hC x) le_rfl)
    · rw [Set.indicator_of_notMem hxc]
      simpa using (abs_nonneg _).trans (hC 0) |>.trans (le_add_of_nonneg_right (abs_nonneg _))
  · refine Set.indicator_of_notMem (fun hxc => ?_) _
    have := hR (BoxIntegral.Box.coe_subset_Icc hxc)
    have h2 : ‖x‖ ≤ R := by simpa using this
    linarith

theorem vbdd_czTrunc (hF : VBdd F) (s : Finset S.ι) : VBdd (czTrunc S s) := by
  have := (hF.sub (VBdd.finsetSum s fun k _ => vbdd_czBad S hF k))
  exact this

/-- The union of the cubes outside `s`. -/
def czTail (s : Finset S.ι) : Set (Vec d) := ⋃ k : {k // k ∉ s}, (S.cube k : Set (Vec d))

theorem measurableSet_czTail (s : Finset S.ι) : MeasurableSet (czTail S s) :=
  MeasurableSet.iUnion fun k => (S.cube k).measurableSet_coe

theorem volume_czTail_le (s : Finset S.ι) :
    volume (czTail S s) ≤ ∑' k : {k // k ∉ s}, volume (S.cube k : Set (Vec d)) :=
  measure_iUnion_le _

theorem vecNormSq_czTrunc_le (s : Finset S.ι) (x : Vec d) :
    vecNormSq (czTrunc S s x) ≤ vecNormSq (czGood S x) +
      (czTail S s).indicator (fun x => vecNormSq (F x)) x := by
  have hnn : 0 ≤ (czTail S s).indicator (fun x => vecNormSq (F x)) x :=
    Set.indicator_nonneg (fun _ _ => vecNormSq_nonneg _) x
  by_cases h : ∃ j, x ∈ (S.cube j : Set (Vec d))
  · obtain ⟨j, hj⟩ := h
    have hz : ∀ k, k ≠ j → czBad S k x = 0 := fun k hk =>
      czBad_of_notMem S (fun hx' => Set.disjoint_left.mp (S.pairwise_disjoint hk) hx' hj)
    by_cases hjs : j ∈ s
    · have : czTrunc S s x = czGood S x := by
        unfold czTrunc
        rw [Finset.sum_eq_single_of_mem j hjs (fun k _ hk => hz k hk), czBad_of_mem S hj,
          czGood_of_mem S hj]
        abel
      rw [this]; linarith
    · have h0 : ∑ k ∈ s, czBad S k x = 0 :=
        Finset.sum_eq_zero fun k hk => hz k (fun hkj => hjs (hkj ▸ hk))
      have : czTrunc S s x = F x := by unfold czTrunc; rw [h0, sub_zero]
      have hxT : x ∈ czTail S s := Set.mem_iUnion.mpr ⟨⟨j, hjs⟩, hj⟩
      rw [this, Set.indicator_of_mem hxT]
      linarith [vecNormSq_nonneg (czGood S x)]
  · have hn : ∀ k, x ∉ (S.cube k : Set (Vec d)) := not_exists.mp h
    have h0 : ∑ k ∈ s, czBad S k x = 0 := Finset.sum_eq_zero fun k _ => czBad_of_notMem S (hn k)
    have : czTrunc S s x = czGood S x := by
      unfold czTrunc; rw [h0, sub_zero, czGood_of_notMem S hn]
    rw [this]; linarith

variable {S}

/-- The `L²` bound for the truncated good part. -/
theorem lintegral_vecNormSq_czTrunc_le (hFm : Measurable F)
    (hF : ∀ i, IntegrableOn (fun x => F x i) (I : Set (Vec d)))
    (hFsupp : ∀ x, x ∉ (I : Set (Vec d)) → F x = 0)
    {M2 : ℝ} (hM2 : ∀ x, vecNormSq (F x) ≤ M2) (s : Finset S.ι) :
    ∫⁻ x, ENNReal.ofReal (vecNormSq (czTrunc S s x)) ≤
      ENNReal.ofReal (2 ^ d * lam) *
          (∫⁻ x in (I : Set (Vec d)), ENNReal.ofReal (vecEuclideanNorm (F x))) +
        ENNReal.ofReal M2 * ∑' k : {k // k ∉ s}, volume (S.cube k : Set (Vec d)) := by
  have hmeasind : Measurable ((czTail S s).indicator (fun x => ENNReal.ofReal (vecNormSq (F x)))) := by
    refine Measurable.indicator ?_ (measurableSet_czTail S s)
    refine ENNReal.measurable_ofReal.comp ?_
    simp_rw [vecNormSq_eq_sum_sq]
    exact Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp hFm).pow_const 2
  have hpt : ∀ x, ENNReal.ofReal (vecNormSq (czTrunc S s x)) ≤
      ENNReal.ofReal (vecNormSq (czGood S x)) +
        (czTail S s).indicator (fun x => ENNReal.ofReal (vecNormSq (F x))) x := by
    intro x
    have h := vecNormSq_czTrunc_le S s x
    calc ENNReal.ofReal (vecNormSq (czTrunc S s x))
        ≤ ENNReal.ofReal (vecNormSq (czGood S x) +
            (czTail S s).indicator (fun x => vecNormSq (F x)) x) := ENNReal.ofReal_le_ofReal h
      _ = ENNReal.ofReal (vecNormSq (czGood S x)) +
            ENNReal.ofReal ((czTail S s).indicator (fun x => vecNormSq (F x)) x) :=
          ENNReal.ofReal_add (vecNormSq_nonneg _)
            (Set.indicator_nonneg (fun _ _ => vecNormSq_nonneg _) x)
      _ = _ := by
          congr 1
          by_cases hx : x ∈ czTail S s
          · simp [Set.indicator_of_mem hx]
          · simp [Set.indicator_of_notMem hx]
  have hgood : ∫⁻ x, ENNReal.ofReal (vecNormSq (czGood S x)) ≤
      ENNReal.ofReal (2 ^ d * lam) *
        ∫⁻ x in (I : Set (Vec d)), ENNReal.ofReal (vecEuclideanNorm (F x)) := by
    refine le_trans (le_of_eq ?_) (lintegral_vecNormSq_czGood_le (S := S) hF)
    symm
    refine setLIntegral_eq_of_support_subset ?_
    intro x hx
    by_contra hxI
    apply hx
    have hn : ∀ k, x ∉ (S.cube k : Set (Vec d)) := fun k hk => hxI (S.le_root k hk)
    simp [czGood_of_notMem S hn, hFsupp x hxI, vecNormSq, vecDot]
  have htail : ∫⁻ x, (czTail S s).indicator (fun x => ENNReal.ofReal (vecNormSq (F x))) x ≤
      ENNReal.ofReal M2 * ∑' k : {k // k ∉ s}, volume (S.cube k : Set (Vec d)) := by
    rw [lintegral_indicator (measurableSet_czTail S s)]
    calc ∫⁻ x in czTail S s, ENNReal.ofReal (vecNormSq (F x))
        ≤ ∫⁻ _ in czTail S s, ENNReal.ofReal M2 :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hM2 x)
      _ = ENNReal.ofReal M2 * volume (czTail S s) := by rw [setLIntegral_const, mul_comm]
      _ ≤ _ := mul_le_mul_right (volume_czTail_le S s) _
  calc ∫⁻ x, ENNReal.ofReal (vecNormSq (czTrunc S s x))
      ≤ ∫⁻ x, (ENNReal.ofReal (vecNormSq (czGood S x)) +
          (czTail S s).indicator (fun x => ENNReal.ofReal (vecNormSq (F x))) x) :=
        lintegral_mono hpt
    _ ≤ _ := (lintegral_add_right _ hmeasind).trans_le (add_le_add hgood htail)

end

end PDE.NewtonWeakType
