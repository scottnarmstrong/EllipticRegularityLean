module

public import EllipticRegularity.Parabolic.NashKernel.KernelDomainBasic
public import EllipticRegularity.Parabolic.NashKernel.KernelExtend

/-!
# Dyadic-cube agreement on `L¹ ∩ L²`

The Dynkin argument of `KernelExtend` for an operator defined on `L¹ ∩ L²` only: agreement on
indicators of finite-measure measurable sets (`agreeD_indicator_one`).
-/

@[expose] public section

namespace PDE.NashKernelExtend

open MeasureTheory Set Filter Topology PDE.NashKernelDyadic

variable {d : ℕ} {M : ℝ} {P : PDE.Vec d → PDE.Vec d → ℝ}
  {Tf : (PDE.Vec d → ℝ) → PDE.Vec d → ℝ}

theorem agreeD_cube {T : ℕ → (Fin d → ℤ) → PDE.Vec d → ℝ}
    (hP : ∀ n k, ∀ᵐ x, ∫ y in cube n k, P x y = T n k x)
    (hcube : ∀ n k, Tf ((cube n k).indicator fun _ => (1 : ℝ)) =ᵐ[volume] T n k) (n : ℕ)
    (k : Fin d → ℤ) : Agree P Tf ((cube n k).indicator fun _ => (1 : ℝ)) := by
  filter_upwards [hcube n k, hP n k] with x h1 h2
  rw [h1, kerOp_indicator_one (measurableSet_cube n k), h2]

theorem agreeD_win {T : ℕ → (Fin d → ℤ) → PDE.Vec d → ℝ}
    (hPm : Measurable (Function.uncurry P)) (hPb : ∀ x y, 0 ≤ P x y ∧ P x y ≤ M)
    (hL : LinearBoundedD M Tf)
    (hP : ∀ n k, ∀ᵐ x, ∫ y in cube n k, P x y = T n k x)
    (hcube : ∀ n k, Tf ((cube n k).indicator fun _ => (1 : ℝ)) =ᵐ[volume] T n k)
    (F : Finset (Fin d → ℤ)) : Agree P Tf ((win F).indicator fun _ => (1 : ℝ)) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    have : (win (∅ : Finset (Fin d → ℤ))) = ∅ := by simp [win]
    rw [this, Set.indicator_empty']
    exact agreeD_zero hL
  | insert k F hk ih =>
    have hu : win (insert k F) = win F ∪ cube 0 k := by
      ext y
      simp only [win, mem_preimage, Finset.coe_insert, mem_insert_iff, mem_union, mem_cube_iff,
        Finset.mem_coe]
      tauto
    have hd : Disjoint (win F) (cube 0 k) := by
      refine Set.disjoint_left.mpr fun y hy hy' => hk ?_
      have := mem_cube_iff.mp hy'
      simp only [win, mem_preimage, Finset.mem_coe] at hy
      rwa [this] at hy
    rw [hu, Set.indicator_union_of_disjoint hd]
    exact agreeD_add hPm hPb hL
      (dom_indicator_one (measurableSet_win F) (volume_win_lt_top F))
      (dom_indicator_one (measurableSet_cube 0 k) (volume_cube_lt_top 0 k))
      ih (agreeD_cube hP hcube 0 k)

/-- Monotone limits of finite-measure sets preserve agreement. -/
theorem agreeD_indicator_of_monotone {A : Set (PDE.Vec d)} {An : ℕ → Set (PDE.Vec d)}
    (hPm : Measurable (Function.uncurry P)) (hPb : ∀ x y, 0 ≤ P x y ∧ P x y ≤ M)
    (hL : LinearBoundedD M Tf) (hA : MeasurableSet A) (hAfin : volume A < ⊤)
    (hAn : ∀ N, MeasurableSet (An N)) (hmono : Monotone An) (hU : ⋃ N, An N = A)
    (h : ∀ N, Agree P Tf ((An N).indicator fun _ => (1 : ℝ))) :
    Agree P Tf (A.indicator fun _ => (1 : ℝ)) := by
  have hsub : ∀ N, An N ⊆ A := fun N => hU ▸ subset_iUnion An N
  have hint : ∀ N, Dom ((An N).indicator fun _ => (1 : ℝ)) := fun N =>
    dom_indicator_one (hAn N) ((measure_mono (hsub N)).trans_lt hAfin)
  refine agreeD_of_tendsto hPm hPb hL (dom_indicator_one hA hAfin) hint ?_ h
  have := tendsto_integral_of_dominated_convergence (μ := (volume : Measure (PDE.Vec d)))
    (F := fun N y => |(An N).indicator (fun _ => (1 : ℝ)) y - A.indicator (fun _ => (1 : ℝ)) y|)
    (f := fun _ => (0 : ℝ)) (A.indicator fun _ => (1 : ℝ))
    (fun N => ((hint N).1.sub (integrable_indicator_one hA hAfin)).abs.aestronglyMeasurable)
    (integrable_indicator_one hA hAfin)
    (fun N => ae_of_all _ fun y => by
      by_cases hy : y ∈ A
      · by_cases hy' : y ∈ An N <;> simp [hy, hy']
      · have : y ∉ An N := fun h' => hy (hsub N h')
        simp [hy, this])
    (ae_of_all _ fun y => by
      by_cases hy : y ∈ A
      · rw [← hU, mem_iUnion] at hy
        obtain ⟨N, hN⟩ := hy
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop N] with n hn
        have := hmono hn hN
        have hyA : y ∈ A := hsub n this
        simp [this, hyA]
      · have : ∀ N, y ∉ An N := fun N h' => hy (hsub N h')
        simp [hy, this])
  simpa using this

theorem agreeD_inter_win {T : ℕ → (Fin d → ℤ) → PDE.Vec d → ℝ}
    (hPm : Measurable (Function.uncurry P)) (hPb : ∀ x y, 0 ≤ P x y ∧ P x y ≤ M)
    (hL : LinearBoundedD M Tf)
    (hP : ∀ n k, ∀ᵐ x, ∫ y in cube n k, P x y = T n k x)
    (hcube : ∀ n k, Tf ((cube n k).indicator fun _ => (1 : ℝ)) =ᵐ[volume] T n k)
    {s : Set (PDE.Vec d)} (hs : MeasurableSet s) (F : Finset (Fin d → ℤ)) :
    Agree P Tf ((s ∩ win F).indicator fun _ => (1 : ℝ)) := by
  revert F
  have hmeq : (inferInstance : MeasurableSpace (PDE.Vec d)) =
      MeasurableSpace.generateFrom {s : Set (PDE.Vec d) | ∃ n k, s = cube n k} :=
    (BorelSpace.measurable_eq (α := PDE.Vec d)).trans borel_eq_generateFrom_cubes
  refine MeasurableSpace.induction_on_inter
    (C := fun s _ => ∀ F : Finset (Fin d → ℤ),
      Agree P Tf ((s ∩ win F).indicator fun _ => (1 : ℝ))) hmeq isPiSystem_cubes ?_ ?_ ?_ ?_ s hs
  · intro F
    rw [Set.empty_inter, Set.indicator_empty']
    exact agreeD_zero hL
  · rintro t ⟨n, k, rfl⟩ F
    rcases cube_subset_win_or_disjoint (n := n) k F with h | h
    · rw [inter_eq_left.mpr h]; exact agreeD_cube hP hcube n k
    · rw [h.inter_eq, Set.indicator_empty']; exact agreeD_zero hL
  · intro t ht ih F
    have hW := agreeD_win hPm hPb hL hP hcube F
    have hfin : ∀ r : Set (PDE.Vec d), MeasurableSet r →
        Dom ((r ∩ win F).indicator fun _ => (1 : ℝ)) := fun r hr =>
      dom_indicator_one (hr.inter (measurableSet_win F))
        ((measure_mono inter_subset_right).trans_lt (volume_win_lt_top F))
    have h := agreeD_sub hPm hPb hL
      (dom_indicator_one (measurableSet_win F) (volume_win_lt_top F)) (hfin t ht) hW (ih F)
    have e : (tᶜ ∩ win F).indicator (fun _ => (1 : ℝ)) =
        (win F).indicator (fun _ => (1 : ℝ)) - (t ∩ win F).indicator fun _ => (1 : ℝ) := by
      funext y
      by_cases h1 : y ∈ t <;> by_cases h2 : y ∈ win F <;> simp [h1, h2]
    rw [e]; exact h
  · intro f hdisj hfm ih F
    set g : ℕ → Set (PDE.Vec d) := fun i => f i ∩ win F with hg
    have hgm : ∀ i, MeasurableSet (g i) := fun i => (hfm i).inter (measurableSet_win F)
    have hgd : Pairwise (Function.onFun Disjoint g) := fun i j hij =>
      (hdisj hij).mono inter_subset_left inter_subset_left
    set An : ℕ → Set (PDE.Vec d) := fun N => ⋃ i, ⋃ (_ : i < N), g i with hAn
    have hAnm : ∀ N, MeasurableSet (An N) := fun N =>
      MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hgm i
    have hAnfin : ∀ N, Dom ((An N).indicator fun _ => (1 : ℝ)) := fun N =>
      dom_indicator_one (hAnm N) ((measure_mono (iUnion₂_subset fun i _ =>
        inter_subset_right)).trans_lt (volume_win_lt_top F))
    have hsucc : ∀ N, An (N + 1) = An N ∪ g N := by
      intro N
      ext y
      simp only [hAn, mem_iUnion, mem_union, exists_prop]
      constructor
      · rintro ⟨i, hi, hy⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
        · exact Or.inl ⟨i, h, hy⟩
        · exact Or.inr (h ▸ hy)
      · rintro (⟨i, hi, hy⟩ | hy)
        · exact ⟨i, Nat.lt_succ_of_lt hi, hy⟩
        · exact ⟨N, Nat.lt_succ_self N, hy⟩
    have hagree : ∀ N, Agree P Tf ((An N).indicator fun _ => (1 : ℝ)) := by
      intro N
      induction N with
      | zero =>
        have : An 0 = ∅ := by simp [hAn]
        rw [this, Set.indicator_empty']; exact agreeD_zero hL
      | succ N ihN =>
        have hd : Disjoint (An N) (g N) := by
          simp only [hAn, Set.disjoint_iUnion_left]
          intro i hi
          exact hgd (Nat.ne_of_lt hi)
        rw [hsucc N, Set.indicator_union_of_disjoint hd]
        exact agreeD_add hPm hPb hL (hAnfin N)
          (dom_indicator_one (hgm N)
            ((measure_mono inter_subset_right).trans_lt (volume_win_lt_top F)))
          ihN (ih N F)
    have hmono : Monotone An := monotone_nat_of_le_succ fun N => by
      rw [hsucc N]; exact subset_union_left
    have hU : ⋃ N, An N = (⋃ i, f i) ∩ win F := by
      rw [Set.iUnion_inter]
      ext y
      simp only [hAn, mem_iUnion, exists_prop]
      constructor
      · rintro ⟨N, i, _, hy⟩; exact ⟨i, hy⟩
      · rintro ⟨i, hy⟩; exact ⟨i + 1, i, Nat.lt_succ_self i, hy⟩
    exact agreeD_indicator_of_monotone hPm hPb hL
      ((MeasurableSet.iUnion hfm).inter (measurableSet_win F))
      ((measure_mono inter_subset_right).trans_lt (volume_win_lt_top F)) hAnm hmono hU hagree

theorem agreeD_indicator_one {T : ℕ → (Fin d → ℤ) → PDE.Vec d → ℝ}
    (hPm : Measurable (Function.uncurry P)) (hPb : ∀ x y, 0 ≤ P x y ∧ P x y ≤ M)
    (hL : LinearBoundedD M Tf)
    (hP : ∀ n k, ∀ᵐ x, ∫ y in cube n k, P x y = T n k x)
    (hcube : ∀ n k, Tf ((cube n k).indicator fun _ => (1 : ℝ)) =ᵐ[volume] T n k)
    {s : Set (PDE.Vec d)} (hs : MeasurableSet s) (hfin : volume s < ⊤) :
    Agree P Tf (s.indicator fun _ => (1 : ℝ)) := by
  refine agreeD_indicator_of_monotone (An := fun N => s ∩ win (box (d := d) N)) hPm hPb hL hs hfin
    (fun N => hs.inter (measurableSet_win _)) ?_ ?_
    (fun N => agreeD_inter_win hPm hPb hL hP hcube hs _)
  · intro N M' h
    exact inter_subset_inter_right _ (fun y hy => by
      simp only [win, mem_preimage, Finset.mem_coe] at hy ⊢
      exact monotone_box h hy)
  · rw [← Set.inter_iUnion, iUnion_win_box, inter_univ]


end PDE.NashKernelExtend
