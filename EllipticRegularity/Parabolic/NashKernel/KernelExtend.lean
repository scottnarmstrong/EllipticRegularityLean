module

public import EllipticRegularity.Parabolic.NashKernel.KernelExtendBasic

/-!
# Representation of an `L¹` operator by its dyadic kernel

`PDE.NashKernelExtend.kernel_represents`: let `P` be a jointly measurable kernel with
`0 ≤ P ≤ M`, and `Tf` an a.e.-additive, a.e.-homogeneous operator on `L¹(Vec d)` with
`|Tf f| ≤ M ‖f‖₁` a.e. (`LinearBounded`).  If `∫_Q P(x, y) dy = Tf(1_Q)(x)` a.e. for every dyadic
cube `Q`, then `Tf f = ∫ P(·, y) f(y) dy` a.e. for every integrable `f`.

Route: a Dynkin (`π`-`λ`) argument from the dyadic cubes (which generate the Borel `σ`-algebra) to
all measurable sets of finite measure, using the closure of agreement under finite sums,
complements, monotone unions (the `L¹` limit lemma) and the exhaustion of `Vec d` by finite
windows; then `Integrable.induction` to all integrable `f`.
-/

@[expose] public section

namespace PDE.NashKernelExtend

open MeasureTheory Set Filter Topology PDE.NashKernelDyadic

variable {d : ℕ} {M : ℝ} {P : PDE.Vec d → PDE.Vec d → ℝ}
  {Tf : (PDE.Vec d → ℝ) → PDE.Vec d → ℝ}

theorem integrable_indicator_one {s : Set (PDE.Vec d)} (hs : MeasurableSet s)
    (hfin : volume s < ⊤) : Integrable (s.indicator fun _ => (1 : ℝ)) :=
  (integrableOn_const (C := (1 : ℝ)) hfin.ne).integrable_indicator hs

theorem kerOp_indicator_one {s : Set (PDE.Vec d)} (hs : MeasurableSet s) (x : PDE.Vec d) :
    kerOp P (s.indicator fun _ => (1 : ℝ)) x = ∫ y in s, P x y := by
  rw [kerOp, ← integral_indicator hs]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  by_cases hy : y ∈ s <;> simp [hy]

theorem agree_cube {T : ℕ → (Fin d → ℤ) → PDE.Vec d → ℝ}
    (hP : ∀ n k, ∀ᵐ x, ∫ y in cube n k, P x y = T n k x)
    (hcube : ∀ n k, Tf ((cube n k).indicator fun _ => (1 : ℝ)) =ᵐ[volume] T n k) (n : ℕ)
    (k : Fin d → ℤ) : Agree P Tf ((cube n k).indicator fun _ => (1 : ℝ)) := by
  filter_upwards [hcube n k, hP n k] with x h1 h2
  rw [h1, kerOp_indicator_one (measurableSet_cube n k), h2]

theorem agree_win {T : ℕ → (Fin d → ℤ) → PDE.Vec d → ℝ}
    (hPm : Measurable (Function.uncurry P)) (hPb : ∀ x y, 0 ≤ P x y ∧ P x y ≤ M)
    (hL : LinearBounded M Tf)
    (hP : ∀ n k, ∀ᵐ x, ∫ y in cube n k, P x y = T n k x)
    (hcube : ∀ n k, Tf ((cube n k).indicator fun _ => (1 : ℝ)) =ᵐ[volume] T n k)
    (F : Finset (Fin d → ℤ)) : Agree P Tf ((win F).indicator fun _ => (1 : ℝ)) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    have : (win (∅ : Finset (Fin d → ℤ))) = ∅ := by simp [win]
    rw [this, Set.indicator_empty']
    exact agree_zero hL
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
    exact agree_add hPm hPb hL
      (integrable_indicator_one (measurableSet_win F) (volume_win_lt_top F))
      (integrable_indicator_one (measurableSet_cube 0 k) (volume_cube_lt_top 0 k))
      ih (agree_cube hP hcube 0 k)

/-- Monotone limits of finite-measure sets preserve agreement. -/
theorem agree_indicator_of_monotone {A : Set (PDE.Vec d)} {An : ℕ → Set (PDE.Vec d)}
    (hPm : Measurable (Function.uncurry P)) (hPb : ∀ x y, 0 ≤ P x y ∧ P x y ≤ M)
    (hL : LinearBounded M Tf) (hA : MeasurableSet A) (hAfin : volume A < ⊤)
    (hAn : ∀ N, MeasurableSet (An N)) (hmono : Monotone An) (hU : ⋃ N, An N = A)
    (h : ∀ N, Agree P Tf ((An N).indicator fun _ => (1 : ℝ))) :
    Agree P Tf (A.indicator fun _ => (1 : ℝ)) := by
  have hsub : ∀ N, An N ⊆ A := fun N => hU ▸ subset_iUnion An N
  have hint : ∀ N, Integrable ((An N).indicator fun _ => (1 : ℝ)) := fun N =>
    integrable_indicator_one (hAn N) ((measure_mono (hsub N)).trans_lt hAfin)
  refine agree_of_tendsto hPm hPb hL (integrable_indicator_one hA hAfin) hint ?_ h
  have := tendsto_integral_of_dominated_convergence (μ := (volume : Measure (PDE.Vec d)))
    (F := fun N y => |(An N).indicator (fun _ => (1 : ℝ)) y - A.indicator (fun _ => (1 : ℝ)) y|)
    (f := fun _ => (0 : ℝ)) (A.indicator fun _ => (1 : ℝ))
    (fun N => ((hint N).sub (integrable_indicator_one hA hAfin)).abs.aestronglyMeasurable)
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

theorem agree_inter_win {T : ℕ → (Fin d → ℤ) → PDE.Vec d → ℝ}
    (hPm : Measurable (Function.uncurry P)) (hPb : ∀ x y, 0 ≤ P x y ∧ P x y ≤ M)
    (hL : LinearBounded M Tf)
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
    exact agree_zero hL
  · rintro t ⟨n, k, rfl⟩ F
    rcases cube_subset_win_or_disjoint (n := n) k F with h | h
    · rw [inter_eq_left.mpr h]; exact agree_cube hP hcube n k
    · rw [h.inter_eq, Set.indicator_empty']; exact agree_zero hL
  · intro t ht ih F
    have hW := agree_win hPm hPb hL hP hcube F
    have hfin : ∀ r : Set (PDE.Vec d), MeasurableSet r →
        Integrable ((r ∩ win F).indicator fun _ => (1 : ℝ)) := fun r hr =>
      integrable_indicator_one (hr.inter (measurableSet_win F))
        ((measure_mono inter_subset_right).trans_lt (volume_win_lt_top F))
    have h := agree_sub hPm hPb hL
      (integrable_indicator_one (measurableSet_win F) (volume_win_lt_top F)) (hfin t ht) hW (ih F)
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
    have hAnfin : ∀ N, Integrable ((An N).indicator fun _ => (1 : ℝ)) := fun N =>
      integrable_indicator_one (hAnm N) ((measure_mono (iUnion₂_subset fun i _ =>
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
        rw [this, Set.indicator_empty']; exact agree_zero hL
      | succ N ihN =>
        have hd : Disjoint (An N) (g N) := by
          simp only [hAn, Set.disjoint_iUnion_left]
          intro i hi
          exact hgd (Nat.ne_of_lt hi)
        rw [hsucc N, Set.indicator_union_of_disjoint hd]
        exact agree_add hPm hPb hL (hAnfin N)
          (integrable_indicator_one (hgm N)
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
    exact agree_indicator_of_monotone hPm hPb hL
      ((MeasurableSet.iUnion hfm).inter (measurableSet_win F))
      ((measure_mono inter_subset_right).trans_lt (volume_win_lt_top F)) hAnm hmono hU hagree

theorem agree_indicator_one {T : ℕ → (Fin d → ℤ) → PDE.Vec d → ℝ}
    (hPm : Measurable (Function.uncurry P)) (hPb : ∀ x y, 0 ≤ P x y ∧ P x y ≤ M)
    (hL : LinearBounded M Tf)
    (hP : ∀ n k, ∀ᵐ x, ∫ y in cube n k, P x y = T n k x)
    (hcube : ∀ n k, Tf ((cube n k).indicator fun _ => (1 : ℝ)) =ᵐ[volume] T n k)
    {s : Set (PDE.Vec d)} (hs : MeasurableSet s) (hfin : volume s < ⊤) :
    Agree P Tf (s.indicator fun _ => (1 : ℝ)) := by
  refine agree_indicator_of_monotone (An := fun N => s ∩ win (box (d := d) N)) hPm hPb hL hs hfin
    (fun N => hs.inter (measurableSet_win _)) ?_ ?_
    (fun N => agree_inter_win hPm hPb hL hP hcube hs _)
  · intro N M' h
    exact inter_subset_inter_right _ (fun y hy => by
      simp only [win, mem_preimage, Finset.mem_coe] at hy ⊢
      exact monotone_box h hy)
  · rw [← Set.inter_iUnion, iUnion_win_box, inter_univ]

/-- **Representation by the dyadic kernel.** -/
theorem kernel_represents {T : ℕ → (Fin d → ℤ) → PDE.Vec d → ℝ}
    (hPm : Measurable (Function.uncurry P)) (hPb : ∀ x y, 0 ≤ P x y ∧ P x y ≤ M)
    (hL : LinearBounded M Tf)
    (hP : ∀ n k, ∀ᵐ x, ∫ y in cube n k, P x y = T n k x)
    (hcube : ∀ n k, Tf ((cube n k).indicator fun _ => (1 : ℝ)) =ᵐ[volume] T n k)
    {f : PDE.Vec d → ℝ} (hf : Integrable f) :
    Tf f =ᵐ[volume] fun x => ∫ y, P x y * f y := by
  have h1 : ∀ (c : ℝ) ⦃s : Set (PDE.Vec d)⦄, MeasurableSet s → volume s < ⊤ →
      Agree P Tf (s.indicator fun _ => c) := by
    intro c s hs hfin
    have e : (s.indicator fun _ => c) = c • s.indicator fun _ => (1 : ℝ) := by
      funext y; by_cases hy : y ∈ s <;> simp [hy]
    rw [e]
    exact agree_smul hL c (integrable_indicator_one hs hfin)
      (agree_indicator_one hPm hPb hL hP hcube hs hfin)
  have h2 : ∀ ⦃f g : PDE.Vec d → ℝ⦄, Disjoint (Function.support f) (Function.support g) → Integrable f →
      Integrable g → Agree P Tf f → Agree P Tf g → Agree P Tf (f + g) :=
    fun f g _ hf hg a b => agree_add hPm hPb hL hf hg a b
  have h3 : IsClosed {g : Lp ℝ 1 (volume : Measure (PDE.Vec d)) | Agree P Tf g} := by
    refine IsSeqClosed.isClosed fun u g hu hg => ?_
    refine agree_of_tendsto hPm hPb hL (L1.integrable_coeFn g)
      (fun n => L1.integrable_coeFn (u n)) ?_ hu
    refine (tendsto_iff_norm_sub_tendsto_zero.mp hg).congr fun n => ?_
    rw [L1.norm_eq_integral_norm]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (u n) g] with y hy
    rw [hy, Real.norm_eq_abs]
    simp
  have h4 : ∀ ⦃f g : PDE.Vec d → ℝ⦄, f =ᵐ[volume] g → Integrable f → Agree P Tf f →
      Agree P Tf g := fun f g hfg hf a => agree_congr_ae hL hfg hf a
  exact Integrable.induction (Agree P Tf) h1 h2 h3 h4 hf

end PDE.NashKernelExtend
