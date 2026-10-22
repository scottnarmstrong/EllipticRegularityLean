module

public import PDEFoundation.Measure.L2CoverGluing

/-!
# Finite-cover root-center gluing

Every member of the cover meets the root either directly or through one
intermediate member. The overlap and piece volumes control the change of
center in the squared integral.
-/

@[expose] public section

namespace PDE

open MeasureTheory

variable {X ι : Type*} [MeasurableSpace X] [DecidableEq ι]
variable {μ : Measure X}

private theorem setIntegral_biUnion_le_sum_of_nonneg
    (t : Finset ι) {s : ι → Set X} {f : X → ℝ}
    (hInt : ∀ i ∈ t, IntegrableOn f (s i) μ)
    (hf : ∀ x, 0 ≤ f x) :
    ∫ x in ⋃ i ∈ t, s i, f x ∂μ ≤
      ∑ i ∈ t, ∫ x in s i, f x ∂μ := by
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hit ih =>
    have hi : IntegrableOn f (s i) μ := hInt i (Finset.mem_insert_self i t)
    have ht : ∀ j ∈ t, IntegrableOn f (s j) μ := by
      intro j hj
      exact hInt j (Finset.mem_insert_of_mem hj)
    rw [Finset.set_biUnion_insert, Finset.sum_insert hit]
    exact (setIntegral_union_le_of_nonneg hi
      (integrableOn_finset_iUnion.mpr ht) hf).trans (by
        gcongr
        exact ih ht)

/-- A finite-cover integral of a nonnegative function is bounded by the
sum of its integrals on the cover members. -/
theorem setIntegral_le_sum_of_finset_cover
    (t : Finset ι) {S : Set X} {s : ι → Set X} {f : X → ℝ}
    (hcover : S ⊆ ⋃ i ∈ t, s i)
    (hInt : ∀ i ∈ t, IntegrableOn f (s i) μ)
    (hf : ∀ x, 0 ≤ f x) :
    ∫ x in S, f x ∂μ ≤ ∑ i ∈ t, ∫ x in s i, f x ∂μ := by
  calc
    ∫ x in S, f x ∂μ ≤ ∫ x in ⋃ i ∈ t, s i, f x ∂μ := by
      apply setIntegral_mono_set (integrableOn_finset_iUnion.mpr hInt)
      · exact Filter.Eventually.of_forall hf
      · exact Filter.Eventually.of_forall hcover
    _ ≤ ∑ i ∈ t, ∫ x in s i, f x ∂μ :=
      setIntegral_biUnion_le_sum_of_nonneg t hInt hf

/-- A root-centered `L²` bound for a finite cover with paths of length at
most two in its positive-overlap graph. -/
theorem setIntegral_sq_sub_le_root_center_finset
    (t : Finset ι) (root : ι) {S : Set X} {s : ι → Set X}
    {u : X → ℝ} {c : ι → ℝ} {V M m : ℝ}
    (hroot : root ∈ t)
    (hcover : S ⊆ ⋃ i ∈ t, s i)
    (hMeas : ∀ i ∈ t, MeasurableSet (s i))
    (hFinite : ∀ i ∈ t, μ (s i) ≠ ⊤)
    (hInt : ∀ i ∈ t, IntegrableOn (fun x => (u x - c i) ^ 2) (s i) μ)
    (hIntRoot : ∀ i ∈ t,
      IntegrableOn (fun x => (u x - c root) ^ 2) (s i) μ)
    (hm : 0 < m)
    (hVolume : ∀ i ∈ t, μ.real (s i) ≤ M)
    (hVariance : ∀ i ∈ t,
      (∫ x in s i, (u x - c i) ^ 2 ∂μ) ≤ V)
    (hPaths : ∀ i ∈ t,
      i = root ∨ m ≤ μ.real (s root ∩ s i) ∨
        ∃ j ∈ t,
          m ≤ μ.real (s root ∩ s j) ∧
          m ≤ μ.real (s j ∩ s i)) :
    ∫ x in S, (u x - c root) ^ 2 ∂μ ≤
      (t.card : ℝ) * (2 * V + 32 * M * V / m) := by
  have hVnonneg : 0 ≤ V :=
    (integral_nonneg_of_ae (Filter.Eventually.of_forall fun x =>
      sq_nonneg (u x - c root))).trans (hVariance root hroot)
  have hMnonneg : 0 ≤ M :=
    measureReal_nonneg.trans (hVolume root hroot)
  have hPair (i j : ι) (hi : i ∈ t) (hj : j ∈ t)
      (hij : m ≤ μ.real (s i ∩ s j)) :
      (c i - c j) ^ 2 ≤ 4 * V / m := by
    have hTop : μ (s i ∩ s j) ≠ ⊤ :=
      measure_ne_top_of_subset Set.inter_subset_left (hFinite i hi)
    have hBound := overlap_center_distance_sq_le_of_local_bounds
      (u := u) (s := s i) (t := s j) (c := c i) (d := c j)
      (V := V) (W := V) (m := m)
      (hInt i hi) (hInt j hj)
      ((hMeas i hi).inter (hMeas j hj)) hTop hij
      (hVariance i hi) (hVariance j hj)
    have hDiv := overlap_center_distance_sq_le_of_integral_bound hBound hm
    convert hDiv using 1; ring
  have hCenter (i : ι) (hi : i ∈ t) :
      (c i - c root) ^ 2 ≤ 16 * V / m := by
    rcases hPaths i hi with hir | hDirect | ⟨j, hj, hRootJ, hJI⟩
    · subst i
      simp only [sub_self, pow_two, zero_mul]
      exact div_nonneg (mul_nonneg (by norm_num) hVnonneg) hm.le
    · have h := hPair root i hroot hi hDirect
      rw [sub_sq_comm] at h
      calc
        (c i - c root) ^ 2 ≤ 4 * V / m := h
        _ ≤ 16 * V / m := by
          apply div_le_div_of_nonneg_right _ hm.le
          linarith only [hVnonneg]
    · have h1 := hPair root j hroot hj hRootJ
      have h2 := hPair j i hj hi hJI
      rw [sub_sq_comm] at h1 h2
      calc
        (c i - c root) ^ 2 ≤
            2 * (c i - c j) ^ 2 + 2 * (c j - c root) ^ 2 :=
          sq_sub_le_two_sq_sub_add_two_sq (c i) (c j) (c root)
        _ ≤ 2 * (4 * V / m) + 2 * (4 * V / m) := by gcongr
        _ = 16 * V / m := by ring
  have hEach (i : ι) (hi : i ∈ t) :
      (∫ x in s i, (u x - c root) ^ 2 ∂μ) ≤
        2 * V + 32 * M * V / m := by
    have hChange := setIntegral_sq_sub_le_change_center
      (hInt i hi) (hIntRoot i hi) (hFinite i hi)
    have hProd : μ.real (s i) * (c i - c root) ^ 2 ≤
        M * (16 * V / m) :=
      mul_le_mul (hVolume i hi) (hCenter i hi)
        (sq_nonneg _) hMnonneg
    calc
      _ ≤ 2 * (∫ x in s i, (u x - c i) ^ 2 ∂μ) +
          2 * μ.real (s i) * (c i - c root) ^ 2 := hChange
      _ ≤ 2 * V + 2 * M * (16 * V / m) := by
        nlinarith only [hVariance i hi, hProd]
      _ = 2 * V + 32 * M * V / m := by ring
  calc
    ∫ x in S, (u x - c root) ^ 2 ∂μ ≤
        ∑ i ∈ t, ∫ x in s i, (u x - c root) ^ 2 ∂μ :=
      setIntegral_le_sum_of_finset_cover t hcover hIntRoot
        (fun x => sq_nonneg (u x - c root))
    _ ≤ ∑ _i ∈ t, (2 * V + 32 * M * V / m) :=
      Finset.sum_le_sum hEach
    _ = (t.card : ℝ) * (2 * V + 32 * M * V / m) := by simp; ring

end PDE
