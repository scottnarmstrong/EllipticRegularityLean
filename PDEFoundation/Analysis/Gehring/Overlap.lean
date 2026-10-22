module

public import PDEFoundation.Analysis.Gehring.Whitney

/-!
# Bounded overlap of the dilated Whitney cubes

If `x` lies in the closed dilates `σ Q` (`σ = s ∈ ℕ`, `s ≥ 1`) of selected cubes, these cubes
live on at most three consecutive dyadic scales, and on each scale at most `(s+1)^d` lattice
cubes can occur, so there are at most `3 (s+1)^d` of them.
-/

@[expose] public section

namespace PDE.Gehring

open Set MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- The number of cubes of a fixed dyadic scale whose closed `s`-dilate contains `x` is at
most `(s+1)^d`. -/
theorem card_scale_le {s : ℕ} (F : Finset (ℤ × (Fin d → ℤ))) (x : Vec d) (j : ℤ)
    (hx : ∀ q ∈ F, x ∈ closedCenteredAxisCube (dyadicCenter q.1 q.2) ((s : ℝ) * 2 ^ q.1 / 2)) :
    (F.filter fun q => q.1 = j).card ≤ (s + 1) ^ d := by
  classical
  have hp := dyadicSide_pos j
  let a : Fin d → ℤ := fun i => ⌈x i / 2 ^ j - 1 / 2 - s / 2⌉
  let b : Fin d → ℤ := fun i => ⌊x i / 2 ^ j - 1 / 2 - s / 2 + s⌋
  have hmaps : ∀ q ∈ F.filter (fun q => q.1 = j), q.2 ∈ Fintype.piFinset (fun i => Finset.Icc (a i) (b i)) := by
    intro q hq
    rw [Finset.mem_filter] at hq
    obtain ⟨hqF, hqj⟩ := hq
    rw [Fintype.mem_piFinset]
    intro i
    have h := hx q hqF i (mem_univ i)
    simp only [dyadicCenter, mem_Icc, hqj] at h
    rw [Finset.mem_Icc]
    constructor
    · apply Int.ceil_le.2
      have : (x i / 2 ^ j - 1 / 2 - s / 2) * 2 ^ j ≤ q.2 i * 2 ^ j := by
        have e : (x i / 2 ^ j - 1 / 2 - s / 2) * 2 ^ j = x i - (1 / 2 + s / 2) * 2 ^ j := by
          field_simp
          ring
        rw [e]; nlinarith [h.1, h.2]
      exact le_of_mul_le_mul_right this hp
    · apply Int.le_floor.2
      have : (q.2 i : ℝ) * 2 ^ j ≤ (x i / 2 ^ j - 1 / 2 - s / 2 + s) * 2 ^ j := by
        have e : (x i / 2 ^ j - 1 / 2 - s / 2 + s) * 2 ^ j = x i + (s / 2 - 1 / 2) * 2 ^ j := by
          field_simp
          ring
        rw [e]; nlinarith [h.1, h.2]
      exact le_of_mul_le_mul_right this hp
  calc (F.filter fun q => q.1 = j).card
      ≤ (Fintype.piFinset (fun i => Finset.Icc (a i) (b i))).card := by
        refine Finset.card_le_card_of_injOn (fun q => q.2) hmaps ?_
        intro q hq q' hq' h
        simp only [Finset.coe_filter, mem_ofPred_eq] at hq hq'
        exact Prod.ext (hq.2.trans hq'.2.symm) h
    _ = ∏ i, (Finset.Icc (a i) (b i)).card := Fintype.card_piFinset _
    _ ≤ ∏ _i : Fin d, (s + 1) := by
        refine Finset.prod_le_prod fun i _ => ?_
        rw [Int.card_Icc]
        have h1 : b i = ⌊x i / 2 ^ j - 1 / 2 - s / 2⌋ + s := by
          simp only [b]; rw [Int.floor_add_natCast]
        have h2 : ⌊x i / 2 ^ j - 1 / 2 - s / 2⌋ ≤ a i := Int.floor_le_ceil _
        omega
    _ = (s + 1) ^ d := by simp

/-- **Bounded overlap (core count).** A finite set of dyadic cubes, each admissible for `E`
with dyadic parent non-admissible and each having `x` in its closed `s`-dilate, has at most
`3 (s+1)^d` elements. -/
theorem card_le_of_overlap {E : Set (Vec d)} {s : ℕ} (hs : 1 ≤ s)
    (F : Finset (ℤ × (Fin d → ℤ))) (x : Vec d)
    (hadm : ∀ q ∈ F, WAdm E s q)
    (hout : ∀ q ∈ F, ∃ y ∈ closedCenteredAxisCube (dyadicCenter q.1 q.2)
      ((4 * (s : ℝ) + 1) * 2 ^ q.1 / 2), y ∉ E)
    (hx : ∀ q ∈ F, x ∈ closedCenteredAxisCube (dyadicCenter q.1 q.2) ((s : ℝ) * 2 ^ q.1 / 2)) :
    F.card ≤ 3 * (s + 1) ^ d := by
  classical
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  -- ratio bound
  have hratio : ∀ q1 ∈ F, ∀ q2 ∈ F, q2.1 ≤ q1.1 + 2 := by
    intro q1 h1 q2 h2
    by_contra hcon
    push Not at hcon
    obtain ⟨y, hy, hyE⟩ := hout q1 h1
    have hyn : y ∉ closedCenteredAxisCube (dyadicCenter q2.1 q2.2) ((s : ℝ) * 2 ^ q2.1) :=
      fun h => hyE (hadm q2 h2 h)
    simp only [closedCenteredAxisCube, mem_pi, mem_univ, forall_true_left, mem_Icc, not_forall,
      not_and_or, not_le] at hyn
    obtain ⟨i, hi⟩ := hyn
    have a1 := hy i (mem_univ i)
    have a2 := hx q1 h1 i (mem_univ i)
    have a3 := hx q2 h2 i (mem_univ i)
    simp only [mem_Icc] at a1 a2 a3
    have hp1 := dyadicSide_pos q1.1
    have hp2 := dyadicSide_pos q2.1
    have h8 : (8 : ℝ) * 2 ^ q1.1 ≤ 2 ^ q2.1 := by
      have : (2 : ℝ) ^ (q1.1 + 3) ≤ 2 ^ q2.1 := dyadicSide_le_of_le (by omega)
      rw [zpow_add₀ (by norm_num)] at this
      norm_num at this
      linarith
    rcases hi with hi | hi <;>
      nlinarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]
  -- minimal scale
  set n0 := (F.image Prod.fst).min' (hF.image _) with hn0
  have hmin : ∀ q ∈ F, n0 ≤ q.1 := fun q hq =>
    Finset.min'_le _ _ (Finset.mem_image_of_mem _ hq)
  obtain ⟨q0, hq0F, hq0⟩ : ∃ q0 ∈ F, q0.1 = n0 := by
    have := Finset.min'_mem (F.image Prod.fst) (hF.image _)
    simpa using this
  have hcov : F ⊆ (Finset.Icc n0 (n0 + 2)).biUnion (fun j => F.filter fun q => q.1 = j) := by
    intro q hq
    rw [Finset.mem_biUnion]
    refine ⟨q.1, ?_, Finset.mem_filter.2 ⟨hq, rfl⟩⟩
    rw [Finset.mem_Icc]
    exact ⟨hmin q hq, by have := hratio q0 hq0F q hq; omega⟩
  calc F.card ≤ ((Finset.Icc n0 (n0 + 2)).biUnion (fun j => F.filter fun q => q.1 = j)).card :=
        Finset.card_le_card hcov
    _ ≤ ∑ j ∈ Finset.Icc n0 (n0 + 2), (F.filter fun q => q.1 = j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ Finset.Icc n0 (n0 + 2), (s + 1) ^ d :=
        Finset.sum_le_sum fun j _ => card_scale_le F x j hx
    _ = 3 * (s + 1) ^ d := by
        rw [Finset.sum_const, Int.card_Icc, smul_eq_mul]
        congr 1
        omega

namespace WhitneyCover

variable {E : Set (Vec d)} {σ : ℝ} (W : WhitneyCover E σ)

/-- Distinct indices of a Whitney cover carry distinct dyadic cubes. -/
theorem key_injective : Function.Injective fun i : W.ι => (W.scale i, W.index i) := by
  intro i j hij
  by_contra hne
  have hd : Disjoint (dyadicCube (W.scale i) (W.index i))
      (dyadicCube (W.scale j) (W.index j)) := W.cube_disjoint hne
  simp only [Prod.mk.injEq] at hij
  obtain ⟨h1, h2⟩ := hij
  have hm : dyadicCenter (W.scale i) (W.index i) ∈ dyadicCube (W.scale i) (W.index i) := by
    intro k
    simp only [dyadicCenter]
    have := dyadicSide_pos (W.scale i)
    constructor <;> nlinarith
  rw [← h1, ← h2] at hd
  exact Set.disjoint_left.1 hd hm hm

/-- **Lemma 4.6** (finite form). For every finite subfamily `S`,
`∑_{i ∈ S} 1_{σ Q_i} ≤ N_σ = 3 (σ+1)^d` pointwise. -/
theorem sum_indicator_dilate_le (hσ : σ = 2 ∨ σ = 4) (S : Finset W.ι) (x : Vec d) :
    ∑ i ∈ S, (W.dilate σ i).indicator (fun _ => (1 : ℝ)) x ≤ 3 * (σ + 1) ^ d := by
  classical
  obtain ⟨s, hs1, hsσ⟩ : ∃ s : ℕ, 1 ≤ s ∧ σ = (s : ℝ) := by
    rcases hσ with h | h
    · exact ⟨2, by norm_num, by simp [h]⟩
    · exact ⟨4, by norm_num, by simp [h]⟩
  subst hsσ
  set T := S.filter (fun i => x ∈ W.dilate (s:ℝ) i) with hT
  have hsum : ∑ i ∈ S, (W.dilate (s:ℝ) i).indicator (fun _ => (1 : ℝ)) x = (T.card : ℝ) := by
    simp only [Set.indicator_apply, hT, Finset.sum_boole]
  have hcard : T.card ≤ 3 * (s + 1) ^ d := by
    have himg : (T.image fun i => (W.scale i, W.index i)).card = T.card :=
      Finset.card_image_of_injective _ W.key_injective
    rw [← himg]
    refine card_le_of_overlap (E := E) hs1 _ x ?_ ?_ ?_
    · intro q hq
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hq
      have := W.closedDilate_subset i
      exact this
    · intro q hq
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hq
      have := W.exists_not_mem i
      exact this
    · intro q hq
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hq
      have hxi : x ∈ W.dilate (s:ℝ) i := (Finset.mem_filter.1 hi).2
      intro k _
      have h := hxi k (mem_univ k)
      simp only [center, side, mem_Icc] at h ⊢
      exact ⟨h.1.le, h.2.le⟩
  rw [hsum]
  exact_mod_cast hcard

/-- **Lemma 4.6** (subfamily form, `ℝ≥0∞`-valued). For every subfamily `T`,
`∑_{i ∈ T} 1_{σ Q_i}(x) ≤ N_σ = 3 (σ+1)^d`. -/
theorem tsum_indicator_dilate_le (hσ : σ = 2 ∨ σ = 4) (T : Set W.ι) (x : Vec d) :
    ∑' i : T, (W.dilate σ i).indicator (fun _ => (1 : ℝ≥0∞)) x ≤
      ENNReal.ofReal (3 * (σ + 1) ^ d) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun S => ?_
  have h := W.sum_indicator_dilate_le hσ (S.map (Function.Embedding.subtype _)) x
  rw [Finset.sum_map] at h
  have : ∑ i ∈ S, (W.dilate σ i).indicator (fun _ => (1 : ℝ≥0∞)) x =
      ENNReal.ofReal (∑ i ∈ S, (W.dilate σ i).indicator (fun _ => (1 : ℝ)) x) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hx : x ∈ W.dilate σ i <;> simp [hx]
  simp only [Function.Embedding.coe_subtype] at h
  rw [this]
  exact ENNReal.ofReal_le_ofReal h

end WhitneyCover

end PDE.Gehring
