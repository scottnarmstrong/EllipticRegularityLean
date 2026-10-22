module

public import EllipticRegularity.Ch4.Meyers.Integrability

/-!
# Non-integrability of `s^{-e}` for `e ≥ 1` in the planar case

Dyadic decomposition of a cube into the shells `box k \ box (k+1)`, on each of which the
integral of `s^{-e}` is bounded below by a positive constant independent of `k`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4Meyers

open MeasureTheory Set

variable {d : ℕ} {w : Fin d → ℝ}

/-- Planar weights: `w` is `1` exactly at `i0` and `i1`. -/
theorem axisSq_planar {i0 i1 : Fin d} (hi : i0 ≠ i1) (h0 : w i0 = 1) (h1 : w i1 = 1)
    (hrest : ∀ j, j ≠ i0 → j ≠ i1 → w j = 0) (x : Vec d) :
    axisSq w x = x i0 ^ 2 + x i1 ^ 2 := by
  unfold axisSq
  rw [Finset.sum_eq_add i0 i1 hi]
  · simp [h0, h1]
  · intro c _ hc; simp [hrest c hc.1 hc.2]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The dyadic boxes: half-side `τ` in the coordinates `i0, i1` and `c` elsewhere. -/
def dyadicBox (i0 i1 : Fin d) (τ c : ℝ) : Set (Vec d) :=
  Set.pi univ fun j => Icc (-(if j = i0 ∨ j = i1 then τ else c)) (if j = i0 ∨ j = i1 then τ else c)

theorem measurableSet_dyadicBox (i0 i1 : Fin d) (τ c : ℝ) : MeasurableSet (dyadicBox i0 i1 τ c) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

/-- Number of coordinates other than `i0, i1`. -/
noncomputable def numOther (i0 i1 : Fin d) : ℕ :=
  (Finset.univ.filter fun j : Fin d => ¬(j = i0 ∨ j = i1)).card

theorem volume_dyadicBox {i0 i1 : Fin d} (hi : i0 ≠ i1) {τ c : ℝ} (hτ : 0 ≤ τ) (hc : 0 ≤ c) :
    volume (dyadicBox i0 i1 τ c) = ENNReal.ofReal ((2 * τ) ^ 2 * (2 * c) ^ numOther i0 i1) := by
  unfold dyadicBox
  rw [volume_pi_pi]
  simp_rw [Real.volume_Icc]
  have h1 : ∀ j : Fin d, ENNReal.ofReal ((if j = i0 ∨ j = i1 then τ else c) -
      -(if j = i0 ∨ j = i1 then τ else c)) =
      ENNReal.ofReal (if j = i0 ∨ j = i1 then 2 * τ else 2 * c) := by
    intro j; split_ifs <;> congr 1 <;> ring
  simp_rw [h1]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => by split_ifs <;> positivity)]
  congr 1
  classical
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have : (Finset.univ.filter fun j : Fin d => j = i0 ∨ j = i1) = {i0, i1} := by
    ext j; simp
  rw [this, Finset.card_pair hi]
  rfl

theorem dyadicBox_mono (i0 i1 : Fin d) {τ τ' : ℝ} (h : τ' ≤ τ) (c : ℝ) :
    dyadicBox i0 i1 τ' c ⊆ dyadicBox i0 i1 τ c := by
  intro x hx j _
  have := hx j (mem_univ j)
  simp only [mem_Icc] at this ⊢
  split_ifs at this ⊢ with hj
  · constructor <;> linarith [this.1, this.2]
  · exact this

theorem dyadicBox_coord_abs_le {i0 i1 : Fin d} {τ c : ℝ} (hτ : τ ≤ c) {x : Vec d}
    (hx : x ∈ dyadicBox i0 i1 τ c) (j : Fin d) : |x j| ≤ c := by
  have := hx j (mem_univ j)
  simp only [mem_Icc] at this
  rw [abs_le]
  split_ifs at this
  · constructor <;> linarith [this.1, this.2]
  · exact ⟨this.1, this.2⟩

theorem dyadicBox_special_abs_le {i0 i1 : Fin d} {τ c : ℝ} {x : Vec d}
    (hx : x ∈ dyadicBox i0 i1 τ c) : |x i0| ≤ τ ∧ |x i1| ≤ τ := by
  have h0 := hx i0 (mem_univ i0)
  have h1 := hx i1 (mem_univ i1)
  simp only [mem_Icc, true_or, or_true, ite_true] at h0 h1
  exact ⟨abs_le.mpr h0, abs_le.mpr h1⟩

theorem shell_special_lt {i0 i1 : Fin d} {τ τ' c : ℝ} (hτc : τ ≤ c) {x : Vec d}
    (hx : x ∈ dyadicBox i0 i1 τ c) (hx' : x ∉ dyadicBox i0 i1 τ' c) :
    τ' < |x i0| ∨ τ' < |x i1| := by
  by_contra hcon
  simp only [not_or, not_lt] at hcon
  apply hx'
  intro j _
  simp only [mem_Icc]
  split_ifs with hj
  · rcases hj with rfl | rfl
    · exact abs_le.mp hcon.1
    · exact abs_le.mp hcon.2
  · exact abs_le.mp (dyadicBox_coord_abs_le hτc hx j)

theorem real_shell_lower {e : ℝ} (he : 1 ≤ e) {τ c M : ℝ} (hτ : 0 < τ) (hτc : τ ≤ c)
    (hM : 0 ≤ M) :
    3 * M * 2 ^ (-e) * (c ^ 2) ^ (1 - e) ≤ (2 * τ ^ 2) ^ (-e) * (3 * τ ^ 2 * M) := by
  have hτ2 : 0 < τ ^ 2 := by positivity
  have h1 : (2 * τ ^ 2) ^ (-e) = 2 ^ (-e) * (τ ^ 2) ^ (-e) :=
    Real.mul_rpow (by norm_num) hτ2.le
  have h2 : (τ ^ 2) ^ (-e) * τ ^ 2 = (τ ^ 2) ^ (1 - e) := by
    have := Real.rpow_add hτ2 (1 : ℝ) (-e)
    rw [Real.rpow_one] at this
    rw [sub_eq_add_neg, this]; ring
  have h3 : (c ^ 2) ^ (1 - e) ≤ (τ ^ 2) ^ (1 - e) :=
    Real.rpow_le_rpow_of_nonpos hτ2 (by nlinarith) (by linarith)
  have h4 : 0 ≤ (2 : ℝ) ^ (-e) := by positivity
  calc 3 * M * 2 ^ (-e) * (c ^ 2) ^ (1 - e)
      = (3 * M * 2 ^ (-e)) * (c ^ 2) ^ (1 - e) := by ring
    _ ≤ (3 * M * 2 ^ (-e)) * (τ ^ 2) ^ (1 - e) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (2 * τ ^ 2) ^ (-e) * (3 * τ ^ 2 * M) := by
        rw [h1, ← h2]; ring

/-- The lower bound of `∫ s^{-e}` over a dyadic shell. -/
theorem shell_lintegral_lower {i0 i1 : Fin d} (hi : i0 ≠ i1)
    (h0 : w i0 = 1) (h1 : w i1 = 1) (hrest : ∀ j, j ≠ i0 → j ≠ i1 → w j = 0)
    {e : ℝ} (he : 1 ≤ e) {τ c : ℝ} (hτ : 0 < τ) (hτc : τ ≤ c) :
    ENNReal.ofReal (3 * (2 * c) ^ numOther i0 i1 * 2 ^ (-e) * (c ^ 2) ^ (1 - e)) ≤
      ∫⁻ x in dyadicBox i0 i1 τ c \ dyadicBox i0 i1 (τ / 2) c,
        ENNReal.ofReal (axisSq w x ^ (-e)) := by
  have hc : 0 < c := lt_of_lt_of_le hτ hτc
  set M : ℝ := (2 * c) ^ numOther i0 i1 with hMdef
  have hM : 0 ≤ M := by positivity
  have hsub : dyadicBox i0 i1 (τ / 2) c ⊆ dyadicBox i0 i1 τ c :=
    dyadicBox_mono i0 i1 (by linarith) c
  have hvol : volume (dyadicBox i0 i1 τ c \ dyadicBox i0 i1 (τ / 2) c) =
      ENNReal.ofReal (3 * τ ^ 2 * M) := by
    rw [measure_sdiff hsub (measurableSet_dyadicBox _ _ _ _).nullMeasurableSet
      (by rw [volume_dyadicBox hi (by linarith) hc.le]; exact ENNReal.ofReal_ne_top),
      volume_dyadicBox hi hτ.le hc.le, volume_dyadicBox hi (by linarith) hc.le,
      ← ENNReal.ofReal_sub _ (by positivity)]
    congr 1
    ring
  have hmeas : MeasurableSet (dyadicBox i0 i1 τ c \ dyadicBox i0 i1 (τ / 2) c) :=
    (measurableSet_dyadicBox _ _ _ _).diff (measurableSet_dyadicBox _ _ _ _)
  calc ENNReal.ofReal (3 * M * 2 ^ (-e) * (c ^ 2) ^ (1 - e))
      ≤ ENNReal.ofReal ((2 * τ ^ 2) ^ (-e) * (3 * τ ^ 2 * M)) :=
        ENNReal.ofReal_le_ofReal (real_shell_lower he hτ hτc hM)
    _ = ENNReal.ofReal ((2 * τ ^ 2) ^ (-e)) *
          volume (dyadicBox i0 i1 τ c \ dyadicBox i0 i1 (τ / 2) c) := by
        rw [hvol, ← ENNReal.ofReal_mul (by positivity)]
    _ = ∫⁻ x in dyadicBox i0 i1 τ c \ dyadicBox i0 i1 (τ / 2) c,
          ENNReal.ofReal ((2 * τ ^ 2) ^ (-e)) := by
        rw [setLIntegral_const]
    _ ≤ _ := by
        refine setLIntegral_mono' hmeas fun x hx => ?_
        refine ENNReal.ofReal_le_ofReal ?_
        obtain ⟨hx1, hx2⟩ := hx
        have hsp := axisSq_planar hi h0 h1 hrest x
        obtain ⟨a0, a1⟩ := dyadicBox_special_abs_le hx1
        have hpos : 0 < axisSq w x := by
          rcases shell_special_lt hτc hx1 hx2 with h | h
          · have : 0 < |x i0| := lt_trans (by linarith) h
            have : 0 < x i0 ^ 2 := by rw [← sq_abs]; positivity
            rw [hsp]; nlinarith [sq_nonneg (x i1)]
          · have : 0 < |x i1| := lt_trans (by linarith) h
            have : 0 < x i1 ^ 2 := by rw [← sq_abs]; positivity
            rw [hsp]; nlinarith [sq_nonneg (x i0)]
        have hle : axisSq w x ≤ 2 * τ ^ 2 := by
          rw [hsp]
          have b0 : x i0 ^ 2 ≤ τ ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) a0 2
          have b1 : x i1 ^ 2 ≤ τ ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) a1 2
          linarith
        exact Real.rpow_le_rpow_of_nonpos hpos hle (by linarith)

theorem dyadicBox_subset_euclideanBall {i0 i1 : Fin d} {c ρ : ℝ}
    (hc : (d : ℝ) * c ^ 2 < ρ ^ 2) :
    dyadicBox i0 i1 c c ⊆ euclideanBall (0 : Vec d) ρ := by
  intro x hx
  have hb : ∀ j, x j ^ 2 ≤ c ^ 2 := fun j => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (dyadicBox_coord_abs_le le_rfl hx j) 2
  change euclideanSqDist x 0 < ρ ^ 2
  have : euclideanSqDist x 0 = ∑ j, x j ^ 2 := by
    simp [euclideanSqDist, vecNormSq_eq_sum_sq]
  rw [this]
  calc ∑ j, x j ^ 2 ≤ ∑ _j : Fin d, c ^ 2 := Finset.sum_le_sum fun j _ => hb j
    _ = (d : ℝ) * c ^ 2 := by simp
    _ < ρ ^ 2 := hc

/-- For `e ≥ 1`, `s^{-e}` is not integrable near the codimension-two set `{s = 0}`. -/
theorem not_integrableOn_axisSq_rpow_neg {i0 i1 : Fin d} (hi : i0 ≠ i1) (h0 : w i0 = 1)
    (h1 : w i1 = 1) (hrest : ∀ j, j ≠ i0 → j ≠ i1 → w j = 0) {e : ℝ} (he : 1 ≤ e) {ρ : ℝ}
    (hρ : 0 < ρ) :
    ¬ IntegrableOn (fun x : Vec d => axisSq w x ^ (-e)) (euclideanBall (0 : Vec d) ρ) := by
  intro hint
  set c : ℝ := ρ / ((d : ℝ) + 1) with hcdef
  have hc : 0 < c := by positivity
  set τ : ℕ → ℝ := fun k => c / 2 ^ k with hτdef
  have hτpos : ∀ k, 0 < τ k := fun k => by positivity
  have hτc : ∀ k, τ k ≤ c := fun k => by
    simp only [hτdef]
    exact div_le_self hc.le (one_le_pow₀ (by norm_num))
  have hτhalf : ∀ k, τ k / 2 = τ (k + 1) := fun k => by
    simp only [hτdef, pow_succ]; field_simp
  have hτanti : ∀ k m, k ≤ m → τ m ≤ τ k := fun k m hkm => by
    simp only [hτdef]
    exact div_le_div_of_nonneg_left hc.le (by positivity) (pow_le_pow_right₀ (by norm_num) hkm)
  let D : ℕ → Set (Vec d) := fun k => dyadicBox i0 i1 (τ k) c \ dyadicBox i0 i1 (τ (k + 1)) c
  have hD : ∀ k, MeasurableSet (D k) := fun k =>
    (measurableSet_dyadicBox _ _ _ _).diff (measurableSet_dyadicBox _ _ _ _)
  have hball : ∀ k, D k ⊆ euclideanBall (0 : Vec d) ρ := by
    intro k x hx
    have h0k : dyadicBox i0 i1 (τ k) c ⊆ dyadicBox i0 i1 (τ 0) c :=
      dyadicBox_mono i0 i1 (hτanti 0 k (Nat.zero_le k)) c
    have hτ0 : τ 0 = c := by simp [hτdef]
    apply dyadicBox_subset_euclideanBall (i0 := i0) (i1 := i1) _
    · have := h0k hx.1
      rwa [hτ0] at this
    · have hd1 : (d : ℝ) < ((d : ℝ) + 1) ^ 2 := by nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
      have : c ^ 2 = ρ ^ 2 / ((d : ℝ) + 1) ^ 2 := by rw [hcdef, div_pow]
      rw [this, ← mul_div_assoc, div_lt_iff₀ (by positivity)]
      nlinarith [mul_lt_mul_of_pos_left hd1 (pow_pos hρ 2)]
  have hdisj : (↑(Finset.range 0) : Set ℕ).PairwiseDisjoint D ∨ True := Or.inr trivial
  clear hdisj
  have hpair : ∀ N : ℕ, (↑(Finset.range N) : Set ℕ).PairwiseDisjoint D := by
    intro N k _ m _ hkm
    rcases lt_or_gt_of_ne hkm with h | h
    · refine Set.disjoint_left.mpr fun x hxk hxm => ?_
      exact hxk.2 (dyadicBox_mono i0 i1 (hτanti (k + 1) m h) c hxm.1)
    · refine Set.disjoint_left.mpr fun x hxk hxm => ?_
      exact hxm.2 (dyadicBox_mono i0 i1 (hτanti (m + 1) k h) c hxk.1)
  set m0 : ℝ := 3 * (2 * c) ^ numOther i0 i1 * 2 ^ (-e) * (c ^ 2) ^ (1 - e) with hm0
  have hm0pos : 0 < m0 := by positivity
  have hlow : ∀ k, ENNReal.ofReal m0 ≤
      ∫⁻ x in D k, ENNReal.ofReal (axisSq w x ^ (-e)) := by
    intro k
    have := shell_lintegral_lower hi h0 h1 hrest he (hτpos k) (hτc k)
    rw [hτhalf] at this
    exact this
  have hfin := hint.lintegral_lt_top
  have hN : ∀ N : ℕ, (N : ℝ≥0∞) * ENNReal.ofReal m0 ≤
      ∫⁻ x in euclideanBall (0 : Vec d) ρ, ENNReal.ofReal (axisSq w x ^ (-e)) := by
    intro N
    calc (N : ℝ≥0∞) * ENNReal.ofReal m0
        = ∑ _k ∈ Finset.range N, ENNReal.ofReal m0 := by simp
      _ ≤ ∑ k ∈ Finset.range N, ∫⁻ x in D k, ENNReal.ofReal (axisSq w x ^ (-e)) :=
          Finset.sum_le_sum fun k _ => hlow k
      _ = ∫⁻ x in ⋃ k ∈ Finset.range N, D k, ENNReal.ofReal (axisSq w x ^ (-e)) :=
          (lintegral_biUnion_finset (hpair N) (fun k _ => hD k) _).symm
      _ ≤ _ := lintegral_mono_set (iUnion₂_subset fun k _ => hball k)
  obtain ⟨N, hNlt⟩ := exists_nat_gt
    ((∫⁻ x in euclideanBall (0 : Vec d) ρ, ENNReal.ofReal (axisSq w x ^ (-e))).toReal / m0)
  have h1' := hN N
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg N),
    ENNReal.ofReal_le_iff_le_toReal hfin.ne] at h1'
  rw [div_lt_iff₀ hm0pos] at hNlt
  linarith

end PDE.Ch4Meyers
