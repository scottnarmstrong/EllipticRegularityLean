module

public import EllipticRegularity.DeGiorgi.Assembly.EssContinuous
public import PDEFoundation.Regularity.Holder

/-!
# Oscillation decay and Hölder continuity (real-analysis part of Theorem 4.21)

Pure statements about a function `v : Vec d → ℝ` on balls: a one-step oscillation decay from a
pointwise Harnack inequality, its iteration, and the resulting Hölder seminorm bound.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.DGNMAssembly

open MeasureTheory Set

variable {d : ℕ}

/-- The oscillation of `v` on `S` is at most `ω`. -/
def OscLE (S : Set (Vec d)) (v : Vec d → ℝ) (ω : ℝ) : Prop :=
  ∀ y ∈ S, ∀ z ∈ S, v y - v z ≤ ω

theorem le_of_forall_pos_add_le {a b H : ℝ} (hH : 1 ≤ H)
    (h : ∀ ε : ℝ, 0 < ε → a + ε ≤ H * (b + ε)) : a ≤ H * b := by
  by_contra hcon
  rw [not_le] at hcon
  have hH0 : 0 < H := by linarith
  have hε : 0 < (a - H * b) / (2 * H) := by positivity
  have := h _ hε
  have h2 : (a - H * b) / (2 * H) * H = (a - H * b) / 2 := by field_simp
  nlinarith

/-- Supremum minus infimum is at most the oscillation bound. -/
theorem sSup_sub_sInf_le {S : Set (Vec d)} {v : Vec d → ℝ} {ω Kb : ℝ} (hne : S.Nonempty)
    (hb : ∀ y ∈ S, |v y| ≤ Kb) (hosc : OscLE S v ω) :
    sSup (v '' S) - sInf (v '' S) ≤ ω := by
  have hne' : (v '' S).Nonempty := hne.image v
  have hbA : BddAbove (v '' S) := ⟨Kb, by rintro _ ⟨y, hy, rfl⟩; exact (le_abs_self _).trans (hb y hy)⟩
  have hbB : BddBelow (v '' S) :=
    ⟨-Kb, by rintro _ ⟨y, hy, rfl⟩; linarith [neg_abs_le (v y), hb y hy]⟩
  have h1 : ∀ y1 ∈ S, v y1 - ω ≤ sInf (v '' S) := by
    intro y1 hy1
    apply le_csInf hne'
    rintro _ ⟨y2, hy2, rfl⟩
    linarith [hosc y1 hy1 y2 hy2]
  have h2 : sSup (v '' S) ≤ sInf (v '' S) + ω := by
    apply csSup_le hne'
    rintro _ ⟨y1, hy1, rfl⟩
    linarith [h1 y1 hy1]
  linarith

/-- One step of oscillation decay from a pointwise Harnack inequality. -/
theorem osc_step {v : Vec d → ℝ} {x : Vec d} {r H Kb ω : ℝ} (hr : 0 < r) (hH : 1 ≤ H)
    (hb : ∀ y ∈ euclideanBall x r, |v y| ≤ Kb)
    (hharn : ∀ s c : ℝ, (s = 1 ∨ s = -1) → (∀ y ∈ euclideanBall x r, 0 < c + s * v y) →
      ∀ y ∈ euclideanBall x (r / 2), ∀ z ∈ euclideanBall x (r / 2),
        c + s * v y ≤ H * (c + s * v z))
    (hosc : OscLE (euclideanBall x r) v ω) :
    OscLE (euclideanBall x (r / 2)) v ((H - 1) / (H + 1) * ω) := by
  have hne : (euclideanBall x r).Nonempty := euclideanBall_nonempty x hr
  set M := sSup (v '' euclideanBall x r) with hM
  set m := sInf (v '' euclideanBall x r) with hm
  have hMm : M - m ≤ ω := sSup_sub_sInf_le hne hb hosc
  have hbA : BddAbove (v '' euclideanBall x r) :=
    ⟨Kb, by rintro _ ⟨y, hy, rfl⟩; exact (le_abs_self _).trans (hb y hy)⟩
  have hbB : BddBelow (v '' euclideanBall x r) :=
    ⟨-Kb, by rintro _ ⟨y, hy, rfl⟩; linarith [neg_abs_le (v y), hb y hy]⟩
  have hvM : ∀ y ∈ euclideanBall x r, v y ≤ M := fun y hy => le_csSup hbA ⟨y, hy, rfl⟩
  have hvm : ∀ y ∈ euclideanBall x r, m ≤ v y := fun y hy => csInf_le hbB ⟨y, hy, rfl⟩
  have hup : ∀ y ∈ euclideanBall x (r / 2), ∀ z ∈ euclideanBall x (r / 2),
      M - v y ≤ H * (M - v z) := by
    intro y hy z hz
    apply le_of_forall_pos_add_le hH
    intro ε hε
    have := hharn (-1) (M + ε) (Or.inr rfl) (fun w hw => by nlinarith [hvM w hw]) y hy z hz
    nlinarith
  have hlow : ∀ y ∈ euclideanBall x (r / 2), ∀ z ∈ euclideanBall x (r / 2),
      v y - m ≤ H * (v z - m) := by
    intro y hy z hz
    apply le_of_forall_pos_add_le hH
    intro ε hε
    have := hharn 1 (-m + ε) (Or.inl rfl) (fun w hw => by nlinarith [hvm w hw]) y hy z hz
    nlinarith
  intro y hy z hz
  have h1 := hup z hz y hy
  have h2 := hlow y hy z hz
  have hH1 : 0 < H + 1 := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hH1]
  nlinarith

theorem osc_iterate {v : Vec d → ℝ} {x : Vec d} {σ K : ℝ}
    (hstep : ∀ r : ℝ, 0 < r → r ≤ 1 / 4 → ∀ ω : ℝ, OscLE (euclideanBall x r) v ω →
      OscLE (euclideanBall x (r / 2)) v (σ * ω))
    (h0 : OscLE (euclideanBall x (1 / 4)) v (2 * K)) :
    ∀ n : ℕ, OscLE (euclideanBall x (1 / 4 * (1 / 2) ^ n)) v (2 * K * σ ^ n) := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    have hr : 0 < 1 / 4 * (1 / 2 : ℝ) ^ n := by positivity
    have hr4 : 1 / 4 * (1 / 2 : ℝ) ^ n ≤ 1 / 4 := by
      have : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      linarith
    have := hstep _ hr hr4 _ ih
    have e : 1 / 4 * (1 / 2 : ℝ) ^ n / 2 = 1 / 4 * (1 / 2) ^ (n + 1) := by
      rw [pow_succ]; ring
    rw [e] at this
    have e2 : σ * (2 * K * σ ^ n) = 2 * K * σ ^ (n + 1) := by ring
    rwa [e2] at this

theorem exists_dyadic_scale {t : ℝ} (ht0 : 0 < t) (ht : t < 1 / 4) :
    ∃ m : ℕ, 4 * t < (1 / 2 : ℝ) ^ m ∧ (1 / 2 : ℝ) ^ m ≤ 16 * t := by
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near_of_lt_one (x := 4 * t) (y := (1 / 2 : ℝ))
    (by positivity) (by linarith) (by norm_num) (by norm_num)
  cases n with
  | zero =>
    refine ⟨0, by simpa using (by linarith : 4 * t < 1), ?_⟩
    simp only [pow_zero] at *
    linarith
  | succ k =>
    refine ⟨k, ?_, ?_⟩
    · have : (1 / 2 : ℝ) ^ (k + 1) < (1 / 2) ^ k :=
        pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (by omega)
      linarith
    · have e : (1 / 2 : ℝ) ^ k = 4 * (1 / 2) ^ (k + 1 + 1) := by
        rw [pow_succ, pow_succ]; ring
      rw [e]; linarith

/-- The Hölder seminorm bound from one-step oscillation decay. -/
theorem holder_of_osc {v : Vec d → ℝ} {K α σ : ℝ} (hK : 0 ≤ K) (hα : 0 < α) (hα1 : α ≤ 1)
    (hσ : σ = (1 / 2 : ℝ) ^ α)
    (hbd : ∀ y ∈ euclideanBall (0 : Vec d) (3 / 4), |v y| ≤ K)
    (hstep : ∀ x ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ, 0 < r → r ≤ 1 / 4 →
      ∀ ω : ℝ, OscLE (euclideanBall x r) v ω → OscLE (euclideanBall x (r / 2)) v (σ * ω)) :
    EuclideanHolderSeminormLE (euclideanBall (0 : Vec d) (1 / 2)) v α (32 * K) := by
  intro x hx y hy
  have hball : ∀ r : ℝ, 0 < r → r ≤ 1 / 4 → euclideanBall x r ⊆ euclideanBall (0 : Vec d) (3 / 4) := by
    intro r hr hr4
    apply euclideanBall_subset_of_center_norm_add_le hr (by norm_num)
    have := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp hx
    rw [sub_zero] at this ⊢
    linarith
  have hh0 : OscLE (euclideanBall x (1 / 4)) v (2 * K) := by
    intro y1 hy1 z1 hz1
    have h1 := hbd y1 (hball _ (by norm_num) le_rfl hy1)
    have h2 := hbd z1 (hball _ (by norm_num) le_rfl hz1)
    linarith [le_abs_self (v y1), neg_abs_le (v z1)]
  have hiter := osc_iterate (fun r hr hr4 ω h => hstep x hx r hr hr4 ω h) hh0
  set t := vecEuclideanNorm (x - y) with ht
  have ht_nn : 0 ≤ t := vecEuclideanNorm_nonneg _
  have hKαnn : 0 ≤ t ^ α := Real.rpow_nonneg ht_nn α
  by_cases htsmall : t < 1 / 4
  · rcases ht_nn.eq_or_lt with h0 | hpos
    · have : x = y := by
        have := vecEuclideanNorm_eq_zero_iff.1 h0.symm
        exact sub_eq_zero.1 this
      subst this
      simpa using mul_nonneg (by positivity : (0 : ℝ) ≤ 32 * K) hKαnn
    · obtain ⟨m, hm1, hm2⟩ := exists_dyadic_scale hpos htsmall
      have hymem : y ∈ euclideanBall x (1 / 4 * (1 / 2) ^ m) := by
        rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity), vecEuclideanNorm_sub_comm]
        linarith
      have hxmem : x ∈ euclideanBall x (1 / 4 * (1 / 2) ^ m) :=
        center_mem_euclideanBall _ (by positivity)
      have h1 := hiter m y hymem x hxmem
      have h2 := hiter m x hxmem y hymem
      have habs : |v x - v y| ≤ 2 * K * σ ^ m := by
        rw [abs_le]; constructor <;> linarith
      have hσm : σ ^ m = ((1 / 2 : ℝ) ^ m) ^ α := by
        rw [hσ, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
          ← Real.rpow_mul (by norm_num), mul_comm]
      have hpow : ((1 / 2 : ℝ) ^ m) ^ α ≤ (16 * t) ^ α :=
        Real.rpow_le_rpow (by positivity) hm2 hα.le
      have h16 : (16 : ℝ) ^ α ≤ 16 := by
        calc (16 : ℝ) ^ α ≤ 16 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1
          _ = 16 := Real.rpow_one _
      have hmul : (16 * t) ^ α = 16 ^ α * t ^ α := Real.mul_rpow (by norm_num) ht_nn
      calc |v x - v y| ≤ 2 * K * σ ^ m := habs
        _ ≤ 2 * K * (16 * t) ^ α := by
          rw [hσm]; exact mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = 2 * K * (16 ^ α * t ^ α) := by rw [hmul]
        _ ≤ 2 * K * (16 * t ^ α) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right h16 hKαnn
        _ ≤ 32 * K * t ^ α := by nlinarith [mul_nonneg hK hKαnn]
  · rw [not_lt] at htsmall
    have hxy : |v x - v y| ≤ 2 * K := by
      have h1 := hbd x (euclideanBall_mono (by norm_num) (by norm_num) hx)
      have h2 := hbd y (euclideanBall_mono (by norm_num) (by norm_num) hy)
      rw [abs_le] at h1 h2 ⊢; constructor <;> linarith
    have h4 : (1 / 4 : ℝ) ≤ t ^ α := by
      calc (1 / 4 : ℝ) = (1 / 4) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (1 / 4) ^ α := Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hα1
        _ ≤ t ^ α := Real.rpow_le_rpow (by norm_num) htsmall hα.le
    calc |v x - v y| ≤ 2 * K := hxy
      _ ≤ 32 * K * t ^ α := by nlinarith

end PDE.DGNMAssembly
