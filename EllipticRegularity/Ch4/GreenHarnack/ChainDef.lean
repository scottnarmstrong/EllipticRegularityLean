module

public import PDEFoundation.Ambient.Basis

/-!
# Chains of points with small steps

`IsChain K s n x y` says that there are points `z₀ = x, …, z_n = y` in `K` with
`|z_{i+1} - z_i| < s` (Euclidean norm). Chains concatenate, reverse, can be padded, and a
Lipschitz path yields a chain.
-/

@[expose] public section

namespace PDE.Ch4GreenHarnack

open PDE

variable {d : ℕ}

/-- A chain of `n` steps of Euclidean length `< s` in `K` from `x` to `y`. -/
def IsChain (K : Set (Vec d)) (s : ℝ) (n : ℕ) (x y : Vec d) : Prop :=
  ∃ z : ℕ → Vec d, z 0 = x ∧ z n = y ∧ (∀ i ≤ n, z i ∈ K) ∧
    ∀ i < n, vecEuclideanNorm (z (i + 1) - z i) < s

theorem IsChain.refl {K : Set (Vec d)} {s : ℝ} (hs : 0 < s) (n : ℕ) {x : Vec d} (hx : x ∈ K) :
    IsChain K s n x x :=
  ⟨fun _ => x, rfl, rfl, fun _ _ => hx, fun _ _ => by
    rw [vecEuclideanNorm_eq_zero_iff.mpr (sub_self x)]; exact hs⟩

theorem IsChain.mem_left {K : Set (Vec d)} {s : ℝ} {n : ℕ} {x y : Vec d}
    (h : IsChain K s n x y) : x ∈ K := by
  obtain ⟨z, hz0, _, hzK, _⟩ := h
  rw [← hz0]; exact hzK 0 (Nat.zero_le _)

theorem IsChain.mem_right {K : Set (Vec d)} {s : ℝ} {n : ℕ} {x y : Vec d}
    (h : IsChain K s n x y) : y ∈ K := by
  obtain ⟨z, _, hzn, hzK, _⟩ := h
  rw [← hzn]; exact hzK n le_rfl

theorem IsChain.mono_set {K K' : Set (Vec d)} {s : ℝ} {n : ℕ} {x y : Vec d}
    (h : IsChain K s n x y) (hK : K ⊆ K') : IsChain K' s n x y := by
  obtain ⟨z, hz0, hzn, hzK, hzs⟩ := h
  exact ⟨z, hz0, hzn, fun i hi => hK (hzK i hi), hzs⟩

theorem IsChain.trans {K : Set (Vec d)} {s : ℝ} {n m : ℕ} {x y w : Vec d}
    (h₁ : IsChain K s n x y) (h₂ : IsChain K s m y w) : IsChain K s (n + m) x w := by
  obtain ⟨z, hz0, hzn, hzK, hzs⟩ := h₁
  obtain ⟨v, hv0, hvm, hvK, hvs⟩ := h₂
  refine ⟨fun i => if i ≤ n then z i else v (i - n), ?_, ?_, ?_, ?_⟩
  · simp [hz0]
  · by_cases hm : m = 0
    · subst hm
      simp only [Nat.add_zero, le_refl, ite_true]
      rw [hzn, ← hv0]; exact hvm
    · have : ¬ (n + m ≤ n) := by omega
      simp only [this, ite_false, Nat.add_sub_cancel_left, hvm]
  · intro i hi
    by_cases h : i ≤ n
    · simp only [h, ite_true]; exact hzK i h
    · simp only [h, ite_false]; exact hvK _ (by omega)
  · intro i hi
    by_cases h1 : i + 1 ≤ n
    · have h0 : i ≤ n := by omega
      simp only [h1, h0, ite_true]; exact hzs i (by omega)
    · by_cases h2 : i = n
      · subst h2
        have h0 : i ≤ i := le_rfl
        have h3 : i + 1 - i = 0 + 1 := by omega
        simp only [h1, h0, ite_true, ite_false, h3]
        rw [hzn, ← hv0]
        exact hvs 0 (by omega)
      · have h0 : ¬ i ≤ n := by omega
        have h3 : i + 1 - n = (i - n) + 1 := by omega
        simp only [h1, h0, ite_false, h3]
        exact hvs (i - n) (by omega)

theorem IsChain.symm {K : Set (Vec d)} {s : ℝ} {n : ℕ} {x y : Vec d}
    (h : IsChain K s n x y) : IsChain K s n y x := by
  obtain ⟨z, hz0, hzn, hzK, hzs⟩ := h
  refine ⟨fun i => z (n - i), by simpa using hzn, by simpa using hz0, ?_, ?_⟩
  · intro i hi; exact hzK _ (Nat.sub_le _ _)
  · intro i hi
    have h1 : n - i = (n - (i + 1)) + 1 := by omega
    have := hzs (n - (i + 1)) (by omega)
    rw [vecEuclideanNorm_sub_comm]
    simpa only [h1] using this

theorem IsChain.mono {K : Set (Vec d)} {s : ℝ} (hs : 0 < s) {n m : ℕ} {x y : Vec d}
    (h : IsChain K s n x y) (hnm : n ≤ m) : IsChain K s m x y := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  simpa using h.trans (IsChain.refl hs k h.mem_right)

/-- A Lipschitz path in `K` gives a chain. -/
theorem IsChain.of_lipschitz {K : Set (Vec d)} {s L : ℝ} {γ : ℝ → Vec d}
    (hK : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ K)
    (hL : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ t' ∈ Set.Icc (0 : ℝ) 1,
      vecEuclideanNorm (γ t - γ t') ≤ L * |t - t'|)
    {n : ℕ} (hn : 0 < n) (hLn : L < n * s) : IsChain K s n (γ 0) (γ 1) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmem : ∀ i ≤ n, ((i : ℝ) / n) ∈ Set.Icc (0 : ℝ) 1 := fun i hi =>
    ⟨by positivity, by rw [div_le_one hn']; exact_mod_cast hi⟩
  refine ⟨fun i => γ ((i : ℝ) / n), by simp, by simp [hn'.ne'], ?_, ?_⟩
  · intro i hi; exact hK _ (hmem i hi)
  · intro i hi
    have h1 := hL _ (hmem (i + 1) hi) _ (hmem i hi.le)
    have h2 : |((i + 1 : ℕ) : ℝ) / n - (i : ℝ) / n| = 1 / n := by
      push_cast
      rw [show ((i : ℝ) + 1) / n - i / n = 1 / n by ring, abs_of_pos (by positivity)]
    rw [h2] at h1
    refine h1.trans_lt ?_
    rw [mul_one_div, div_lt_iff₀ hn']
    linarith

end PDE.Ch4GreenHarnack
