module

public import PDEFoundation.Monotonicity.Poon.DerivBoundsSlice

/-!
# Pointwise derivative bounds with Gaussian growth for backward-caloric functions

Setting of Poon's monotonicity formula: `u` is smooth on `(-T, 0) × ℝᵈ`, solves the heat equation
`∂_t u = Δ u` there and satisfies `|u(t,x)| ≤ C exp (A |x|²)`.  For every compact time interval
`[t₁, t₂] ⊂ (-T, 0)` and every `A' > A` there is `C'` such that, on `[t₁, t₂] × ℝᵈ`, `u`, its spatial
derivatives up to order `3`, `∂_t u` and `∇ ∂_t u` are all bounded by `C' exp (A' |x|²)`.

Route: the Bernstein estimate on cylinders of radius `ρ` (`DerivBoundsStep`) is iterated three times on
the caloric functions `∂_i u`, shrinking the time interval by `ρ²` each time.
-/

@[expose] public section

open Set Filter

namespace PDE

noncomputable section

variable {d : ℕ}

theorem le_const_mul_exp_of_le {b c C' A₀ A' X : ℝ} (h : b ≤ c * Real.exp (A₀ * X))
    (hc : c ≤ C') (hc0 : 0 ≤ c) (hX : 0 ≤ X) (hA : A₀ ≤ A') :
    b ≤ C' * Real.exp (A' * X) :=
  h.trans (mul_le_mul hc (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hA hX))
    (Real.exp_nonneg _) (hc0.trans hc))

theorem abs_sum_le_card_mul {ι : Type*} (s : Finset ι) {f : ι → ℝ} {c : ℝ}
    (h : ∀ k ∈ s, |f k| ≤ c) : |∑ k ∈ s, f k| ≤ (s.card : ℝ) * c :=
  (Finset.abs_sum_le_sum_abs _ _).trans (by
    have := Finset.sum_le_card_nsmul s (fun k => |f k|) c h
    simpa [nsmul_eq_mul] using this)

theorem grow_jEx_of_norm {a b s t₂ A' C' : ℝ} {h : ℝ × Vec d → ℝ} (hh : CaloricOn a b h)
    (hsub : Icc s t₂ ⊆ Ioo a b)
    (hn : ∀ t ∈ Icc s t₂, ∀ x : Vec d,
      vecEuclideanNorm (classicalGradient (fun y => h (t, y)) x) ≤
        C' * Real.exp (A' * vecNormSq x)) (i : Fin d) :
    Grow (jEx i h) s t₂ A' C' := fun t ht x =>
  (abs_jEx_le_norm_gradient hh.1 (hsub ht) x i).trans (hn t ht x)

theorem caloricOn_of_heat {u : ℝ → Vec d → ℝ} {T : ℝ}
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec d => u p.1 p.2)
      (Ioo (-T) 0 ×ˢ (univ : Set (Vec d))))
    (heat : ∀ t ∈ Ioo (-T) 0, ∀ x : Vec d,
      HasDerivAt (fun τ : ℝ => u τ x) (euclideanCoordLaplacian (u t) x) t) :
    CaloricOn (-T) 0 (fun p : ℝ × Vec d => u p.1 p.2) := by
  refine ⟨hsmooth, ?_⟩
  rintro ⟨t, x⟩ hp
  have hΩ := isOpen_slab (d := d) (-T) 0
  have h1 := deriv_slice_time (g := fun p : ℝ × Vec d => u p.1 p.2)
    (JSm.differentiableAt hΩ hsmooth hp)
  have h2 := euclideanCoordLaplacian_slice hΩ hsmooth hp
  have h3 : jEt (fun p : ℝ × Vec d => u p.1 p.2) (t, x) = deriv (fun τ : ℝ => u τ x) t := h1.symm
  have h4 : jEt (fun p : ℝ × Vec d => u p.1 p.2) (t, x) =
      jLap (fun p : ℝ × Vec d => u p.1 p.2) (t, x) := by
    rw [h3, (heat t hp.1 x).deriv, ← h2]
  exact h4

/-- **Interior derivative bounds with Gaussian growth.** -/
theorem derivBounds_exists {u : ℝ → Vec d → ℝ} {T A C : ℝ}
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec d => u p.1 p.2)
      (Ioo (-T) 0 ×ˢ (univ : Set (Vec d))))
    (heat : ∀ t ∈ Ioo (-T) 0, ∀ x : Vec d,
      HasDerivAt (fun τ : ℝ => u τ x) (euclideanCoordLaplacian (u t) x) t)
    (hbound : ∀ t ∈ Ioo (-T) 0, ∀ x : Vec d, |u t x| ≤ C * Real.exp (A * vecNormSq x))
    {t₁ t₂ A' : ℝ} (ht₁ : -T < t₁) (ht₂ : t₂ < 0) (hA : A < A') :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ t ∈ Icc t₁ t₂, ∀ x : Vec d,
      |u t x| ≤ C' * Real.exp (A' * vecNormSq x) ∧
      vecEuclideanNorm (classicalGradient (u t) x) ≤ C' * Real.exp (A' * vecNormSq x) ∧
      (∀ i j : Fin d, |euclideanCoordDeriv i (euclideanCoordDeriv j (u t)) x| ≤
        C' * Real.exp (A' * vecNormSq x)) ∧
      (∀ i j k : Fin d,
        |euclideanCoordDeriv i (euclideanCoordDeriv j (euclideanCoordDeriv k (u t))) x| ≤
          C' * Real.exp (A' * vecNormSq x)) ∧
      |deriv (fun τ : ℝ => u τ x) t| ≤ C' * Real.exp (A' * vecNormSq x) ∧
      vecEuclideanNorm (classicalGradient (fun y => deriv (fun τ : ℝ => u τ y) t) x) ≤
        C' * Real.exp (A' * vecNormSq x) := by
  classical
  set g : ℝ × Vec d → ℝ := fun p => u p.1 p.2 with hgdef
  have hcal : CaloricOn (-T) 0 g := caloricOn_of_heat hsmooth heat
  have hΩ := isOpen_slab (d := d) (-T) 0
  -- radius and time shrinking
  set ρ : ℝ := min 1 ((t₁ + T) / 4) with hρdef
  have hρ : 0 < ρ := lt_min one_pos (by linarith)
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρ2 : ρ ≤ (t₁ + T) / 4 := min_le_right _ _
  have hρsq : ρ ^ 2 ≤ ρ := pow_le_of_le_one hρ.le hρ1 two_ne_zero
  set s₀ : ℝ := t₁ - 3 * ρ ^ 2 with hs₀
  have hs₀T : -T < s₀ := by linarith
  have hsub : ∀ s : ℝ, -T < s → Icc s t₂ ⊆ Ioo (-T) 0 :=
    fun s hs p hp => ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have hρ2' : 0 ≤ ρ ^ 2 := by positivity
  set C₀ : ℝ := max C 0 with hC₀def
  have hC₀ : 0 ≤ C₀ := le_max_right _ _
  set δ : ℝ := (A' - A) / 3 with hδ
  have G0 : Grow g s₀ t₂ A C₀ := fun t ht x => by
    have := hbound t (hsub s₀ hs₀T ht) x
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _))
  obtain ⟨C₁, hC₁, S1⟩ := grad_growth_step (a := -T) (b := 0) (t₁ := s₀) (t₂ := t₂) (A := A)
    (A' := A + δ) (C := C₀) (ρ := ρ) (hsub s₀ hs₀T) hρ hC₀ (by linarith)
  obtain ⟨C₂, hC₂, S2⟩ := grad_growth_step (a := -T) (b := 0) (t₁ := s₀ + ρ ^ 2) (t₂ := t₂)
    (A := A + δ) (A' := A + 2 * δ) (C := C₁) (ρ := ρ)
    (hsub _ (by linarith)) hρ hC₁ (by linarith)
  obtain ⟨C₃, hC₃, S3⟩ := grad_growth_step (a := -T) (b := 0) (t₁ := s₀ + ρ ^ 2 + ρ ^ 2)
    (t₂ := t₂) (A := A + 2 * δ) (A' := A') (C := C₂) (ρ := ρ)
    (hsub _ (by linarith)) hρ hC₂ (by linarith)
  have e3 : s₀ + ρ ^ 2 + ρ ^ 2 + ρ ^ 2 = t₁ := by rw [hs₀]; ring
  have N1 := S1 g hcal G0
  have G1 : ∀ i, Grow (jEx i g) (s₀ + ρ ^ 2) t₂ (A + δ) C₁ :=
    grow_jEx_of_norm hcal (hsub _ (by linarith)) N1
  have N2 : ∀ i, ∀ t ∈ Icc (s₀ + ρ ^ 2 + ρ ^ 2) t₂, ∀ x : Vec d,
      vecEuclideanNorm (classicalGradient (fun y => jEx i g (t, y)) x) ≤
        C₂ * Real.exp ((A + 2 * δ) * vecNormSq x) := fun i => S2 _ (hcal.jEx i) (G1 i)
  have G2 : ∀ i j, Grow (jEx j (jEx i g)) (s₀ + ρ ^ 2 + ρ ^ 2) t₂ (A + 2 * δ) C₂ :=
    fun i => grow_jEx_of_norm (hcal.jEx i) (hsub _ (by linarith)) (N2 i)
  have N3 : ∀ i j, ∀ t ∈ Icc t₁ t₂, ∀ x : Vec d,
      vecEuclideanNorm (classicalGradient (fun y => jEx j (jEx i g) (t, y)) x) ≤
        C₃ * Real.exp (A' * vecNormSq x) := fun i j t ht x =>
    S3 _ ((hcal.jEx i).jEx j) (G2 i j) t (by rw [e3]; exact ht) x
  have G3 : ∀ i j k, Grow (jEx k (jEx j (jEx i g))) t₁ t₂ A' C₃ := fun i j k =>
    grow_jEx_of_norm ((hcal.jEx i).jEx j) (hsub _ ht₁) (N3 i j) k
  set Cs : ℝ := C₀ + C₁ + C₂ + C₃ with hCs
  have hD : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine ⟨(1 + (d : ℝ)) ^ 2 * Cs, by positivity, fun t ht x => ?_⟩
  have htT : t ∈ Ioo (-T) 0 := hsub t₁ ht₁ ht
  have hX := vecNormSq_nonneg x
  have hbig : ∀ c : ℝ, 0 ≤ c → c ≤ Cs → ∀ m : ℝ, 0 ≤ m → m ≤ (1 + (d : ℝ)) ^ 2 →
      m * c ≤ (1 + (d : ℝ)) ^ 2 * Cs := fun c hc hcs m hm hm2 =>
    mul_le_mul hm2 hcs hc (by positivity)
  have hc0 : C₀ ≤ Cs := by linarith
  have hc1 : C₁ ≤ Cs := by linarith
  have hc2 : C₂ ≤ Cs := by linarith
  have hc3 : C₃ ≤ Cs := by linarith
  have hsq : ∀ m : ℝ, 0 ≤ m → m ≤ (1 + (d : ℝ)) ^ 2 → ∀ c : ℝ, 0 ≤ c → c ≤ Cs →
      m * c ≤ (1 + (d : ℝ)) ^ 2 * Cs := fun m hm hm2 c hc hcs => hbig c hc hcs m hm hm2
  have h1d : (1 : ℝ) ≤ (1 + (d : ℝ)) ^ 2 := by linarith [sq_nonneg (d : ℝ)]
  have hdd : (d : ℝ) ≤ (1 + (d : ℝ)) ^ 2 := by linarith [sq_nonneg (d : ℝ)]
  have hdd2 : (d : ℝ) * d ≤ (1 + (d : ℝ)) ^ 2 := by linarith
  -- exponents
  have hA1 : A + δ ≤ A' := by linarith
  have hA2 : A + 2 * δ ≤ A' := by linarith
  have hsq' : ∀ c : ℝ, 0 ≤ c → c ≤ Cs → ∀ m : ℝ, 0 ≤ m → m ≤ (1 + (d : ℝ)) ^ 2 →
      m * c * Real.exp (A' * vecNormSq x) ≤ (1 + (d : ℝ)) ^ 2 * Cs * Real.exp (A' * vecNormSq x) :=
    fun c hc hcs m hm hm2 =>
      mul_le_mul_of_nonneg_right (hbig c hc hcs m hm hm2) (Real.exp_nonneg _)
  have ht0 : s₀ ≤ t₁ := by rw [hs₀]; linarith
  have htA : ∀ s : ℝ, s ≤ t₁ → t ∈ Icc s t₂ := fun s hs => ⟨hs.trans ht.1, ht.2⟩
  have hu0 : |u t x| ≤ (1 + (d : ℝ)) ^ 2 * Cs * Real.exp (A' * vecNormSq x) := by
    have h := G0 t (htA s₀ ht0) x
    refine le_const_mul_exp_of_le (c := C₀) (A₀ := A) h ?_ hC₀ hX hA.le
    have := hbig C₀ hC₀ hc0 1 zero_le_one h1d
    linarith
  have hu1 : vecEuclideanNorm (classicalGradient (u t) x) ≤
      (1 + (d : ℝ)) ^ 2 * Cs * Real.exp (A' * vecNormSq x) := by
    have h := N1 t (htA (s₀ + ρ ^ 2) (by linarith)) x
    refine le_const_mul_exp_of_le (c := C₁) (A₀ := A + δ) h ?_ hC₁ hX hA1
    have := hbig C₁ hC₁ hc1 1 zero_le_one h1d
    linarith
  have E2 : ∀ i j : Fin d, euclideanCoordDeriv i (euclideanCoordDeriv j (u t)) x =
      jEx i (jEx j g) (t, x) := by
    intro i j
    have e2 : euclideanCoordDeriv j (u t) = fun y => jEx j g (t, y) :=
      coordDeriv_slice_eq hcal.1 htT j
    rw [e2]
    exact congrFun (coordDeriv_slice_eq (hcal.1.jEx hΩ j) htT i) x
  have E3 : ∀ i j k : Fin d,
      euclideanCoordDeriv i (euclideanCoordDeriv j (euclideanCoordDeriv k (u t))) x =
        jEx i (jEx j (jEx k g)) (t, x) := by
    intro i j k
    have e1 : euclideanCoordDeriv k (u t) = fun y => jEx k g (t, y) :=
      coordDeriv_slice_eq hcal.1 htT k
    rw [e1, coordDeriv_slice_eq (hcal.1.jEx hΩ k) htT j]
    exact congrFun (coordDeriv_slice_eq ((hcal.1.jEx hΩ k).jEx hΩ j) htT i) x
  have hu2 : ∀ i j : Fin d, |euclideanCoordDeriv i (euclideanCoordDeriv j (u t)) x| ≤
      (1 + (d : ℝ)) ^ 2 * Cs * Real.exp (A' * vecNormSq x) := by
    intro i j
    rw [E2]
    have h := G2 j i t (htA _ (by linarith)) x
    refine le_const_mul_exp_of_le (c := C₂) (A₀ := A + 2 * δ) h ?_ hC₂ hX hA2
    have := hbig C₂ hC₂ hc2 1 zero_le_one h1d
    linarith
  have hu3 : ∀ i j k : Fin d,
      |euclideanCoordDeriv i (euclideanCoordDeriv j (euclideanCoordDeriv k (u t))) x| ≤
        (1 + (d : ℝ)) ^ 2 * Cs * Real.exp (A' * vecNormSq x) := by
    intro i j k
    rw [E3]
    have h := G3 k j i t ht x
    refine le_const_mul_exp_of_le (c := C₃) (A₀ := A') h ?_ hC₃ hX le_rfl
    have := hbig C₃ hC₃ hc3 1 zero_le_one h1d
    linarith
  -- time derivative
  have Dt : (fun y : Vec d => deriv (fun τ : ℝ => u τ y) t) = fun y => jLap g (t, y) := by
    rw [deriv_slice_eq hcal.1 htT]
    exact funext fun y => hcal.2 ⟨htT, mem_univ y⟩
  have hu4 : |deriv (fun τ : ℝ => u τ x) t| ≤
      (1 + (d : ℝ)) ^ 2 * Cs * Real.exp (A' * vecNormSq x) := by
    have e : deriv (fun τ : ℝ => u τ x) t = jLap g (t, x) := congrFun Dt x
    rw [e]
    change |∑ k : Fin d, jEx k (jEx k g) (t, x)| ≤ _
    have hk : ∀ k ∈ (Finset.univ : Finset (Fin d)), |jEx k (jEx k g) (t, x)| ≤
        C₂ * Real.exp (A' * vecNormSq x) := fun k _ => by
      have h := G2 k k t (htA _ (by linarith)) x
      exact le_const_mul_exp_of_le (c := C₂) (A₀ := A + 2 * δ) h le_rfl hC₂ hX hA2
    refine (abs_sum_le_card_mul _ hk).trans ?_
    rw [Finset.card_univ, Fintype.card_fin]
    have := hsq' C₂ hC₂ hc2 (d : ℝ) hD hdd
    linarith
  have hu5 : vecEuclideanNorm (classicalGradient (fun y => deriv (fun τ : ℝ => u τ y) t) x) ≤
      (1 + (d : ℝ)) ^ 2 * Cs * Real.exp (A' * vecNormSq x) := by
    rw [Dt]
    refine (vecEuclideanNorm_le_sum_abs _).trans ?_
    have hi : ∀ i ∈ (Finset.univ : Finset (Fin d)),
        |classicalGradient (fun y => jLap g (t, y)) x i| ≤
          (d : ℝ) * (C₃ * Real.exp (A' * vecNormSq x)) := by
      intro i _
      have e1 : classicalGradient (fun y => jLap g (t, y)) x i = jEx i (jLap g) (t, x) := by
        rw [← euclideanCoordDeriv_eq_classicalGradient_apply,
          coordDeriv_slice_eq (hcal.1.jLap hΩ) htT i]
      have e2 : jEx i (jLap g) (t, x) = ∑ k : Fin d, jEx i (jEx k (jEx k g)) (t, x) :=
        jd_sum Finset.univ hΩ _ (fun k _ => (hcal.1.jEx hΩ k).jEx hΩ k) ⟨htT, mem_univ x⟩
      rw [e1, e2]
      have hk : ∀ k ∈ (Finset.univ : Finset (Fin d)), |jEx i (jEx k (jEx k g)) (t, x)| ≤
          C₃ * Real.exp (A' * vecNormSq x) := fun k _ => G3 k k i t ht x
      have := abs_sum_le_card_mul _ hk
      rwa [Finset.card_univ, Fintype.card_fin] at this
    have hs := Finset.sum_le_card_nsmul Finset.univ
      (fun i => |classicalGradient (fun y => jLap g (t, y)) x i|) _ hi
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    refine hs.trans ?_
    have := hsq' C₃ hC₃ hc3 ((d : ℝ) * d) (by positivity) hdd2
    linarith [this]
  exact ⟨hu0, hu1, hu2, hu3, hu4, hu5⟩

end

end PDE
