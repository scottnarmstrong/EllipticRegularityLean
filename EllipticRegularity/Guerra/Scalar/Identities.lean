module

public import EllipticRegularity.Guerra.Scalar.Profile

/-!
# Guerra sharpness: pole matching, hyperbolic identity, exponent

Scalar identities `μ = (d-1) φ'(1)`, `L(±1) = ∓ μ`, `μ φ = (d-1) φ' sinh(2γt)/sinh(2γ)`, and
the bounds on `α`.
-/

@[expose] public section

namespace PDE.Guerra

open Real

theorem tanh_mul_cosh_sq (s : ℝ) : tanh s * cosh s ^ 2 = sinh (2 * s) / 2 := by
  rw [tanh_eq_sinh_div_cosh, sinh_two_mul]
  have := (cosh_pos s).ne'
  field_simp

/-- Pole matching, first half: `μ = (d-1) φ'(1)`. -/
theorem mu_eq_dphi_one {γ : ℝ} (d : ℕ) (hγ : 1 ≤ γ) : mu d γ = ((d : ℝ) - 1) * dphi γ 1 := by
  unfold mu dphi
  rw [mul_one, tanh_mul_cosh_sq γ]
  have := (sinh_two_pos hγ).ne'
  field_simp

theorem mu_eq_dphi_neg_one {γ : ℝ} (d : ℕ) (hγ : 1 ≤ γ) :
    mu d γ = ((d : ℝ) - 1) * dphi γ (-1) := by
  rw [dphi_neg]; exact mu_eq_dphi_one d hγ

theorem mu_pos {γ : ℝ} {d : ℕ} (hd : 3 ≤ d) (hγ : 1 ≤ γ) : 0 < mu d γ := by
  unfold mu
  have h : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have := sinh_two_pos hγ
  apply div_pos _ this
  have : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  positivity

/-- `L(1) = -μ`. -/
theorem Lop_one {γ : ℝ} (d : ℕ) (hγ : 1 ≤ γ) : Lop d γ 1 = - mu d γ := by
  unfold Lop; rw [mu_eq_dphi_one d hγ]; ring

/-- `L(-1) = μ`. -/
theorem Lop_neg_one {γ : ℝ} (d : ℕ) (hγ : 1 ≤ γ) : Lop d γ (-1) = mu d γ := by
  unfold Lop; rw [mu_eq_dphi_neg_one d hγ]; ring

/-- Pole matching for `h`. -/
theorem hcorr_one (d : ℕ) (γ : ℝ) : hcorr d γ 1 = 0 := by simp [hcorr]

theorem hcorr_neg_one (d : ℕ) (γ : ℝ) : hcorr d γ (-1) = 0 := by simp [hcorr]

/-- The hyperbolic identity `μ φ(t) = (d-1) φ'(t) sinh(2γt)/sinh(2γ)`, all `t`. -/
theorem hyperbolic_identity {γ : ℝ} (d : ℕ) (hγ : 1 ≤ γ) (t : ℝ) :
    mu d γ * phi γ t = ((d : ℝ) - 1) * dphi γ t * (sinh (2 * γ * t) / sinh (2 * γ)) := by
  unfold mu phi dphi
  have h1 := (sinh_two_pos hγ).ne'
  have h2 := (tanh_pos_of_one_le hγ).ne'
  have h3 := (cosh_pos (γ * t)).ne'
  have e : sinh (2 * γ * t) = 2 * sinh (γ * t) * cosh (γ * t) := by
    rw [← sinh_two_mul]; ring_nf
  rw [e, tanh_eq_sinh_div_cosh (γ * t)]
  field_simp

/-- The quantity under the root exceeds `(d-2)²`. -/
theorem alpha_radicand_gt {γ : ℝ} {d : ℕ} (hd : 3 ≤ d) (hγ : 1 ≤ γ) :
    ((d : ℝ) - 2) ^ 2 < ((d : ℝ) - 2) ^ 2 + 4 * (2 * ((d : ℝ) - 1) * γ / sinh (2 * γ)) / (400 * γ ^ 2) := by
  have hμ := mu_pos hd hγ
  unfold mu at hμ
  have : 0 < 4 * (2 * ((d : ℝ) - 1) * γ / sinh (2 * γ)) / (400 * γ ^ 2) := by
    have : 0 < γ := by linarith
    positivity
  linarith

theorem alpha_pos {γ : ℝ} {d : ℕ} (hd : 3 ≤ d) (hγ : 1 ≤ γ) : 0 < alpha d γ := by
  unfold alpha
  have h : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have := (Real.lt_sqrt (by linarith)).2 (alpha_radicand_gt hd hγ)
  linarith

theorem beta_pos {γ : ℝ} {d : ℕ} (hd : 3 ≤ d) (hγ : 1 ≤ γ) : 0 < beta d γ := by
  unfold beta
  have h : (3 : ℝ) ≤ d := by exact_mod_cast hd
  linarith [alpha_pos hd hγ]

theorem beta_ge {γ : ℝ} {d : ℕ} (hd : 3 ≤ d) (hγ : 1 ≤ γ) : (d : ℝ) - 2 ≤ beta d γ := by
  unfold beta; linarith [alpha_pos hd hγ]

/-- `b α β = μ`. -/
theorem b_mul_alpha_mul_beta {γ : ℝ} {d : ℕ} (hd : 3 ≤ d) (hγ : 1 ≤ γ) :
    bconst γ * alpha d γ * beta d γ = mu d γ := by
  have hγ0 : 0 < γ := by linarith
  have hrad := alpha_radicand_gt hd hγ
  have hs := Real.sq_sqrt (show 0 ≤ ((d : ℝ) - 2) ^ 2 +
    4 * (2 * ((d : ℝ) - 1) * γ / sinh (2 * γ)) / (400 * γ ^ 2) by
      have := sq_nonneg ((d : ℝ) - 2); linarith)
  unfold bconst beta mu alpha
  set s := Real.sqrt (((d : ℝ) - 2) ^ 2 +
    4 * (2 * ((d : ℝ) - 1) * γ / sinh (2 * γ)) / (400 * γ ^ 2))
  have h1 : (400 * γ ^ 2) ≠ 0 := by positivity
  have : s ^ 2 - ((d : ℝ) - 2) ^ 2 = 4 * (2 * ((d : ℝ) - 1) * γ / sinh (2 * γ)) / (400 * γ ^ 2) := by
    linarith
  have h2 : (1 / 2 * (s - ((d : ℝ) - 2))) * (1 / 2 * (s - ((d : ℝ) - 2)) + ((d : ℝ) - 2))
      = (s ^ 2 - ((d : ℝ) - 2) ^ 2) / 4 := by ring
  rw [mul_assoc, h2, this]
  field_simp

/-- `α ≤ exp(-2γ)`. -/
theorem alpha_le_exp {γ : ℝ} {d : ℕ} (hd : 3 ≤ d) (hγ : 1 ≤ γ) : alpha d γ ≤ exp (-(2 * γ)) := by
  have hγ0 : 0 < γ := by linarith
  have h3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hq := b_mul_alpha_mul_beta hd hγ
  have hα := alpha_pos hd hγ
  have hβ := beta_ge hd hγ
  have hsh := sinh_two_pos hγ
  have hsg := sinh_two_ge hγ
  have he := exp_pos (2 * γ)
  have hD : (0 : ℝ) < (d : ℝ) - 2 := by linarith
  -- α * (b * (d-2)) ≤ μ
  have h1 : alpha d γ * (bconst γ * ((d : ℝ) - 2)) ≤ mu d γ := by
    rw [← hq]
    have : 0 ≤ bconst γ * alpha d γ := by unfold bconst; positivity
    nlinarith
  have hμ : mu d γ * sinh (2 * γ) = 2 * ((d : ℝ) - 1) * γ := by
    unfold mu; field_simp
  -- α * b * (d-2) * sinh ≤ 2 (d-1) γ ≤ 4 (d-2) γ
  have h2 : alpha d γ * (bconst γ * ((d : ℝ) - 2)) * sinh (2 * γ) ≤ 4 * ((d : ℝ) - 2) * γ := by
    calc _ ≤ mu d γ * sinh (2 * γ) := mul_le_mul_of_nonneg_right h1 hsh.le
      _ = 2 * ((d : ℝ) - 1) * γ := hμ
      _ ≤ _ := by nlinarith
  have h4 : alpha d γ * (100 * γ * sinh (2 * γ)) ≤ 1 := by
    unfold bconst at h2
    have : ((d : ℝ) - 2) * γ * (alpha d γ * (100 * γ * sinh (2 * γ)) * 4) ≤ ((d : ℝ) - 2) * γ * 4 := by
      nlinarith
    have hp : 0 < ((d : ℝ) - 2) * γ := by positivity
    have := le_of_mul_le_mul_left this hp
    linarith
  rw [exp_neg, ← one_div, le_div_iff₀ he]
  have h5 : exp (2 * γ) ≤ 100 * γ * sinh (2 * γ) := by
    nlinarith
  nlinarith

theorem alpha_lt_one {γ : ℝ} {d : ℕ} (hd : 3 ≤ d) (hγ : 1 ≤ γ) : alpha d γ < 1 := by
  refine (alpha_le_exp hd hγ).trans_lt ?_
  have := Real.exp_lt_exp.2 (show -(2 * γ) < 0 by linarith)
  simpa using this

/-- With `Λ = (80γ)²`: `α ≤ exp(-√Λ/40)`. -/
theorem alpha_le_exp_sqrt_80 {γ Λ : ℝ} {d : ℕ} (hd : 3 ≤ d) (hγ : 1 ≤ γ)
    (hΛ : Λ = (80 * γ) ^ 2) : alpha d γ ≤ exp (-(Real.sqrt Λ / 40)) := by
  have : Real.sqrt Λ / 40 = 2 * γ := by
    rw [hΛ, Real.sqrt_sq (by linarith)]; ring
  rw [this]; exact alpha_le_exp hd hγ

/-- With `Λ = (40γ)²`: `α ≤ exp(-√Λ/20)`. -/
theorem alpha_le_exp_sqrt_40 {γ Λ : ℝ} {d : ℕ} (hd : 3 ≤ d) (hγ : 1 ≤ γ)
    (hΛ : Λ = (40 * γ) ^ 2) : alpha d γ ≤ exp (-(Real.sqrt Λ / 20)) := by
  have : Real.sqrt Λ / 20 = 2 * γ := by
    rw [hΛ, Real.sqrt_sq (by linarith)]; ring
  rw [this]; exact alpha_le_exp hd hγ

/-! ### The correction functions -/

theorem Fcorr_hasDerivAt (γ t : ℝ) :
    HasDerivAt (Fcorr γ) (1 - 2 * γ * cosh (2 * γ * t) / sinh (2 * γ)) t := by
  have h1 : HasDerivAt (fun s => 2 * γ * s) (2 * γ) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * γ)
  have h2 := ((hasDerivAt_sinh (2 * γ * t)).comp t h1).div_const (sinh (2 * γ))
  have h3 := (hasDerivAt_id t).sub h2
  refine HasDerivAt.congr_deriv h3 ?_
  ring

theorem Fcorr_one {γ : ℝ} (hγ : 1 ≤ γ) : Fcorr γ 1 = 0 := by
  unfold Fcorr; rw [mul_one, div_self (sinh_two_pos hγ).ne']; ring

theorem Fcorr_neg (γ t : ℝ) : Fcorr γ (-t) = - Fcorr γ t := by
  unfold Fcorr; rw [mul_neg, sinh_neg]; ring

theorem Fcorr_neg_one {γ : ℝ} (hγ : 1 ≤ γ) : Fcorr γ (-1) = 0 := by
  rw [Fcorr_neg, Fcorr_one hγ]; simp

theorem abs_Fcorr_deriv_le {γ : ℝ} (hγ : 1 ≤ γ) {t : ℝ} (ht : |t| ≤ 1) :
    |1 - 2 * γ * cosh (2 * γ * t) / sinh (2 * γ)| ≤ 4 * γ := by
  have hsh := sinh_two_pos hγ
  have hc : cosh (2 * γ * t) ≤ cosh (2 * γ) := by
    rw [cosh_le_cosh]
    have : |2 * γ * t| = 2 * γ * |t| := by rw [abs_mul, abs_of_pos (by linarith)]
    rw [this, abs_of_pos (by linarith : (0 : ℝ) < 2 * γ)]
    nlinarith
  have hc2 := coth_two_le hγ
  have hq : cosh (2 * γ * t) / sinh (2 * γ) ≤ 3 / 2 := by
    rw [div_le_iff₀ hsh]; linarith
  have hq0 : 0 ≤ cosh (2 * γ * t) / sinh (2 * γ) := div_nonneg (cosh_pos _).le hsh.le
  have e : 2 * γ * cosh (2 * γ * t) / sinh (2 * γ) = 2 * γ * (cosh (2 * γ * t) / sinh (2 * γ)) := by
    ring
  rw [e, abs_le]
  constructor <;> nlinarith

theorem abs_Fcorr_le {γ : ℝ} (hγ : 1 ≤ γ) {t : ℝ} (ht : |t| ≤ 1) :
    |Fcorr γ t| ≤ 4 * γ * (1 - |t|) := by
  have hd : ∀ x ∈ Set.Icc (-1 : ℝ) 1, DifferentiableAt ℝ (Fcorr γ) x :=
    fun x _ => (Fcorr_hasDerivAt γ x).differentiableAt
  have hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ‖deriv (Fcorr γ) x‖ ≤ 4 * γ := by
    intro x hx
    rw [(Fcorr_hasDerivAt γ x).deriv, Real.norm_eq_abs]
    exact abs_Fcorr_deriv_le hγ (abs_le.2 ⟨hx.1, hx.2⟩)
  have hI : t ∈ Set.Icc (-1 : ℝ) 1 := ⟨(abs_le.1 ht).1, (abs_le.1 ht).2⟩
  have h1 := (abs_le.1 ht).2
  have h2 := (abs_le.1 ht).1
  rcases le_total 0 t with h | h
  · have := Convex.norm_image_sub_le_of_norm_deriv_le hd hb (convex_Icc (-1 : ℝ) 1)
      hI (⟨by norm_num, le_rfl⟩ : (1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1)
    rw [Fcorr_one hγ, Real.norm_eq_abs, Real.norm_eq_abs, zero_sub, abs_neg,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - t)] at this
    rwa [abs_of_nonneg h]
  · have := Convex.norm_image_sub_le_of_norm_deriv_le hd hb (convex_Icc (-1 : ℝ) 1)
      hI (⟨le_rfl, by norm_num⟩ : (-1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1)
    rw [Fcorr_neg_one hγ, Real.norm_eq_abs, Real.norm_eq_abs, zero_sub, abs_neg,
      abs_of_nonpos (by linarith : -1 - t ≤ 0)] at this
    rw [abs_of_nonpos h]
    linarith [this]


/-- `|F(t)| ≤ 4γ(1-t²)`. -/
theorem abs_Fcorr_le_sq {γ : ℝ} (hγ : 1 ≤ γ) {t : ℝ} (ht : |t| ≤ 1) :
    |Fcorr γ t| ≤ 4 * γ * (1 - t ^ 2) := by
  refine (abs_Fcorr_le hγ ht).trans ?_
  have h0 := abs_nonneg t
  have : t ^ 2 ≤ |t| := by
    rw [← sq_abs]; nlinarith
  nlinarith

/-- The cancellation identity `β h(t)(1-t²) φ'(t) = -L(t) - μ φ(t)` for `|t| ≤ 1`
(including `t = ±1`). -/
theorem cancellation_identity {γ : ℝ} {d : ℕ} (hd : 3 ≤ d) (hγ : 1 ≤ γ) {t : ℝ}
    (ht : |t| ≤ 1) :
    beta d γ * hcorr d γ t * (1 - t ^ 2) * dphi γ t = - Lop d γ t - mu d γ * phi γ t := by
  have hβ := (beta_pos hd hγ).ne'
  rcases lt_or_eq_of_le ht with h | h
  · have hlt : 1 - t ^ 2 ≠ 0 := by
      have : t ^ 2 < 1 := by rw [← sq_abs]; nlinarith [abs_nonneg t]
      linarith
    have hh : hcorr d γ t = (1 / beta d γ) * (2 * γ * tanh (γ * t) +
        ((d : ℝ) - 1) * (Fcorr γ t / (1 - t ^ 2))) := by simp [hcorr, h]
    rw [hh, hyperbolic_identity d hγ t]
    unfold Lop ddphi Fcorr
    field_simp
    ring
  · have h1 : t = 1 ∨ t = -1 := abs_eq (by norm_num) |>.1 h
    rcases h1 with rfl | rfl
    · rw [hcorr_one, Lop_one d hγ, phi_one hγ]; ring
    · rw [hcorr_neg_one, Lop_neg_one d hγ, phi_neg_one hγ]; ring

/-- `|h| ≤ 10γ` on `[-1,1]`. -/
theorem abs_hcorr_le {γ : ℝ} {d : ℕ} (hd : 3 ≤ d) (hγ : 1 ≤ γ) {t : ℝ} (ht : |t| ≤ 1) :
    |hcorr d γ t| ≤ 10 * γ := by
  have hγ0 : 0 < γ := by linarith
  have h3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  by_cases h : |t| < 1
  · have hlt : 0 < 1 - t ^ 2 := by
      have : t ^ 2 < 1 := by rw [← sq_abs]; nlinarith [abs_nonneg t]
      linarith
    have hh : hcorr d γ t = (1 / beta d γ) * (2 * γ * tanh (γ * t) +
        ((d : ℝ) - 1) * (Fcorr γ t / (1 - t ^ 2))) := by simp [hcorr, h]
    have hβ := beta_ge hd hγ
    have hβ0 : 0 < beta d γ := beta_pos hd hγ
    have hF : |Fcorr γ t / (1 - t ^ 2)| ≤ 4 * γ := by
      rw [abs_div, abs_of_pos hlt, div_le_iff₀ hlt]
      exact abs_Fcorr_le_sq hγ ht
    have hT := abs_tanh_lt_one (γ * t)
    have hinner : |2 * γ * tanh (γ * t) + ((d : ℝ) - 1) * (Fcorr γ t / (1 - t ^ 2))| ≤
        2 * γ + ((d : ℝ) - 1) * (4 * γ) := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul (2 * γ), abs_mul ((d : ℝ) - 1), abs_of_pos (by linarith : (0 : ℝ) < 2 * γ),
        abs_of_pos (by linarith : (0 : ℝ) < (d : ℝ) - 1)]
      have := mul_le_mul_of_nonneg_left hF (by linarith : (0 : ℝ) ≤ (d : ℝ) - 1)
      nlinarith
    rw [hh, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / beta d γ), one_div,
      inv_mul_le_iff₀ hβ0]
    refine hinner.trans ?_
    nlinarith
  · have : t = 1 ∨ t = -1 := (abs_eq (by norm_num)).1 (le_antisymm ht (not_lt.1 h))
    rcases this with rfl | rfl
    · rw [hcorr_one]; simp; linarith
    · rw [hcorr_neg_one]; simp; linarith

end PDE.Guerra
