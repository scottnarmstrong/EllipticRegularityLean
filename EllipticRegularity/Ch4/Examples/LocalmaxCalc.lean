module

public import EllipticRegularity.Ch4.Examples.Basic

/-!
# Calculus for the Proposition 4.12 example

Let `l = d - 1` be the last coordinate, `q(x) = Σ_{i < l} x_i²`, `S = 1 + Λ q`, `σ = √S` and
`φ = x_l²/2 - σ/(d-1)`, `u = exp φ`.  We compute `D_i φ`, `D_i D_i φ` and
`Σ_i w_i D_i D_i u`.
-/

@[expose] public section

namespace PDE.Ch4Examples

open MeasureTheory

section Calculus

variable {d : ℕ}

/-- The indicator (as a real number) of the "tangential" coordinates `i < d - 1`. -/
noncomputable def tq (d : ℕ) (i : Fin d) : ℝ := if i.val + 1 < d then 1 else 0

/-- The squared length of the tangential part. -/
noncomputable def qf (x : Vec d) : ℝ := ∑ i, tq d i * x i ^ 2

theorem contDiff_qf : ContDiff ℝ (⊤ : ℕ∞) (qf : Vec d → ℝ) := by
  unfold qf
  refine ContDiff.sum fun i _ => ?_
  exact contDiff_const.mul ((contDiff_apply ℝ ℝ i).pow 2)

theorem hasFDerivAt_qf (x : Vec d) :
    HasFDerivAt (qf : Vec d → ℝ)
      (∑ j, (tq d j * (2 * x j)) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j) x := by
  unfold qf
  refine HasFDerivAt.fun_sum fun j _ => ?_
  have h1 : HasFDerivAt (fun y : Vec d => y j)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j) x := hasFDerivAt_apply j x
  have h2 := (h1.pow 2).const_mul (tq d j)
  refine h2.congr_fderiv ?_
  simp only [Nat.add_one_sub_one, pow_one]
  ext v
  simp
  ring

theorem D_qf (i : Fin d) (x : Vec d) : D i qf x = 2 * tq d i * x i := by
  unfold D
  rw [(hasFDerivAt_qf x).fderiv]
  simp [basisVec_apply]
  ring

theorem D_qf_fun (i : Fin d) : D i qf = fun x => 2 * tq d i * x i := funext (D_qf i)

/-! ### The exponential of a smooth function -/

theorem D_exp (i : Fin d) {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    D i (fun x => Real.exp (φ x)) = fun x => Real.exp (φ x) * D i φ x := by
  funext x
  have h := (hφ.differentiable (by simp) x).hasFDerivAt.exp
  unfold D
  rw [h.fderiv]
  simp

theorem DD_exp (i : Fin d) {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Vec d) :
    D i (D i (fun x => Real.exp (φ x))) x =
      Real.exp (φ x) * (D i φ x ^ 2 + D i (D i φ) x) := by
  rw [D_exp i hφ]
  have h1 := (hφ.differentiable (by simp) x).hasFDerivAt.exp
  have h2 : HasFDerivAt (D i φ) (fderiv ℝ (D i φ) x) x :=
    ((contDiff_D i hφ).differentiable (by simp) x).hasFDerivAt
  have h3 := h1.mul h2
  change fderiv ℝ (fun x => Real.exp (φ x) * D i φ x) x (basisVec i) = _
  have h4 : HasFDerivAt (fun x => Real.exp (φ x) * D i φ x) _ x := h3
  rw [h4.fderiv]
  simp [D]
  ring

/-! ### The phase function -/

/-- `S = 1 + Λ q`. -/
noncomputable def Sf (Λ : ℝ) (x : Vec d) : ℝ := 1 + Λ * qf x

/-- The phase `φ = x_l²/2 - c √S`. -/
noncomputable def phiLM (Λ c : ℝ) (l : Fin d) (x : Vec d) : ℝ :=
  1 / 2 * x l ^ 2 - c * Real.sqrt (Sf Λ x)

theorem qf_nonneg (x : Vec d) : 0 ≤ qf x := by
  unfold qf
  refine Finset.sum_nonneg fun i _ => mul_nonneg ?_ (sq_nonneg _)
  unfold tq
  split_ifs <;> norm_num

theorem Sf_ge_one {Λ : ℝ} (hΛ : 0 ≤ Λ) (x : Vec d) : 1 ≤ Sf Λ x := by
  unfold Sf
  have := qf_nonneg x
  nlinarith

theorem contDiff_Sf (Λ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (Sf Λ : Vec d → ℝ) := by
  unfold Sf
  exact contDiff_const.add (contDiff_const.mul contDiff_qf)

theorem contDiff_phiLM {Λ : ℝ} (hΛ : 0 ≤ Λ) (c : ℝ) (l : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (phiLM Λ c l) := by
  unfold phiLM
  refine (contDiff_const.mul ((contDiff_apply ℝ ℝ l).pow 2)).sub (contDiff_const.mul ?_)
  exact (contDiff_Sf Λ).sqrt fun x => (lt_of_lt_of_le one_pos (Sf_ge_one hΛ x)).ne'

theorem hasFDerivAt_Sf (Λ : ℝ) (x : Vec d) :
    HasFDerivAt (Sf Λ : Vec d → ℝ)
      (Λ • ∑ j, (tq d j * (2 * x j)) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j) x := by
  unfold Sf
  exact ((hasFDerivAt_qf x).const_mul Λ).const_add 1

theorem D_phiLM {Λ : ℝ} (hΛ : 0 ≤ Λ) (c : ℝ) (l : Fin d) (i : Fin d) (x : Vec d) :
    D i (phiLM Λ c l) x =
      x l * (if l = i then 1 else 0) -
        c * (Λ * (2 * tq d i * x i) / (2 * Real.sqrt (Sf Λ x))) := by
  have hpos : Sf Λ x ≠ 0 := (lt_of_lt_of_le one_pos (Sf_ge_one hΛ x)).ne'
  have h1 : HasFDerivAt (fun y : Vec d => y l)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) l) x := hasFDerivAt_apply l x
  have h2 := ((h1.pow 2).const_mul (1 / 2 : ℝ)).sub (((hasFDerivAt_Sf Λ x).sqrt hpos).const_mul c)
  unfold D
  have h3 : HasFDerivAt (phiLM Λ c l) _ x := h2
  rw [h3.fderiv]
  simp [basisVec_apply]
  left
  field_simp

theorem D_phiLM_fun {Λ : ℝ} (hΛ : 0 ≤ Λ) (c : ℝ) (l : Fin d) (i : Fin d) :
    D i (phiLM Λ c l) = fun x =>
      x l * (if l = i then 1 else 0) -
        c * (Λ * (2 * tq d i * x i) / (2 * Real.sqrt (Sf Λ x))) :=
  funext (D_phiLM hΛ c l i)

theorem DD_phiLM {Λ : ℝ} (hΛ : 0 ≤ Λ) (c : ℝ) (l : Fin d) (i : Fin d) (x : Vec d) :
    D i (D i (phiLM Λ c l)) x =
      (if l = i then 1 else 0) -
        c * (Λ * tq d i / Real.sqrt (Sf Λ x) -
          Λ ^ 2 * tq d i ^ 2 * x i ^ 2 / Real.sqrt (Sf Λ x) ^ 3) := by
  have hpos : 0 < Sf Λ x := lt_of_lt_of_le one_pos (Sf_ge_one hΛ x)
  have hsq : 0 < Real.sqrt (Sf Λ x) := Real.sqrt_pos.2 hpos
  rw [D_phiLM_fun hΛ c l i]
  have h1 : HasFDerivAt (fun y : Vec d => y l)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) l) x := hasFDerivAt_apply l x
  have h1' : HasFDerivAt (fun y : Vec d => y i)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i) x := hasFDerivAt_apply i x
  have hσ := (hasFDerivAt_Sf Λ x).sqrt hpos.ne'
  have hnum : HasFDerivAt (fun y : Vec d => Λ * (2 * tq d i * y i))
      (Λ • (2 * tq d i) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i) x := by
    have := (h1'.const_mul (2 * tq d i)).const_mul Λ
    exact this.congr_fderiv (by ext v; simp)
  have hden := hσ.const_mul 2
  have hinv := (hasDerivAt_inv (show 2 * Real.sqrt (Sf Λ x) ≠ 0 by positivity)).comp_hasFDerivAt x
    hden
  have hdiv := hnum.mul hinv
  have hall := (h1.mul_const (if l = i then (1 : ℝ) else 0)).sub (hdiv.const_mul c)
  have h4 : HasFDerivAt (fun x : Vec d => x l * (if l = i then (1 : ℝ) else 0) -
        c * (Λ * (2 * tq d i * x i) * (2 * Real.sqrt (Sf Λ x))⁻¹)) _ x := hall
  have h5 : (fun x : Vec d => x l * (if l = i then (1 : ℝ) else 0) -
        c * (Λ * (2 * tq d i * x i) / (2 * Real.sqrt (Sf Λ x)))) = fun x : Vec d =>
        x l * (if l = i then (1 : ℝ) else 0) -
        c * (Λ * (2 * tq d i * x i) * (2 * Real.sqrt (Sf Λ x))⁻¹) := by
    funext y; rw [div_eq_mul_inv]
  change fderiv ℝ (fun x : Vec d => x l * (if l = i then (1 : ℝ) else 0) -
        c * (Λ * (2 * tq d i * x i) / (2 * Real.sqrt (Sf Λ x)))) x (basisVec i) = _
  rw [h5, h4.fderiv]
  by_cases hli : l = i
  · simp [hli, basisVec_apply]
    field_simp
    ring
  · simp [hli, basisVec_apply]
    field_simp
    ring

theorem tq_last {l : Fin d} (hl : l.val + 1 = d) : tq d l = 0 := by
  unfold tq
  simp [hl]

theorem tq_of_ne {l i : Fin d} (hl : l.val + 1 = d) (hi : l ≠ i) : tq d i = 1 := by
  unfold tq
  have : i.val ≠ l.val := fun h => hi (Fin.ext h.symm)
  have := i.isLt
  simp only [ite_eq_left_iff, not_lt]
  omega

/-- The integrand `Σ_i w_i D_i D_i u / u` is nonnegative. -/
theorem sum_weighted_nonneg {Λ : ℝ} (hΛ : 1 ≤ Λ) (hd : 2 ≤ d) (l : Fin d) (hl : l.val + 1 = d)
    (x : Vec d) :
    0 ≤ ∑ i, (if l = i then Λ else 1) *
      (D i (phiLM Λ ((d - 1 : ℝ))⁻¹ l) x ^ 2 + D i (D i (phiLM Λ ((d - 1 : ℝ))⁻¹ l)) x) := by
  set c : ℝ := ((d - 1 : ℝ))⁻¹ with hc
  have hΛ0 : 0 ≤ Λ := by linarith
  have hd1 : (1 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hc0 : 0 ≤ c := inv_nonneg.2 (by linarith)
  set σ := Real.sqrt (Sf Λ x) with hσ
  have hσ1 : 1 ≤ σ := by
    rw [hσ]
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ _ := Real.sqrt_le_sqrt (Sf_ge_one hΛ0 x)
  have hσpos : 0 < σ := by linarith
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ l)]
  have hl1 : (if l = l then Λ else 1) *
      (D l (phiLM Λ c l) x ^ 2 + D l (D l (phiLM Λ c l)) x) = Λ * (x l ^ 2 + 1) := by
    rw [D_phiLM hΛ0, DD_phiLM hΛ0, tq_last hl]
    simp
  have hi : ∀ i ∈ Finset.univ.erase l, -(c * Λ / σ) ≤ (if l = i then Λ else 1) *
      (D i (phiLM Λ c l) x ^ 2 + D i (D i (phiLM Λ c l)) x) := by
    intro i hi'
    have hne : l ≠ i := fun h => (Finset.mem_erase.1 hi').1 h.symm
    rw [D_phiLM hΛ0, DD_phiLM hΛ0, tq_of_ne hl hne]
    simp only [hne, ite_false, one_mul, mul_one, one_pow]
    rw [← hσ]
    have hpos' : 0 ≤ (c * Λ * x i / σ) ^ 2 + c * (Λ ^ 2 * x i ^ 2 / σ ^ 3) := by positivity
    have e2 : (x l * 0 - c * (Λ * (2 * x i) / (2 * σ))) ^ 2 +
        (0 - c * (Λ / σ - Λ ^ 2 * x i ^ 2 / σ ^ 3)) =
        ((c * Λ * x i / σ) ^ 2 + c * (Λ ^ 2 * x i ^ 2 / σ ^ 3)) - c * Λ / σ := by
      field_simp
      ring
    rw [e2]
    linarith
  have hsum := Finset.sum_le_sum hi
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ l), Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  have hcard : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [hcard] at hsum
  have h3 : ((d : ℝ) - 1) * -(c * Λ / σ) = -(Λ / σ) := by
    rw [hc]; field_simp
  rw [h3] at hsum
  rw [hl1]
  have h4 : Λ / σ ≤ Λ := div_le_self hΛ0 hσ1
  nlinarith [sq_nonneg (x l)]

end Calculus

end PDE.Ch4Examples
