module

public import EllipticRegularity.Guerra.Field.Divergence
public import EllipticRegularity.Guerra.Field.Elliptic

/-!
# Guerra sharpness: flux identity and `div(B ∇u) = 0`

The scalar facts of the proof (produced by the scalar toolbox `Guerra/Scalar/`) enter only
through the bundled hypotheses `ProfileData`; nothing else about `φ` and `h` is used.

The classical hypotheses of `integral_vecDot_grad_eq_zero_of_classical_divergence_punctured`
and `hasWeakGradientOn_of_punctured_classicalGradient` are provided in exactly their form:
`contDiffOn_guerraFlux_punctured`, `sum_classicalGradient_guerraFlux_punctured`,
`contDiffOn_uFun_punctured`, `classicalGradient_uFun_punctured`.
-/

@[expose] public section

open scoped BigOperators

namespace PDE.Guerra

noncomputable section

variable {d : ℕ}

/-- `L(t) = (1-t²) φ''(t) - (d-1) t φ'(t)`. -/
def profL (d : ℕ) (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  (1 - t ^ 2) * deriv (deriv φ) t - ((d : ℝ) - 1) * t * deriv φ t

/-- `Q(t) = -L(t)/β`, `β = α + d - 2`. -/
def profQ (d : ℕ) (α : ℝ) (φ : ℝ → ℝ) (t : ℝ) : ℝ := -(profL d φ t) / (α + d - 2)

/-- `f = Q - t φ'`. -/
def profF (d : ℕ) (α : ℝ) (φ : ℝ → ℝ) (t : ℝ) : ℝ := profQ d α φ t - t * deriv φ t

/-- The smooth flux `B ∇u = r^{α-2} f(t) x + r^{α-1} φ'(t) e_j`. -/
def guerraFlux (d : ℕ) (α : ℝ) (φ : ℝ → ℝ) (j : Fin d) : Vec d → Vec d :=
  fluxVec α (profF d α φ) (deriv φ) j

/-- The scalar facts about the profile that the ambient computation consumes (to be supplied
by the scalar toolbox): `φ` smooth with `φ' > 0` and `φ(±1) = ±1`; `h` measurable with
`|h| ≤ 10γ` on `[-1,1]`; `b α β = μ` with `b = 400γ²`, `β = α+d-2`; and the pole/interior
cancellation identity `β h (1-t²) φ' = -L - μ φ` on `[-1,1]`. -/
structure ProfileData (d : ℕ) (γ α μ : ℝ) (φ h : ℝ → ℝ) : Prop where
  three_le : 3 ≤ d
  one_le : 1 ≤ γ
  alpha_pos : 0 < α
  smooth : ContDiff ℝ 3 φ
  dphi_pos : ∀ t, 0 < deriv φ t
  phi_one : φ 1 = 1
  phi_neg_one : φ (-1) = -1
  h_meas : Measurable h
  h_bound : ∀ t, |t| ≤ 1 → |h t| ≤ 10 * γ
  quad : bcoef γ * α * (α + d - 2) = μ
  cancel : ∀ t, |t| ≤ 1 →
    (α + d - 2) * h t * (1 - t ^ 2) * deriv φ t = -(profL d φ t) - μ * φ t

theorem ProfileData.beta_pos {γ α μ : ℝ} {φ h : ℝ → ℝ} (hP : ProfileData d γ α μ φ h) :
    0 < α + d - 2 := by
  have := hP.three_le
  have h3 : (3 : ℝ) ≤ d := by exact_mod_cast this
  linarith [hP.alpha_pos]

theorem ProfileData.differentiable {γ α μ : ℝ} {φ h : ℝ → ℝ} (hP : ProfileData d γ α μ φ h) :
    Differentiable ℝ φ :=
  hP.smooth.differentiable (by norm_num)

theorem ProfileData.contDiff_dphi {γ α μ : ℝ} {φ h : ℝ → ℝ} (hP : ProfileData d γ α μ φ h) :
    ContDiff ℝ 2 (deriv φ) := by
  have h3 : ContDiff ℝ (2 + 1) φ := by norm_num; exact hP.smooth
  exact (contDiff_succ_iff_deriv.mp h3).2.2

theorem ProfileData.contDiff_ddphi {γ α μ : ℝ} {φ h : ℝ → ℝ} (hP : ProfileData d γ α μ φ h) :
    ContDiff ℝ 1 (deriv (deriv φ)) := by
  have h3 : ContDiff ℝ (1 + 1) (deriv φ) := by norm_num; exact hP.contDiff_dphi
  exact (contDiff_succ_iff_deriv.mp h3).2.2

theorem ProfileData.contDiff_profF {γ α μ : ℝ} {φ h : ℝ → ℝ} (hP : ProfileData d γ α μ φ h) :
    ContDiff ℝ 1 (profF d α φ) := by
  have h1 : ContDiff ℝ 1 (deriv φ) := hP.contDiff_dphi.of_le (by norm_num)
  have h2 := hP.contDiff_ddphi
  unfold profF profQ profL
  fun_prop

/-! ### The flux identity -/

/-- `B ∇u = r^{α-2} f(t) x + r^{α-1} φ'(t) e_j` for `x ≠ 0`. -/
theorem matVecMul_fieldMatrix_gradU {γ α μ : ℝ} {φ h : ℝ → ℝ}
    (hP : ProfileData d γ α μ φ h) (j : Fin d) {x : Vec d} (hx : x ≠ 0) :
    matVecMul (fieldMatrix γ h j x) (gradU α φ j x) = guerraFlux d α φ j x := by
  have hr := rad_pos hx
  have hr0 := hr.ne'
  have hβ := hP.beta_pos
  set t := lat j x with ht
  have hωq := vecDot_omega_qvec hx j
  have hqω : vecDot (qvec j x) (omega x) = 0 := by rw [vecDot_comm]; exact hωq
  have hg := gradU_eq_smul α φ j x
  have hωξ : vecDot (omega x) (gradU α φ j x) = rad x ^ (α - 1) * (α * φ t) := by
    rw [hg, vecDot_smul_right, vecDot_add_right, vecDot_smul_right, vecDot_smul_right,
      vecNormSq_omega hx, hωq]; ring
  have hYξ : vecDot (yvec h j x) (gradU α φ j x) =
      rad x ^ (α - 1) * (h t * (deriv φ t * (1 - t ^ 2))) := by
    rw [hg, yvec, vecDot_smul_left, vecDot_smul_right, vecDot_add_right, vecDot_smul_right,
      vecDot_smul_right, hqω, vecDot_qvec_qvec hx j]
    ring
  have hQ : bcoef γ * α * φ t + h t * (deriv φ t * (1 - t ^ 2)) = profQ d α φ t := by
    have hc := hP.cancel t (abs_lat_le_one j x)
    unfold profQ
    rw [eq_div_iff hβ.ne']
    have hq := hP.quad
    linear_combination (φ t) * hq + hc
  have e2 : rad x ^ (α - 1) = rad x ^ (α - 2) * rad x := by
    rw [← Real.rpow_add_one hr0]; congr 1; ring
  funext i
  rw [matVecMul_fieldMatrix, hωξ, hYξ]
  have hQ' : profQ d α φ t = bcoef γ * α * φ t + h t * (deriv φ t * (1 - t ^ 2)) := hQ.symm
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, guerraFlux, fluxVec, profF, hQ',
    gradU, qvec, omega, Pi.sub_apply, basisVec_apply, ← ht]
  rw [e2]
  have hti : t = x j / rad x := rfl
  by_cases hij : i = j
  · subst hij
    simp only [ite_true]
    field_simp
    ring
  · simp only [hij, ite_false]
    field_simp
    ring

/-! ### The equation away from the origin -/

/-- `div(B ∇u) = 0` on `ℝ^d ∖ {0}`, for the smooth flux expression. -/
theorem sum_classicalGradient_guerraFlux {γ α μ : ℝ} {φ h : ℝ → ℝ}
    (hP : ProfileData d γ α μ φ h) (j : Fin d) {x : Vec d} (hx : x ≠ 0) :
    ∑ i, classicalGradient (fun y : Vec d => guerraFlux d α φ j y i) x i = 0 := by
  have hβ := hP.beta_pos
  have hf : Differentiable ℝ (profF d α φ) :=
    hP.contDiff_profF.differentiable (by norm_num)
  have hg : Differentiable ℝ (deriv φ) :=
    (hP.contDiff_dphi.differentiable (by norm_num))
  unfold guerraFlux
  rw [sum_classicalGradient_fluxVec hf hg α j hx]
  have hQ : (α + d - 2) * profQ d α φ (lat j x) = -(profL d φ (lat j x)) := by
    unfold profQ; field_simp
  have : (α + d - 2) * profF d α φ (lat j x) + (α - 1) * lat j x * deriv φ (lat j x) +
      (1 - lat j x ^ 2) * deriv (deriv φ) (lat j x) = 0 := by
    unfold profF
    have := hQ
    unfold profL at this
    linear_combination this
  rw [this, mul_zero]

theorem contDiffOn_guerraFlux_apply {γ α μ : ℝ} {φ h : ℝ → ℝ}
    (hP : ProfileData d γ α μ φ h) (j i : Fin d) :
    ContDiffOn ℝ 1 (fun y : Vec d => guerraFlux d α φ j y i) ({0} : Set (Vec d))ᶜ :=
  contDiffOn_fluxVec_apply hP.contDiff_profF (hP.contDiff_dphi.of_le (by norm_num)) α j i

/-- Smoothness of the flux components on `U ∖ {0}`, in the form required by
`integral_vecDot_grad_eq_zero_of_classical_divergence_punctured`. -/
theorem contDiffOn_guerraFlux_punctured {γ α μ : ℝ} {φ h : ℝ → ℝ}
    (hP : ProfileData d γ α μ φ h) (j : Fin d) (U : Set (Vec d)) (i : Fin d) :
    ContDiffOn ℝ 1 (fun y : Vec d => guerraFlux d α φ j y i) (U \ {0}) :=
  (contDiffOn_guerraFlux_apply hP j i).mono fun _ hy => hy.2

/-- Divergence-free on `U ∖ {0}`, in the form required by
`integral_vecDot_grad_eq_zero_of_classical_divergence_punctured`. -/
theorem sum_classicalGradient_guerraFlux_punctured {γ α μ : ℝ} {φ h : ℝ → ℝ}
    (hP : ProfileData d γ α μ φ h) (j : Fin d) (U : Set (Vec d)) :
    ∀ x ∈ U \ {0},
      (∑ i : Fin d, classicalGradient (fun y : Vec d => guerraFlux d α φ j y i) x i) = 0 :=
  fun _ hx => sum_classicalGradient_guerraFlux hP j hx.2

/-- Smoothness of `u` on `U ∖ {0}` (hypothesis `hSmooth` of
`hasWeakGradientOn_of_punctured_classicalGradient`). -/
theorem contDiffOn_uFun_punctured {γ α μ : ℝ} {φ h : ℝ → ℝ}
    (hP : ProfileData d γ α μ φ h) (j : Fin d) (U : Set (Vec d)) :
    ContDiffOn ℝ 1 (uFun α φ j) (U \ {0}) :=
  (contDiffOn_uFun (hP.smooth.of_le (by norm_num)) α j).mono fun _ hy => hy.2

/-- The classical gradient of `u` on `U ∖ {0}` (hypothesis `hGrad` of
`hasWeakGradientOn_of_punctured_classicalGradient` with `G = gradU α φ j`). -/
theorem classicalGradient_uFun_punctured {γ α μ : ℝ} {φ h : ℝ → ℝ}
    (hP : ProfileData d γ α μ φ h) (j : Fin d) (U : Set (Vec d)) :
    ∀ x ∈ U \ {0}, classicalGradient (uFun α φ j) x = gradU α φ j x :=
  fun _ hx => classicalGradient_uFun hP.differentiable α j hx.2

/-- The flux of the symmetric field: `a ∇u = 4 B ∇u = 4 J` away from the origin, for a
symmetrizer `S` with the data of `guerra_symmetrize`. -/
theorem matVecMul_symField_gradU {γ α μ : ℝ} {φ h : ℝ → ℝ}
    (hP : ProfileData d γ α μ φ h) (j : Fin d) {S : Mat d → Vec d → Mat d}
    (hS : IsSymmetrizer (40 * γ) S) {x : Vec d} (hx : x ≠ 0) :
    matVecMul (symField γ h j S (gradU α φ j) x) (gradU α φ j x) =
      (4 : ℝ) • guerraFlux d α φ j x := by
  rw [symField_apply_self hP.one_le j hP.h_bound hS (gradU α φ j) hx,
    matVecMul_fieldMatrix_gradU hP j hx]

/-- The flux of the nonsymmetric field `2B`: `2B ∇u = 2 J` away from the origin. -/
theorem matVecMul_nonsymField_gradU {γ α μ : ℝ} {φ h : ℝ → ℝ}
    (hP : ProfileData d γ α μ φ h) (j : Fin d) {x : Vec d} (hx : x ≠ 0) :
    matVecMul (nonsymField γ h j x) (gradU α φ j x) = (2 : ℝ) • guerraFlux d α φ j x := by
  unfold nonsymField
  rw [matVecMul_smul', matVecMul_fieldMatrix_gradU hP j hx]

end

end PDE.Guerra
