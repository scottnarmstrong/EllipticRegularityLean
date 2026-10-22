module

public import PDEFoundation
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Guerra sharpness: the scalar profile toolbox

Pure one-variable facts for the explicit example of Proposition 4.30:
the angular profile `φ(t) = tanh(γ t)/tanh γ`, the correction `F`, `h`, the
constants `μ`, `b`, `α`, `β`, and the identities used at the poles.
-/

@[expose] public section

namespace PDE.Guerra

open Real

/-- Angular profile `φ(t) = tanh(γ t) / tanh γ`. -/
noncomputable def phi (γ t : ℝ) : ℝ := tanh (γ * t) / tanh γ

/-- The derivative `φ'(t) = γ / (tanh γ cosh²(γ t))`. -/
noncomputable def dphi (γ t : ℝ) : ℝ := γ / (tanh γ * cosh (γ * t) ^ 2)

/-- The second derivative `φ''(t) = -2γ tanh(γ t) φ'(t)`. -/
noncomputable def ddphi (γ t : ℝ) : ℝ := -2 * γ * tanh (γ * t) * dphi γ t

/-- `F(t) = t - sinh(2γ t)/sinh(2γ)`. -/
noncomputable def Fcorr (γ t : ℝ) : ℝ := t - sinh (2 * γ * t) / sinh (2 * γ)

/-- `μ = 2(d-1)γ / sinh(2γ)`. -/
noncomputable def mu (d : ℕ) (γ : ℝ) : ℝ := 2 * ((d : ℝ) - 1) * γ / sinh (2 * γ)

/-- `b = 400 γ²`. -/
noncomputable def bconst (γ : ℝ) : ℝ := 400 * γ ^ 2

/-- The homogeneity exponent (syntactically the one of `PDE.guerra_sharp_example`). -/
noncomputable def alpha (d : ℕ) (γ : ℝ) : ℝ :=
  (1 / 2) * (Real.sqrt (((d : ℝ) - 2) ^ 2 +
        4 * (2 * ((d : ℝ) - 1) * γ / Real.sinh (2 * γ)) / (400 * γ ^ 2)) - ((d : ℝ) - 2))

/-- `β = α + d - 2`. -/
noncomputable def beta (d : ℕ) (γ : ℝ) : ℝ := alpha d γ + ((d : ℝ) - 2)

/-- The correction `h(t) = (2γ tanh(γ t) + (d-1) F(t)/(1-t²))/β` for `|t| < 1`, and `h = 0`
otherwise (in particular `h(±1) = 0`). -/
noncomputable def hcorr (d : ℕ) (γ t : ℝ) : ℝ :=
  if |t| < 1 then
    (1 / beta d γ) * (2 * γ * tanh (γ * t) + ((d : ℝ) - 1) * (Fcorr γ t / (1 - t ^ 2)))
  else 0

/-- `L(t) = (1-t²) φ''(t) - (d-1) t φ'(t)`. -/
noncomputable def Lop (d : ℕ) (γ t : ℝ) : ℝ :=
  (1 - t ^ 2) * ddphi γ t - ((d : ℝ) - 1) * t * dphi γ t

/-! ### Elementary hyperbolic facts -/

theorem hasDerivAt_tanh' (x : ℝ) : HasDerivAt tanh (1 / cosh x ^ 2) x := by
  have h := (hasDerivAt_sinh x).div (hasDerivAt_cosh x) (cosh_pos x).ne'
  have e : tanh = fun y => sinh y / cosh y := funext tanh_eq_sinh_div_cosh
  rw [e]
  convert h using 1
  have := cosh_sq x
  field_simp
  nlinarith [this]

theorem tanh_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < tanh x := by
  rw [tanh_eq_sinh_div_cosh]
  exact div_pos (sinh_pos_iff.2 hx) (cosh_pos x)

theorem tanh_ge_half {γ : ℝ} (hγ : 1 ≤ γ) : 1 / 2 ≤ tanh γ := by
  rw [tanh_eq_sinh_div_cosh, le_div_iff₀ (cosh_pos γ), sinh_eq, cosh_eq]
  have h1 : 3 ≤ exp (2 * γ) := by
    have := add_one_le_exp (2 * γ); linarith
  have h2 : exp (2 * γ) = exp γ * exp γ := by rw [← exp_add]; ring_nf
  have h3 : exp (-γ) * exp γ = 1 := by rw [← exp_add]; simp
  have h4 := exp_pos γ
  have h5 := exp_pos (-γ)
  nlinarith [mul_pos h4 h5]

theorem sinh_two_ge {γ : ℝ} (hγ : 1 ≤ γ) : exp (2 * γ) / 3 ≤ sinh (2 * γ) := by
  rw [sinh_eq]
  have h1 : 3 ≤ exp (4 * γ) := by
    have := add_one_le_exp (4 * γ); linarith
  have h2 : exp (4 * γ) = exp (2 * γ) * exp (2 * γ) := by rw [← exp_add]; ring_nf
  have h3 : exp (-(2 * γ)) * exp (2 * γ) = 1 := by rw [← exp_add]; simp
  have h4 := exp_pos (2 * γ)
  have h5 := exp_pos (-(2 * γ))
  nlinarith [mul_pos h4 h5]

theorem sinh_two_pos {γ : ℝ} (hγ : 1 ≤ γ) : 0 < sinh (2 * γ) :=
  sinh_pos_iff.2 (by linarith)

theorem tanh_pos_of_one_le {γ : ℝ} (hγ : 1 ≤ γ) : 0 < tanh γ :=
  tanh_pos_of_pos (by linarith)

theorem coth_two_le {γ : ℝ} (hγ : 1 ≤ γ) : cosh (2 * γ) ≤ 3 / 2 * sinh (2 * γ) := by
  rw [sinh_eq, cosh_eq]
  have h1 : 5 ≤ exp (4 * γ) := by
    have := add_one_le_exp (4 * γ); linarith
  have h2 : exp (4 * γ) = exp (2 * γ) * exp (2 * γ) := by rw [← exp_add]; ring_nf
  have h3 : exp (-(2 * γ)) * exp (2 * γ) = 1 := by rw [← exp_add]; simp
  have h4 := exp_pos (2 * γ)
  have h5 := exp_pos (-(2 * γ))
  nlinarith [mul_pos h4 h5]

/-! ### The profile -/

theorem phi_hasDerivAt (γ t : ℝ) (hγ : 1 ≤ γ) : HasDerivAt (phi γ) (dphi γ t) t := by
  have h1 : HasDerivAt (fun s => γ * s) γ t := by simpa using (hasDerivAt_id t).const_mul γ
  have h2 := (hasDerivAt_tanh' (γ * t)).comp t h1
  have h3 := h2.div_const (tanh γ)
  refine HasDerivAt.congr_deriv h3 ?_
  unfold dphi
  have := (tanh_pos_of_one_le hγ).ne'
  have := (cosh_pos (γ * t)).ne'
  field_simp

theorem dphi_hasDerivAt (γ t : ℝ) (hγ : 1 ≤ γ) : HasDerivAt (dphi γ) (ddphi γ t) t := by
  have h1 : HasDerivAt (fun s => γ * s) γ t := by simpa using (hasDerivAt_id t).const_mul γ
  have h2 := (hasDerivAt_cosh (γ * t)).comp t h1
  have h3 := (h2.pow 2).const_mul (tanh γ)
  have h4 := (hasDerivAt_const t γ).div h3 (mul_ne_zero (tanh_pos_of_one_le hγ).ne'
    (pow_ne_zero 2 (cosh_pos _).ne'))
  refine HasDerivAt.congr_deriv h4 ?_
  simp only [Function.comp_apply, Pi.pow_apply]
  unfold ddphi dphi
  have := (tanh_pos_of_one_le hγ).ne'
  have := (cosh_pos (γ * t)).ne'
  rw [tanh_eq_sinh_div_cosh (γ * t)]
  field_simp
  ring

theorem phi_neg (γ t : ℝ) : phi γ (-t) = - phi γ t := by
  unfold phi; rw [mul_neg, tanh_neg]; ring

theorem phi_one {γ : ℝ} (hγ : 1 ≤ γ) : phi γ 1 = 1 := by
  unfold phi; rw [mul_one]; exact div_self (tanh_pos_of_one_le hγ).ne'

theorem phi_neg_one {γ : ℝ} (hγ : 1 ≤ γ) : phi γ (-1) = -1 := by
  rw [phi_neg, phi_one hγ]

theorem tanh_le_tanh_of_nonneg {γ t : ℝ} (ht1 : t ≤ 1) (hγ : 0 ≤ γ) :
    tanh (γ * t) ≤ tanh γ := by
  rw [tanh_eq_sinh_div_cosh, tanh_eq_sinh_div_cosh, div_le_div_iff₀ (cosh_pos _) (cosh_pos _)]
  have h := sinh_nonneg_iff.2 (show 0 ≤ γ - γ * t by nlinarith)
  rw [sinh_sub] at h
  linarith

theorem abs_tanh_le_tanh {γ t : ℝ} (hγ : 0 ≤ γ) (ht : |t| ≤ 1) : |tanh (γ * t)| ≤ tanh γ := by
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h] at ht
    have h0 : 0 ≤ tanh (γ * t) := by
      rw [tanh_eq_sinh_div_cosh]
      exact div_nonneg (sinh_nonneg_iff.2 (mul_nonneg hγ h)) (cosh_pos _).le
    rw [abs_of_nonneg h0]
    exact tanh_le_tanh_of_nonneg ht hγ
  · rw [abs_of_nonpos h] at ht
    have := tanh_le_tanh_of_nonneg (t := -t) ht hγ
    rw [mul_neg, tanh_neg] at this
    rw [abs_of_nonpos]
    · linarith
    · rw [tanh_eq_sinh_div_cosh]
      exact div_nonpos_of_nonpos_of_nonneg (sinh_nonpos_iff.2 (mul_nonpos_of_nonneg_of_nonpos hγ h)) (cosh_pos _).le

theorem abs_phi_le_one {γ t : ℝ} (hγ : 1 ≤ γ) (ht : |t| ≤ 1) : |phi γ t| ≤ 1 := by
  have hp := tanh_pos_of_one_le hγ
  unfold phi
  rw [abs_div, abs_of_pos hp, div_le_one hp]
  exact abs_tanh_le_tanh (by linarith) ht

theorem dphi_pos {γ : ℝ} (hγ : 1 ≤ γ) (t : ℝ) : 0 < dphi γ t := by
  unfold dphi
  have := tanh_pos_of_one_le hγ
  have := cosh_pos (γ * t)
  positivity

theorem dphi_le {γ : ℝ} (hγ : 1 ≤ γ) (t : ℝ) : dphi γ t ≤ γ / tanh γ := by
  unfold dphi
  have hp := tanh_pos_of_one_le hγ
  have h1 : 1 ≤ cosh (γ * t) ^ 2 := by
    have := one_le_cosh (γ * t); nlinarith
  apply div_le_div_of_nonneg_left (by linarith) hp
  nlinarith

/-- `φ' ≤ 2γ`. -/
theorem dphi_le_two_mul {γ : ℝ} (hγ : 1 ≤ γ) (t : ℝ) : dphi γ t ≤ 2 * γ := by
  refine (dphi_le hγ t).trans ?_
  have := tanh_ge_half hγ
  have hp := tanh_pos_of_one_le hγ
  rw [div_le_iff₀ hp]
  nlinarith

theorem dphi_neg (γ t : ℝ) : dphi γ (-t) = dphi γ t := by
  unfold dphi; rw [mul_neg, cosh_neg]

theorem abs_ddphi_le {γ : ℝ} (hγ : 1 ≤ γ) (t : ℝ) : |ddphi γ t| ≤ 2 * γ * dphi γ t := by
  unfold ddphi
  have h := dphi_pos hγ t
  have h1 := abs_tanh_lt_one (γ * t)
  have hγ0 : 0 < γ := by linarith
  rw [show -2 * γ * tanh (γ * t) * dphi γ t = -(2 * γ * dphi γ t) * tanh (γ * t) by ring,
    abs_mul, abs_neg, abs_of_pos (by positivity)]
  nlinarith [mul_pos (mul_pos (by norm_num : (0:ℝ) < 2) hγ0) h]

/-- Lipschitz bound `|φ(a) - φ(b)| ≤ 2γ |a - b|`. -/
theorem abs_phi_sub_le {γ : ℝ} (hγ : 1 ≤ γ) (a b : ℝ) :
    |phi γ a - phi γ b| ≤ 2 * γ * |a - b| := by
  have hd : ∀ x ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ (phi γ) x :=
    fun x _ => (phi_hasDerivAt γ x hγ).differentiableAt
  have hb : ∀ x ∈ (Set.univ : Set ℝ), ‖deriv (phi γ) x‖ ≤ 2 * γ := by
    intro x _
    rw [(phi_hasDerivAt γ x hγ).deriv, Real.norm_eq_abs, abs_of_pos (dphi_pos hγ x)]
    exact dphi_le_two_mul hγ x
  have := Convex.norm_image_sub_le_of_norm_deriv_le hd hb convex_univ
    (Set.mem_univ b) (Set.mem_univ a)
  simpa [Real.norm_eq_abs] using this

end PDE.Guerra
