module

public import EllipticRegularity.Guerra.Field.Flux
public import EllipticRegularity.Guerra.Scalar.Function

/-!
# Guerra sharpness: the scalar toolbox instantiates `ProfileData`

For `d ≥ 3`, `γ ≥ 1`, the profile `φ = phi γ`, the correction `h = hcorr d γ`,
`α = alpha d γ`, `μ = mu d γ` of `Guerra/Scalar/` satisfy every hypothesis in
`ProfileData`.
-/

@[expose] public section

namespace PDE.Guerra

open Real

theorem contDiff_phi (γ : ℝ) (hγ : 1 ≤ γ) {n : ℕ} : ContDiff ℝ n (phi γ) := by
  have h0 : tanh γ ≠ 0 := (tanh_pos_of_one_le hγ).ne'
  have e : phi γ = fun t => (sinh (γ * t) / cosh (γ * t)) / tanh γ := by
    funext t; simp [phi, tanh_eq_sinh_div_cosh]
  rw [e]
  refine ContDiff.div_const ?_ _
  exact ContDiff.div (Real.contDiff_sinh.comp (contDiff_const.mul contDiff_id))
    (Real.contDiff_cosh.comp (contDiff_const.mul contDiff_id)) fun t => (cosh_pos _).ne'

theorem deriv_phi (γ : ℝ) (hγ : 1 ≤ γ) : deriv (phi γ) = dphi γ := by
  funext t; exact (phi_hasDerivAt γ t hγ).deriv

theorem deriv_dphi (γ : ℝ) (hγ : 1 ≤ γ) : deriv (dphi γ) = ddphi γ := by
  funext t; exact (dphi_hasDerivAt γ t hγ).deriv

theorem profL_phi (d : ℕ) {γ : ℝ} (hγ : 1 ≤ γ) (t : ℝ) : profL d (phi γ) t = Lop d γ t := by
  unfold profL Lop
  rw [deriv_phi γ hγ, deriv_dphi γ hγ]

theorem measurable_hcorr (d : ℕ) (γ : ℝ) : Measurable (hcorr d γ) := by
  unfold hcorr Fcorr
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_lt (by fun_prop) measurable_const
  · have ht : Measurable (fun t : ℝ => tanh (γ * t)) := by
      simp only [tanh_eq_sinh_div_cosh]; fun_prop
    fun_prop

/-- `uFun` with the toolbox profile is the toolbox function `uProf`, that is the `u` of the
statement (for `i = ⟨d-1, _⟩`). -/
theorem uFun_phi_eq_uProf {d : ℕ} (i : Fin d) (γ α : ℝ) :
    uFun α (phi γ) i = uProf i γ α := by
  funext x
  by_cases hx : x = 0
  · subst hx; simp [uFun_zero, uProf_zero]
  · rw [uFun_of_ne α (phi γ) i hx, uProf_eq_of_ne i γ α hx]
    rfl

/-- The scalar toolbox supplies all the hypotheses of `ProfileData`. -/
theorem profileData_guerra {d : ℕ} (hd : 3 ≤ d) {γ : ℝ} (hγ : 1 ≤ γ) :
    ProfileData d γ (alpha d γ) (mu d γ) (phi γ) (hcorr d γ) where
  three_le := hd
  one_le := hγ
  alpha_pos := alpha_pos hd hγ
  smooth := contDiff_phi γ hγ
  dphi_pos := fun t => by rw [deriv_phi γ hγ]; exact dphi_pos hγ t
  phi_one := phi_one hγ
  phi_neg_one := phi_neg_one hγ
  h_meas := measurable_hcorr d γ
  h_bound := fun t ht => abs_hcorr_le hd hγ ht
  quad := by
    have := b_mul_alpha_mul_beta hd hγ
    unfold bcoef
    unfold beta bconst at this
    linarith
  cancel := fun t ht => by
    have := cancellation_identity hd hγ ht
    rw [profL_phi d hγ, deriv_phi γ hγ]
    unfold beta at this
    linarith

end PDE.Guerra
