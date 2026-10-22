module

public import PDEFoundation.Euler.TimeKernel
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Time-mollified product rule (abstract Fubini identity)

Pure real analysis.  Let `F(τ,σ)` be the pairing of a first weak solution at time `τ` with a smooth
spatial field built from a second weak solution at time `σ`; `H`, `Kt` the corresponding quadratic
terms.  If `F` satisfies, for a.e. `σ`, the first solution's time-weak formulation in `τ`
(with datum term `D1 σ`), and for a.e. `τ`, the second solution's time-weak formulation in `σ`
(with datum term `D2 τ`), then the doubly mollified diagonal identity holds for every cut-off `χ`:

`∫ χ' (η_δ ⋆ F) + ∫ χ η_δ ⋆ (H + Kt) + χ(0) ∫ η_δ D1 + ∫ χ η_δ D2 = 0`.

The proof is the symmetric trick `χ'(τ) η(σ-τ) = ∂_τ[χ(τ) η(σ-τ)] + χ(τ) η'(σ-τ)`.
-/

@[expose] public section

open MeasureTheory Set Filter

namespace PDE

section Aux

variable {T : ℝ}

theorem exists_bound_ae_prod {g : ℝ → ℝ → ℝ} (hg : Continuous (fun p : ℝ × ℝ => g p.1 p.2)) :
    ∃ C, ∀ᵐ p ∂((volume.restrict (Icc (0 : ℝ) T)).prod (volume.restrict (Icc (0 : ℝ) T))),
      ‖g p.1 p.2‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Icc (0 : ℝ) T ×ˢ Icc (0 : ℝ) T)).exists_bound_of_continuousOn hg.continuousOn
  refine ⟨C, ?_⟩
  rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Icc)]
  exact Filter.Eventually.of_forall fun p hp => hC p hp

theorem integrable_continuous_mul {f g : ℝ → ℝ → ℝ}
    (hf : Integrable (fun p : ℝ × ℝ => f p.1 p.2)
      ((volume.restrict (Icc (0 : ℝ) T)).prod (volume.restrict (Icc (0 : ℝ) T))))
    (hg : Continuous (fun p : ℝ × ℝ => g p.1 p.2)) :
    Integrable (fun p : ℝ × ℝ => g p.1 p.2 * f p.1 p.2)
      ((volume.restrict (Icc (0 : ℝ) T)).prod (volume.restrict (Icc (0 : ℝ) T))) := by
  obtain ⟨C, hC⟩ := exists_bound_ae_prod (T := T) hg
  exact hf.bdd_mul hg.aestronglyMeasurable hC

end Aux

section Cutoff

theorem contDiff_one_le {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Differentiable ℝ f := hf.differentiable (by simp)

theorem continuous_deriv_of_contDiff_top {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Continuous (deriv f) := hf.continuous_deriv (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))

theorem hasDerivAt_etaK_comp (n : ℕ) (σ τ : ℝ) :
    HasDerivAt (fun τ => etaK n (σ - τ)) (-(deriv (etaK n) (σ - τ))) τ := by
  have h1 : HasDerivAt (etaK n) (deriv (etaK n) (σ - τ)) (σ - τ) :=
    ((contDiff_one_le (etaK_contDiff n)) (σ - τ)).hasDerivAt
  have h2 := h1.comp τ ((hasDerivAt_id τ).const_sub σ)
  convert h2 using 1
  · rfl
  · ring

theorem contDiff_etaK_comp (n : ℕ) (σ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun τ => etaK n (σ - τ)) :=
  (etaK_contDiff n).comp (contDiff_const.sub contDiff_id)

theorem hasDerivAt_cutoff_etaK {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (n : ℕ) (σ τ : ℝ) :
    HasDerivAt (fun τ => χ τ * etaK n (σ - τ))
      (deriv χ τ * etaK n (σ - τ) + χ τ * (-(deriv (etaK n) (σ - τ)))) τ :=
  ((contDiff_one_le hχ) τ).hasDerivAt.mul (hasDerivAt_etaK_comp n σ τ)

theorem contDiff_cutoff_etaK {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (n : ℕ) (σ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun τ => χ τ * etaK n (σ - τ)) :=
  hχ.mul (contDiff_etaK_comp n σ)

end Cutoff

/-- **Time-mollified product rule.**  See the module docstring. -/
theorem time_product_identity (n : ℕ) {T : ℝ} {F H Kt : ℝ → ℝ → ℝ} {D1 D2 : ℝ → ℝ}
    (hF : Integrable (fun p : ℝ × ℝ => F p.1 p.2)
      ((volume.restrict (Icc (0 : ℝ) T)).prod (volume.restrict (Icc (0 : ℝ) T))))
    (hH : Integrable (fun p : ℝ × ℝ => H p.1 p.2)
      ((volume.restrict (Icc (0 : ℝ) T)).prod (volume.restrict (Icc (0 : ℝ) T))))
    (hK : Integrable (fun p : ℝ × ℝ => Kt p.1 p.2)
      ((volume.restrict (Icc (0 : ℝ) T)).prod (volume.restrict (Icc (0 : ℝ) T))))
    (hD1 : Integrable D1 (volume.restrict (Icc (0 : ℝ) T)))
    (hD2 : Integrable D2 (volume.restrict (Icc (0 : ℝ) T)))
    (hU : ∀ᵐ σ ∂(volume.restrict (Icc (0 : ℝ) T)), ∀ θ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ →
      (∃ b, b < T ∧ ∀ τ, b ≤ τ → θ τ = 0) →
      ∫ τ, (deriv θ τ * F τ σ + θ τ * H τ σ) ∂(volume.restrict (Icc (0 : ℝ) T)) + θ 0 * D1 σ = 0)
    (hV : ∀ᵐ τ ∂(volume.restrict (Icc (0 : ℝ) T)), ∀ θ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ →
      (∃ b, b < T ∧ ∀ σ, b ≤ σ → θ σ = 0) →
      ∫ σ, (deriv θ σ * F τ σ + θ σ * Kt τ σ) ∂(volume.restrict (Icc (0 : ℝ) T)) + θ 0 * D2 τ = 0)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) {b : ℝ} (hb : b + tDelta n < T)
    (hχb : ∀ τ, b ≤ τ → χ τ = 0) :
    ∫ τ, deriv χ τ * ∫ σ, etaK n (σ - τ) * F τ σ ∂(volume.restrict (Icc (0 : ℝ) T))
        ∂(volume.restrict (Icc (0 : ℝ) T)) +
      ∫ τ, χ τ * ∫ σ, etaK n (σ - τ) * H τ σ ∂(volume.restrict (Icc (0 : ℝ) T))
        ∂(volume.restrict (Icc (0 : ℝ) T)) +
      ∫ τ, χ τ * ∫ σ, etaK n (σ - τ) * Kt τ σ ∂(volume.restrict (Icc (0 : ℝ) T))
        ∂(volume.restrict (Icc (0 : ℝ) T)) +
      χ 0 * ∫ σ, etaK n σ * D1 σ ∂(volume.restrict (Icc (0 : ℝ) T)) +
      ∫ τ, χ τ * (etaK n τ * D2 τ) ∂(volume.restrict (Icc (0 : ℝ) T)) = 0 := by
  set ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) T) with hν
  have hδ := tDelta_pos n
  have hηc : Continuous (etaK n) := (etaK_contDiff n).continuous
  have hη'c : Continuous (deriv (etaK n)) := continuous_deriv_of_contDiff_top (etaK_contDiff n)
  have hχ'c : Continuous (deriv χ) := continuous_deriv_of_contDiff_top hχ
  have hχc : Continuous χ := hχ.continuous
  have hs : Continuous (fun p : ℝ × ℝ => p.2 - p.1) := continuous_snd.sub continuous_fst
  -- integrable products
  have iA : Integrable (fun p : ℝ × ℝ => deriv χ p.1 * etaK n (p.2 - p.1) * F p.1 p.2) (ν.prod ν) :=
    integrable_continuous_mul (g := fun τ σ => deriv χ τ * etaK n (σ - τ)) hF
      ((hχ'c.comp continuous_fst).mul (hηc.comp hs))
  have iC : Integrable (fun p : ℝ × ℝ => χ p.1 * deriv (etaK n) (p.2 - p.1) * F p.1 p.2) (ν.prod ν) :=
    integrable_continuous_mul (g := fun τ σ => χ τ * deriv (etaK n) (σ - τ)) hF
      ((hχc.comp continuous_fst).mul (hη'c.comp hs))
  have iB : Integrable (fun p : ℝ × ℝ => χ p.1 * etaK n (p.2 - p.1) * H p.1 p.2) (ν.prod ν) :=
    integrable_continuous_mul (g := fun τ σ => χ τ * etaK n (σ - τ)) hH
      ((hχc.comp continuous_fst).mul (hηc.comp hs))
  have iK : Integrable (fun p : ℝ × ℝ => χ p.1 * etaK n (p.2 - p.1) * Kt p.1 p.2) (ν.prod ν) :=
    integrable_continuous_mul (g := fun τ σ => χ τ * etaK n (σ - τ)) hK
      ((hχc.comp continuous_fst).mul (hηc.comp hs))
  have iF : Integrable (fun p : ℝ × ℝ => etaK n (p.2 - p.1) * F p.1 p.2) (ν.prod ν) :=
    integrable_continuous_mul (g := fun τ σ => etaK n (σ - τ)) hF (hηc.comp hs)
  have iH : Integrable (fun p : ℝ × ℝ => etaK n (p.2 - p.1) * H p.1 p.2) (ν.prod ν) :=
    integrable_continuous_mul (g := fun τ σ => etaK n (σ - τ)) hH (hηc.comp hs)
  have iKt : Integrable (fun p : ℝ × ℝ => etaK n (p.2 - p.1) * Kt p.1 p.2) (ν.prod ν) :=
    integrable_continuous_mul (g := fun τ σ => etaK n (σ - τ)) hK (hηc.comp hs)
  have iC2 : Integrable (fun p : ℝ × ℝ => deriv (etaK n) (p.2 - p.1) * F p.1 p.2) (ν.prod ν) :=
    integrable_continuous_mul (g := fun τ σ => deriv (etaK n) (σ - τ)) hF (hη'c.comp hs)
  obtain ⟨Cη, hCη⟩ := etaK_le_const n
  have hD1' : Integrable (fun σ => etaK n σ * D1 σ) ν :=
    hD1.bdd_mul hηc.aestronglyMeasurable (Filter.Eventually.of_forall fun σ => by
      simpa [Real.norm_eq_abs] using hCη σ)
  have hD2' : Integrable (fun τ => χ τ * (etaK n τ * D2 τ)) ν := by
    have h1 : Integrable (fun τ => etaK n τ * D2 τ) ν :=
      hD2.bdd_mul hηc.aestronglyMeasurable (Filter.Eventually.of_forall fun σ => by
        simpa [Real.norm_eq_abs] using hCη σ)
    obtain ⟨Cχ, hCχ⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).exists_bound_of_continuousOn
      hχc.continuousOn
    exact h1.bdd_mul hχc.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall hCχ))
  -- the σ-identity coming from the first weak formulation
  have hσ : ∀ᵐ σ ∂ν, ∫ τ, deriv χ τ * etaK n (σ - τ) * F τ σ ∂ν =
      (-(∫ τ, χ τ * etaK n (σ - τ) * H τ σ ∂ν) - χ 0 * (etaK n σ * D1 σ)) +
        ∫ τ, χ τ * deriv (etaK n) (σ - τ) * F τ σ ∂ν := by
    filter_upwards [hU, iA.prod_left_ae, iC.prod_left_ae, iB.prod_left_ae] with σ h ia ic ib
    have hθ := h _ (contDiff_cutoff_etaK hχ n σ)
      ⟨b, by linarith, fun τ hτ => by simp [hχb τ hτ]⟩
    have hder : ∀ τ, deriv (fun τ => χ τ * etaK n (σ - τ)) τ =
        deriv χ τ * etaK n (σ - τ) + χ τ * (-(deriv (etaK n) (σ - τ))) :=
      fun τ => (hasDerivAt_cutoff_etaK hχ n σ τ).deriv
    have key : ∫ τ, (deriv (fun τ => χ τ * etaK n (σ - τ)) τ * F τ σ +
          (χ τ * etaK n (σ - τ)) * H τ σ) ∂ν =
        ((∫ τ, deriv χ τ * etaK n (σ - τ) * F τ σ ∂ν) -
          ∫ τ, χ τ * deriv (etaK n) (σ - τ) * F τ σ ∂ν) +
          ∫ τ, χ τ * etaK n (σ - τ) * H τ σ ∂ν := by
      have ias : Integrable (fun τ => deriv χ τ * etaK n (σ - τ) * F τ σ -
          χ τ * deriv (etaK n) (σ - τ) * F τ σ) ν := ia.sub ic
      rw [← integral_sub ia ic, ← integral_add ias ib]
      refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
      simp only [hder]
      ring
    simp only [sub_zero] at hθ
    rw [key] at hθ
    linarith
  -- the τ-identity coming from the second weak formulation
  have hτ : ∀ᵐ τ ∂ν, ∫ σ, χ τ * deriv (etaK n) (σ - τ) * F τ σ ∂ν =
      -(∫ σ, χ τ * etaK n (σ - τ) * Kt τ σ ∂ν) - χ τ * (etaK n τ * D2 τ) := by
    filter_upwards [hV, iC2.prod_right_ae, iKt.prod_right_ae] with τ h ic ik
    by_cases hτb : b ≤ τ
    · simp [hχb τ hτb]
    · push Not at hτb
      have hθ := h (fun σ => etaK n (σ - τ)) ((etaK_contDiff n).comp (contDiff_id.sub contDiff_const))
        ⟨τ + tDelta n, by linarith, fun σ hσ => etaK_eq_zero n (by
          rw [abs_of_nonneg (by linarith [tDelta_pos n])]; linarith)⟩
      have hder : ∀ σ, deriv (fun σ => etaK n (σ - τ)) σ = deriv (etaK n) (σ - τ) := by
        intro σ
        have h1 : HasDerivAt (etaK n) (deriv (etaK n) (σ - τ)) (σ - τ) :=
          ((contDiff_one_le (etaK_contDiff n)) (σ - τ)).hasDerivAt
        have h2 := h1.comp σ ((hasDerivAt_id σ).sub_const τ)
        exact h2.deriv.trans (by simp)
      simp only [hder, zero_sub, etaK_neg] at hθ
      have hsplit : ∫ σ, (deriv (etaK n) (σ - τ) * F τ σ + etaK n (σ - τ) * Kt τ σ) ∂ν =
          (∫ σ, deriv (etaK n) (σ - τ) * F τ σ ∂ν) + ∫ σ, etaK n (σ - τ) * Kt τ σ ∂ν :=
        integral_add ic ik
      rw [hsplit] at hθ
      have e1 : ∫ σ, χ τ * deriv (etaK n) (σ - τ) * F τ σ ∂ν =
          χ τ * ∫ σ, deriv (etaK n) (σ - τ) * F τ σ ∂ν := by
        rw [← integral_const_mul]; simp only [mul_assoc]
      have e2 : ∫ σ, χ τ * etaK n (σ - τ) * Kt τ σ ∂ν =
          χ τ * ∫ σ, etaK n (σ - τ) * Kt τ σ ∂ν := by
        rw [← integral_const_mul]; simp only [mul_assoc]
      rw [e1, e2]
      have := congrArg (fun r => χ τ * r) hθ
      simp only [mul_zero] at this
      linarith
  -- assembly
  have s1 : ∀ τ, deriv χ τ * ∫ σ, etaK n (σ - τ) * F τ σ ∂ν =
      ∫ σ, deriv χ τ * etaK n (σ - τ) * F τ σ ∂ν := by
    intro τ; rw [← integral_const_mul]; simp only [mul_assoc]
  have IA' : Integrable (fun σ => ∫ τ, χ τ * etaK n (σ - τ) * H τ σ ∂ν) ν := iB.integral_prod_right
  have IC' : Integrable (fun σ => ∫ τ, χ τ * deriv (etaK n) (σ - τ) * F τ σ ∂ν) ν :=
    iC.integral_prod_right
  have ID' : Integrable (fun σ => χ 0 * (etaK n σ * D1 σ)) ν := hD1'.const_mul _
  have IAn : Integrable (fun σ => -(∫ τ, χ τ * etaK n (σ - τ) * H τ σ ∂ν)) ν := IA'.neg
  have IAD : Integrable (fun σ => -(∫ τ, χ τ * etaK n (σ - τ) * H τ σ ∂ν) -
      χ 0 * (etaK n σ * D1 σ)) ν := IAn.sub ID'
  have E1 : ∫ τ, deriv χ τ * ∫ σ, etaK n (σ - τ) * F τ σ ∂ν ∂ν =
      -(∫ σ, ∫ τ, χ τ * etaK n (σ - τ) * H τ σ ∂ν ∂ν) - χ 0 * ∫ σ, etaK n σ * D1 σ ∂ν +
        ∫ σ, ∫ τ, χ τ * deriv (etaK n) (σ - τ) * F τ σ ∂ν ∂ν := by
    simp only [s1]
    rw [integral_integral_swap (f := fun τ σ => deriv χ τ * etaK n (σ - τ) * F τ σ) iA,
      integral_congr_ae hσ, integral_add IAD IC', integral_sub IAn ID', integral_neg,
      integral_const_mul]
  have A2 : ∫ σ, ∫ τ, χ τ * etaK n (σ - τ) * H τ σ ∂ν ∂ν =
      ∫ τ, ∫ σ, χ τ * etaK n (σ - τ) * H τ σ ∂ν ∂ν :=
    (integral_integral_swap (f := fun τ σ => χ τ * etaK n (σ - τ) * H τ σ) iB).symm
  have C2 : ∫ σ, ∫ τ, χ τ * deriv (etaK n) (σ - τ) * F τ σ ∂ν ∂ν =
      ∫ τ, ∫ σ, χ τ * deriv (etaK n) (σ - τ) * F τ σ ∂ν ∂ν :=
    (integral_integral_swap (f := fun τ σ => χ τ * deriv (etaK n) (σ - τ) * F τ σ) iC).symm
  have IBτ : Integrable (fun τ => ∫ σ, χ τ * etaK n (σ - τ) * H τ σ ∂ν) ν := iB.integral_prod_left
  have IKτ : Integrable (fun τ => ∫ σ, χ τ * etaK n (σ - τ) * Kt τ σ ∂ν) ν := iK.integral_prod_left
  have C3 : ∫ τ, ∫ σ, χ τ * deriv (etaK n) (σ - τ) * F τ σ ∂ν ∂ν =
      -(∫ τ, ∫ σ, χ τ * etaK n (σ - τ) * Kt τ σ ∂ν ∂ν) - ∫ τ, χ τ * (etaK n τ * D2 τ) ∂ν := by
    have IKn : Integrable (fun τ => -(∫ σ, χ τ * etaK n (σ - τ) * Kt τ σ ∂ν)) ν := IKτ.neg
    rw [integral_congr_ae hτ, integral_sub IKn hD2', integral_neg]
  have A3 : ∫ τ, ∫ σ, χ τ * etaK n (σ - τ) * H τ σ ∂ν ∂ν =
      ∫ τ, χ τ * ∫ σ, etaK n (σ - τ) * H τ σ ∂ν ∂ν := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    simp only
    rw [← integral_const_mul]; simp only [mul_assoc]
  have K3 : ∫ τ, ∫ σ, χ τ * etaK n (σ - τ) * Kt τ σ ∂ν ∂ν =
      ∫ τ, χ τ * ∫ σ, etaK n (σ - τ) * Kt τ σ ∂ν ∂ν := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    simp only
    rw [← integral_const_mul]; simp only [mul_assoc]
  rw [E1, A2, C2, C3, A3, K3]
  ring

end PDE
