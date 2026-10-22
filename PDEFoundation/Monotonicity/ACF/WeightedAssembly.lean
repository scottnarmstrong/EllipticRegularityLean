module

public import PDEFoundation.Monotonicity.ACF.WeightedSlices
public import PDEFoundation.Monotonicity.ACF.WeightedLebesgue

/-!
# From the kernel average to the pointwise bound (Lebesgue points)

`J(r) ≤ ofReal (profile r)` for a.e. `r ∈ (0, R)`, where
`profile(ρ) = (flux(ρ) + ((d-2)/2) a(ρ)) / ρ^{d-1}`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace PDE

noncomputable section

variable {d : ℕ} {R : ℝ}

theorem integrableOn_profile [NeZero d] (u : H1Function (euclideanBall (0 : Vec d) R)) {δ : ℝ}
    (hδ : 0 < δ) : IntegrableOn (acfProfile d u.toFun u.grad) (Ioo δ R) := by
  have hF := integrableOn_slice_of_integrableOn (integrableOn_flux u)
  have hA := integrableOn_slice_of_integrableOn (integrableOn_sq_u u)
  have hsum : IntegrableOn (fun ρ => acfSliceFlux u.toFun u.grad ρ +
      (((d : ℝ) - 2) / 2) * acfSliceMass u.toFun ρ) (Ioo δ R) :=
    ((hF.mono_set (Ioo_subset_Ioo_left hδ.le)).add
      ((hA.mono_set (Ioo_subset_Ioo_left hδ.le)).const_mul _))
  have hbd : ∀ᵐ ρ ∂(volume.restrict (Ioo δ R)), ‖(ρ ^ (d - 1))⁻¹‖ ≤ (δ ^ (d - 1))⁻¹ := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    refine Filter.Eventually.of_forall fun ρ hρ => ?_
    have h0 : 0 < ρ := hδ.trans hρ.1
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (pow_pos h0 _))]
    exact inv_anti₀ (pow_pos hδ _) (pow_le_pow_left₀ hδ.le hρ.1.le _)
  have := hsum.mul_bdd (c := (δ ^ (d - 1))⁻¹)
    ((measurable_id.pow_const (d - 1)).inv.aestronglyMeasurable) hbd
  refine this.congr (Filter.Eventually.of_forall fun ρ => ?_)
  simp only [acfProfile, div_eq_mul_inv, id, Pi.inv_apply]

/-- **A.e. bound by the profile.** -/
theorem ae_energy_le_profile {d : ℕ} (hd : 3 ≤ d) {R : ℝ} (u : H1Function (euclideanBall (0 : Vec d) R))
    (hcont : ContinuousOn u.toFun (euclideanBall (0 : Vec d) R))
    (hnonneg : ∀ x ∈ euclideanBall (0 : Vec d) R, 0 ≤ u.toFun x)
    (hsub : IsWeakDivergenceFormSubharmonicOn (fun _ => (1 : Mat d))
      (euclideanBall (0 : Vec d) R) u) :
    ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R)),
      acfWeightedEnergy u.grad r ≤ ENNReal.ofReal (acfProfile d u.toFun u.grad r) := by
  have : NeZero d := ⟨by omega⟩
  set P : ℝ → ℝ := acfProfile d u.toFun u.grad with hP
  set f : ℕ → ℝ → ℝ := fun n => (Ioo (1 / ((n : ℝ) + 1)) R).indicator P with hf
  have hfint : ∀ n, Integrable (f n) := fun n =>
    (integrable_indicator_iff measurableSet_Ioo).mpr (integrableOn_profile u (by positivity))
  have hall : ∀ᵐ r : ℝ, ∀ n : ℕ,
      Tendsto (fun k => ∫ ρ, acfKer r k ρ * f n ρ) (𝓝[>] 0) (𝓝 (f n r)) :=
    ae_all_iff.mpr fun n => ae_tendsto_kernel_average (hfint n)
  filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem measurableSet_Ioo] with r hr hrm
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hrm.1
  have hlim := hr n
  have hrn : f n r = P r := by
    simp only [hf, indicator_of_mem (show r ∈ Ioo (1 / ((n : ℝ) + 1)) R from ⟨hn, hrm.2⟩)]
  rw [hrn] at hlim
  have hev : ∀ᶠ k in 𝓝[>] (0 : ℝ), acfWeightedEnergy u.grad r ≤
      ENNReal.ofReal (∫ ρ, acfKer r k ρ * f n ρ) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < R - r by linarith [hrm.2])] with k hk
    have hk0 : 0 < k := hk.1
    have hrk : r + k < R := by linarith [hk.2]
    refine (acf_energy_le_kernel hd hrm.1 hk0 hrk u hcont hnonneg hsub).trans (le_of_eq ?_)
    congr 1
    have hker0 : ∀ ρ, ρ ∉ Icc r (r + k) → acfKer r k ρ = 0 := fun ρ hρ =>
      Function.notMem_support.mp (fun hh => hρ (acfKer_support_subset hk0 hh))
    have hzero : ∀ ρ, ρ ∉ Ioi (0 : ℝ) → acfKer r k ρ * f n ρ = 0 := by
      intro ρ hρ
      rw [hker0 ρ (fun h => hρ (lt_of_lt_of_le hrm.1 h.1)), zero_mul]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    refine setIntegral_congr_fun measurableSet_Ioi fun ρ _ => ?_
    by_cases hρ : ρ ∈ Icc r (r + k)
    · have : ρ ∈ Ioo (1 / ((n : ℝ) + 1)) R := ⟨lt_of_lt_of_le hn hρ.1, by linarith [hρ.2]⟩
      simp only [hf, indicator_of_mem this]
      rfl
    · rw [hker0 ρ hρ, zero_mul, zero_mul]
  exact ge_of_tendsto (ENNReal.tendsto_ofReal hlim) hev

end

end PDE
