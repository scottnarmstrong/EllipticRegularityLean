module

public import EllipticRegularity.DeGiorgi.Holder.OscDecay

/-!
# The oscillation decay step

`oscillation_decay_step`: if a solution `u` on `B_1` has essential range in `[m, M]` on
a ball `B_ρ(z) ⊆ B_1`, then on `B_{ρ/2}(z)` its essential range lies in an interval of
length at most `(1 - δ) (M - m)`.  This is (4.53) of the manuscript, proved from
expansion of positivity applied to `2 (u - m) / (M - m)` or to `2 (M - u) / (M - m)`.
-/

@[expose] public section

namespace PDE.DGNMHolder

open PDE MeasureTheory

variable {d : ℕ}

/-- **Oscillation decay** for solutions in the unit ball. -/
theorem oscillation_decay_step {Ce : ℝ} (hCe : 0 < Ce) (hE : EoPStatement d Ce)
    (hAff : AffineStability d) (hScale : ScaleStability d)
    {Λ : ℝ} {a : CoeffField d}
    (hm : ∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1)))
    (he : ∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function (euclideanBall (0 : Vec d) 1)}
    (hsol : IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u (0 : Vec d → ℝ) 0)
    {z : Vec d} {ρ : ℝ} (hρ : 0 < ρ) (hsub : euclideanBall z ρ ⊆ euclideanBall (0 : Vec d) 1)
    {m M : ℝ} (hr : EssentialRangeBoundsOn u.toFun (euclideanBall z ρ) m M) :
    ∃ m' M' : ℝ, EssentialRangeBoundsOn u.toFun (euclideanBall z (ρ / 2)) m' M' ∧
      M' - m' ≤ (1 - decayConst d Ce Λ) * (M - m) := by
  have hΛ : 1 ≤ Λ := (he 0 (center_mem_euclideanBall (0 : Vec d) one_pos)).lam_le_Lam
  have hmM : m ≤ M := le_of_essentialRange hρ hr
  have hhalf : euclideanBall z (ρ / 2) ⊆ euclideanBall z ρ :=
    euclideanBall_mono (by linarith) (by linarith)
  by_cases hlt : m < M
  swap
  · refine ⟨m, M, hr.mono hhalf, ?_⟩
    have : M - m = 0 := by linarith
    rw [this]; simp
  set δ : ℝ := decayConst d Ce Λ with hδ
  have hδ0 : 0 < δ := decayConst_pos d Ce Λ
  have hL : 0 < M - m := sub_pos.2 hlt
  obtain ⟨a', u', hm', he', hsol', hu'⟩ := hScale Λ a hm he u hsol z ρ hρ hsub
  have hr' := range_scale_fwd hρ hu' hr
  obtain ⟨v1, hv1sol, hv1ae⟩ := hAff Λ a' hm' he' u' hsol' (2 / (M - m)) (-(2 * m) / (M - m))
  obtain ⟨v2, hv2sol, hv2ae⟩ := hAff Λ a' hm' he' u' hsol' (-(2 / (M - m))) (2 * M / (M - m))
  have hf1 : ∀ x, 2 / (M - m) * x + -(2 * m) / (M - m) = 2 * (x - m) / (M - m) := by
    intro x; field_simp; ring
  have hf2 : ∀ x, -(2 / (M - m)) * x + 2 * M / (M - m) = 2 * (M - x) / (M - m) := by
    intro x; field_simp; ring
  have hv1nn : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1), 0 ≤ v1.toFun x := by
    filter_upwards [hv1ae, hr'] with x h1 h2
    rw [h1, hf1]
    exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.2 h2.1)) hL.le
  have hv2nn : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1), 0 ≤ v2.toFun x := by
    filter_upwards [hv2ae, hr'] with x h1 h2
    rw [h1, hf2]
    exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.2 h2.2)) hL.le
  have hcover : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
      1 ≤ v1.toFun x ∨ 1 ≤ v2.toFun x := by
    filter_upwards [hv1ae, hv2ae] with x h1 h2
    by_contra hcon
    push Not at hcon
    have hsum : v1.toFun x + v2.toFun x = 2 := by
      rw [h1, h2, hf1, hf2]
      field_simp; ring
    linarith [hcon.1, hcon.2]
  -- one of the two functions satisfies the measure hypothesis of expansion of positivity
  have hB : MeasurableSet (euclideanBall (0 : Vec d) 1) := measurableSet_euclideanBall _ _
  have hcov : volume (euclideanBall (0 : Vec d) 1) ≤
      volume {x ∈ euclideanBall (0 : Vec d) 1 | 1 ≤ v1.toFun x} +
        volume {x ∈ euclideanBall (0 : Vec d) 1 | 1 ≤ v2.toFun x} := by
    calc volume (euclideanBall (0 : Vec d) 1)
        ≤ volume ({x ∈ euclideanBall (0 : Vec d) 1 | 1 ≤ v1.toFun x} ∪
            {x ∈ euclideanBall (0 : Vec d) 1 | 1 ≤ v2.toFun x}) := by
          apply measure_mono_ae
          filter_upwards [(ae_restrict_iff' hB).1 hcover] with x hx hxB
          rcases hx hxB with h | h
          · exact Or.inl ⟨hxB, h⟩
          · exact Or.inr ⟨hxB, h⟩
      _ ≤ _ := measure_union_le _ _
  have hhalf2 : ENNReal.ofReal (1 - 1 / 2 : ℝ) = 2⁻¹ := by
    rw [show (1 - 1 / 2 : ℝ) = 2⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num)]
    simp
  have hcase : ENNReal.ofReal (1 - 1 / 2 : ℝ) * volume (euclideanBall (0 : Vec d) 1) ≤
        volume {x ∈ euclideanBall (0 : Vec d) 1 | 1 ≤ v1.toFun x} ∨
      ENNReal.ofReal (1 - 1 / 2 : ℝ) * volume (euclideanBall (0 : Vec d) 1) ≤
        volume {x ∈ euclideanBall (0 : Vec d) 1 | 1 ≤ v2.toFun x} := by
    by_contra hcon
    push Not at hcon
    have := ENNReal.add_lt_add hcon.1 hcon.2
    rw [← add_mul, hhalf2, ENNReal.inv_two_add_inv_two, one_mul] at this
    exact absurd hcov (not_le.2 this)
  have hsubhalf : euclideanBall (0 : Vec d) (1 / 2) ⊆ euclideanBall (0 : Vec d) 1 :=
    euclideanBall_mono (by norm_num) (by norm_num)
  have hr'h := ae_restrict_of_ae_restrict_of_subset hsubhalf hr'
  have hv1h := ae_restrict_of_ae_restrict_of_subset hsubhalf hv1ae
  have hv2h := ae_restrict_of_ae_restrict_of_subset hsubhalf hv2ae
  have hv1nnh := ae_restrict_of_ae_restrict_of_subset hsubhalf hv1nn
  have hv2nnh := ae_restrict_of_ae_restrict_of_subset hsubhalf hv2nn
  set e0 : ℝ := Real.exp (-(Ce * (1 / 2 : ℝ) ^ ((1 : ℝ) / d) * Λ ^ (((d : ℝ) + 2) / 4))) with he0
  have hδle : δ ≤ e0 / 2 := decayConst_le_expansion d hCe hΛ
  rcases hcase with h1 | h2
  · have hess := hE (1 / 2) (by norm_num) le_rfl Λ a' hm' he' v1 hv1sol.toSupersolutionOn hv1nn h1
    have hae : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) (1 / 2)), e0 ≤ v1.toFun x := by
      filter_upwards [ae_essInf_le (μ := volumeOn (euclideanBall (0 : Vec d) (1 / 2)))
        (f := fun x => ENNReal.ofReal (v1.toFun x)), hv1nnh] with x hx hnn
      exact (ENNReal.ofReal_le_ofReal_iff hnn).1 (hess.trans hx)
    refine ⟨m + δ * (M - m), M, range_scale_back hρ hu' ?_, le_of_eq (by ring)⟩
    filter_upwards [hae, hr'h, hv1h] with y h0 hr1 h1y
    rw [h1y, hf1] at h0
    have h3 := (le_div_iff₀ hL).1 h0
    have h4 := mul_le_mul_of_nonneg_right hδle hL.le
    refine ⟨by nlinarith, hr1.2⟩
  · have hess := hE (1 / 2) (by norm_num) le_rfl Λ a' hm' he' v2 hv2sol.toSupersolutionOn hv2nn h2
    have hae : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) (1 / 2)), e0 ≤ v2.toFun x := by
      filter_upwards [ae_essInf_le (μ := volumeOn (euclideanBall (0 : Vec d) (1 / 2)))
        (f := fun x => ENNReal.ofReal (v2.toFun x)), hv2nnh] with x hx hnn
      exact (ENNReal.ofReal_le_ofReal_iff hnn).1 (hess.trans hx)
    refine ⟨m, M - δ * (M - m), range_scale_back hρ hu' ?_, le_of_eq (by ring)⟩
    filter_upwards [hae, hr'h, hv2h] with y h0 hr1 h1y
    rw [h1y, hf2] at h0
    have h3 := (le_div_iff₀ hL).1 h0
    have h4 := mul_le_mul_of_nonneg_right hδle hL.le
    refine ⟨hr1.1, by nlinarith⟩

end PDE.DGNMHolder
