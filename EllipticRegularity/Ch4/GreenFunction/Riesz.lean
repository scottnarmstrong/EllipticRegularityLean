module

public import PDEFoundation

/-!
# Weak limits in `L²` through the Riesz representation theorem

If `∫ Gₙ f dμ` converges for every `f ∈ L²(μ)` and the limit is bounded by `K ‖f‖₂`, then the
limit functional is represented by some `G ∈ L²(μ)`.  This is the functional-analytic step
used both to construct the Green function (Step 2 of Proposition 4.40) and to identify its weak
gradient (Step 6).
-/

@[expose] public section

open scoped Topology ENNReal InnerProductSpace

namespace PDE.Ch4Green

open MeasureTheory Filter

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Riesz representation of a limit functional on `L²(μ)`.** -/
theorem exists_rep_of_tendsto_integral {Gn : ℕ → α → ℝ} (hGn : ∀ n, MemLp (Gn n) 2 μ)
    (hlim : ∀ f : α → ℝ, MemLp f 2 μ →
      ∃ L : ℝ, Tendsto (fun n => ∫ x, Gn n x * f x ∂μ) atTop (𝓝 L))
    {K : ℝ} (hK : ∀ f : α → ℝ, MemLp f 2 μ → ∀ L : ℝ,
      Tendsto (fun n => ∫ x, Gn n x * f x ∂μ) atTop (𝓝 L) → |L| ≤ K * (eLpNorm f 2 μ).toReal) :
    ∃ G : α → ℝ, StronglyMeasurable G ∧ MemLp G 2 μ ∧
      ∀ f : α → ℝ, MemLp f 2 μ →
        Tendsto (fun n => ∫ x, Gn n x * f x ∂μ) atTop (𝓝 (∫ x, G x * f x ∂μ)) := by
  have hT : ∀ F : Lp ℝ 2 μ, Tendsto (fun n => ∫ x, Gn n x * F x ∂μ) atTop
      (𝓝 (limUnder atTop (fun n => ∫ x, Gn n x * F x ∂μ))) := by
    intro F
    obtain ⟨L, hL⟩ := hlim F (Lp.memLp F)
    rwa [hL.limUnder_eq]
  have hint : ∀ n (F : Lp ℝ 2 μ), Integrable (fun x => Gn n x * F x) μ := fun n F =>
    MemLp.integrable_mul (p := 2) (q := 2) (hGn n) (Lp.memLp F)
  let ℓ : Lp ℝ 2 μ →ₗ[ℝ] ℝ :=
    { toFun := fun F => limUnder atTop (fun n => ∫ x, Gn n x * F x ∂μ)
      map_add' := by
        intro F F'
        have hsum : ∀ n, ∫ x, Gn n x * (F + F') x ∂μ =
            ∫ x, Gn n x * F x ∂μ + ∫ x, Gn n x * F' x ∂μ := by
          intro n
          rw [← integral_add (hint n F) (hint n F')]
          refine integral_congr_ae ?_
          filter_upwards [Lp.coeFn_add F F'] with x hx
          rw [hx, Pi.add_apply, mul_add]
        refine tendsto_nhds_unique (hT (F + F')) ?_
        simp_rw [hsum]
        exact (hT F).add (hT F')
      map_smul' := by
        intro c F
        have hsmul : ∀ n, ∫ x, Gn n x * (c • F) x ∂μ = c * ∫ x, Gn n x * F x ∂μ := by
          intro n
          rw [← integral_const_mul]
          refine integral_congr_ae ?_
          filter_upwards [Lp.coeFn_smul c F] with x hx
          rw [hx, Pi.smul_apply, smul_eq_mul]
          ring
        refine tendsto_nhds_unique (hT (c • F)) ?_
        simp_rw [hsmul]
        exact (hT F).const_mul c }
  have hℓ : ∀ F : Lp ℝ 2 μ, ℓ F = limUnder atTop (fun n => ∫ x, Gn n x * F x ∂μ) := fun _ => rfl
  let ℓc : StrongDual ℝ (Lp ℝ 2 μ) := ℓ.mkContinuous K (fun F => by
    rw [Real.norm_eq_abs, Lp.norm_def, hℓ]
    exact hK _ (Lp.memLp F) _ (hT F))
  set G' : Lp ℝ 2 μ := (InnerProductSpace.toDual ℝ (Lp ℝ 2 μ)).symm ℓc with hG'
  have hinner : ∀ F : Lp ℝ 2 μ, ∫ x, G' x * F x ∂μ = ℓ F := by
    intro F
    have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := Lp ℝ 2 μ) (x := F) (y := ℓc)
    rw [← hG', L2.inner_def] at h
    simp only [RCLike.inner_apply', conj_trivial] at h
    rw [h]
    rfl
  refine ⟨G', Lp.stronglyMeasurable G', Lp.memLp G', fun f hf => ?_⟩
  set F := hf.toLp f
  have h1 : ∀ n, ∫ x, Gn n x * f x ∂μ = ∫ x, Gn n x * F x ∂μ := by
    intro n
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]
  have h2 : ∫ x, G' x * f x ∂μ = ∫ x, G' x * F x ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]
  simp_rw [h1]
  rw [h2, hinner F, hℓ]
  exact hT F

/-- An `L²` function orthogonal to all of `L²` vanishes a.e. -/
theorem ae_eq_zero_of_integral_mul_eq_zero {h : α → ℝ} (hh : MemLp h 2 μ)
    (horth : ∀ f : α → ℝ, MemLp f 2 μ → ∫ x, h x * f x ∂μ = 0) : h =ᵐ[μ] 0 := by
  have h0 := horth h hh
  have hsq : ∫ x, h x ^ 2 ∂μ = 0 := by
    rw [← h0]
    congr 1
    funext x
    ring
  have := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (h x)) hh.integrable_sq).1 hsq
  filter_upwards [this] with x hx
  simpa using hx

end PDE.Ch4Green
