module

public import PDEFoundation.Euler.TimeDiagBil

/-!
# Diagonal limit for bilinear time-mollified forms

For `Φ(τ,σ) = ∫_Ω a(ω,τ) b(ω,σ) dμ(ω)` with `a`, `b` bounded and jointly a.e. strongly measurable on
`μ ⊗ (Leb|[0,T])`, `μ` finite, and `g` continuous,
`∫ g(τ) ∫ η_n(σ-τ) Φ(τ,σ) dσ dτ → ∫ g(τ) Φ(τ,τ) dτ`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace PDE

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : ℝ} {a b : Ω × ℝ → ℝ}

/-- Fubini step for fixed `n`: pull the `ω`-integral out of the time mollification. -/
theorem bilin_inner_eq [IsFiniteMeasure μ] {A B : ℝ}
    (ha : AEStronglyMeasurable a (μ.prod (volume.restrict (Icc (0 : ℝ) T))))
    (hb : AEStronglyMeasurable b (μ.prod (volume.restrict (Icc (0 : ℝ) T))))
    (haA : ∀ᵐ p ∂(μ.prod (volume.restrict (Icc (0 : ℝ) T))), |a p| ≤ A)
    (hbB : ∀ᵐ p ∂(μ.prod (volume.restrict (Icc (0 : ℝ) T))), |b p| ≤ B) (n : ℕ) :
    ∀ᵐ τ ∂(volume.restrict (Icc (0 : ℝ) T)),
      ∫ σ, etaK n (σ - τ) * (∫ ω, a (ω, τ) * b (ω, σ) ∂μ) ∂(volume.restrict (Icc (0 : ℝ) T)) =
      ∫ ω, a (ω, τ) * (∫ σ, etaK n (σ - τ) * b (ω, σ) ∂(volume.restrict (Icc (0 : ℝ) T))) ∂μ := by
  set ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) T) with hν
  have : IsFiniteMeasure ν := ⟨by rw [hν, Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
  have hswap : ∀ᵐ τ ∂ν, ∀ᵐ ω ∂μ, |a (ω, τ)| ≤ A := by
    have h1 := (Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae haA
    exact Measure.ae_ae_of_ae_prod h1
  filter_upwards [ha.prodMk_right, hswap] with τ hτ hτA
  have hbs : AEStronglyMeasurable (fun q : ℝ × Ω => b (q.2, q.1)) (ν.prod μ) := by
    have := hb.prod_swap
    exact this
  have hint : Integrable (fun q : ℝ × Ω => etaK n (q.1 - τ) * (a (q.2, τ) * b (q.2, q.1))) (ν.prod μ) := by
    obtain ⟨Cη, hCη⟩ := etaK_le_const n
    have h1 : AEStronglyMeasurable (fun q : ℝ × Ω => etaK n (q.1 - τ) * (a (q.2, τ) * b (q.2, q.1)))
        (ν.prod μ) := by
      refine AEStronglyMeasurable.mul ?_ (AEStronglyMeasurable.mul hτ.comp_snd hbs)
      exact (((etaK_contDiff n).continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable).comp_fst
    refine Integrable.of_bound (C := Cη * (A * B)) h1 ?_
    have hb' : ∀ᵐ q ∂(ν.prod μ), |b (q.2, q.1)| ≤ B :=
      (Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae hbB
    have ha' : ∀ᵐ q ∂(ν.prod μ), |a (q.2, τ)| ≤ A :=
      (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := μ)).ae hτA
    filter_upwards [hb', ha'] with q hq1 hq2
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have hη0 : 0 ≤ Cη := (abs_nonneg _).trans (hCη 0)
    have hA0 : 0 ≤ A := (abs_nonneg _).trans hq2
    exact mul_le_mul (hCη _) (mul_le_mul hq2 hq1 (abs_nonneg _) hA0) (by positivity) hη0
  have e1 : ∀ σ, etaK n (σ - τ) * (∫ ω, a (ω, τ) * b (ω, σ) ∂μ) =
      ∫ ω, etaK n (σ - τ) * (a (ω, τ) * b (ω, σ)) ∂μ := fun σ => by rw [integral_const_mul]
  simp_rw [e1]
  rw [integral_integral_swap (f := fun σ ω => etaK n (σ - τ) * (a (ω, τ) * b (ω, σ))) hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
  simp only
  ring

/-- **Diagonal limit.**  `∫ g(τ) ∫ η_n(σ-τ) Φ(τ,σ) dσ dτ → ∫ g(τ) Φ(τ,τ) dτ` for the bilinear form
`Φ(τ,σ) = ∫ a(ω,τ) b(ω,σ) dμ`. -/
theorem tendsto_time_mollify_bilinear [IsFiniteMeasure μ] {A B : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (ha : AEStronglyMeasurable a (μ.prod (volume.restrict (Icc (0 : ℝ) T))))
    (hb : AEStronglyMeasurable b (μ.prod (volume.restrict (Icc (0 : ℝ) T))))
    (haA : ∀ᵐ p ∂(μ.prod (volume.restrict (Icc (0 : ℝ) T))), |a p| ≤ A)
    (hbB : ∀ᵐ p ∂(μ.prod (volume.restrict (Icc (0 : ℝ) T))), |b p| ≤ B)
    {g : ℝ → ℝ} (hg : Continuous g) :
    Tendsto (fun n : ℕ => ∫ τ, g τ * ∫ σ, etaK n (σ - τ) * (∫ ω, a (ω, τ) * b (ω, σ) ∂μ)
        ∂(volume.restrict (Icc (0 : ℝ) T)) ∂(volume.restrict (Icc (0 : ℝ) T))) atTop
      (𝓝 (∫ τ, g τ * ∫ ω, a (ω, τ) * b (ω, τ) ∂μ ∂(volume.restrict (Icc (0 : ℝ) T)))) := by
  set ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) T) with hν
  have : IsFiniteMeasure ν := ⟨by rw [hν, Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
  obtain ⟨Cg0, hCg0⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).exists_bound_of_continuousOn
    hg.continuousOn
  set Cg : ℝ := max Cg0 0 with hCgdef
  have hCg : ∀ τ ∈ Icc (0 : ℝ) T, |g τ| ≤ Cg := fun τ hτ => by
    have := hCg0 τ hτ
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have hCg0' : 0 ≤ Cg := le_max_right _ _
  set Bn : ℕ → Ω × ℝ → ℝ := fun n p => ∫ σ, etaK n (σ - p.2) * b (p.1, σ) ∂ν with hBn
  set f : ℕ → Ω × ℝ → ℝ := fun n p => g p.2 * a p * Bn n p with hfdef
  set f0 : Ω × ℝ → ℝ := fun p => g p.2 * a p * b p with hf0def
  have hBn_meas : ∀ n, AEStronglyMeasurable (Bn n) (μ.prod ν) := fun n => bilin_B_aesm n hb
  have hgm : AEStronglyMeasurable (fun p : Ω × ℝ => g p.2) (μ.prod ν) :=
    hg.aestronglyMeasurable.comp_snd
  have hf_meas : ∀ n, AEStronglyMeasurable (f n) (μ.prod ν) := fun n => (hgm.mul ha).mul (hBn_meas n)
  have hf0_meas : AEStronglyMeasurable f0 (μ.prod ν) := (hgm.mul ha).mul hb
  have hgb : ∀ᵐ p ∂(μ.prod ν), |g p.2| ≤ Cg :=
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae
      (ae_restrict_of_forall_mem measurableSet_Icc hCg)
  have hBnb : ∀ n, ∀ᵐ p ∂(μ.prod ν), |Bn n p| ≤ B := fun n =>
    ((Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae
      (bilin_B_bound hB0 hb hbB n)).mono fun p hp => hp p.2
  have hf_bd : ∀ n, ∀ᵐ p ∂(μ.prod ν), ‖f n p‖ ≤ Cg * A * B := by
    intro n
    filter_upwards [hgb, haA, hBnb n] with p h1 h2 h3
    simp only [hfdef, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) hCg0') h3 (abs_nonneg _) (by positivity)
  have hf0_bd : ∀ᵐ p ∂(μ.prod ν), ‖f0 p‖ ≤ Cg * A * B := by
    filter_upwards [hgb, haA, hbB] with p h1 h2 h3
    simp only [hf0def, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) hCg0') h3 (abs_nonneg _) (by positivity)
  have hf_int : ∀ n, Integrable (f n) (μ.prod ν) := fun n => Integrable.of_bound (hf_meas n) _ (hf_bd n)
  have hf0_int : Integrable f0 (μ.prod ν) := Integrable.of_bound hf0_meas _ hf0_bd
  -- rewrite both sides as `ω`-integrals
  have hL : ∀ n, ∫ τ, g τ * ∫ σ, etaK n (σ - τ) * (∫ ω, a (ω, τ) * b (ω, σ) ∂μ) ∂ν ∂ν =
      ∫ ω, ∫ τ, f n (ω, τ) ∂ν ∂μ := by
    intro n
    rw [integral_integral_swap (f := fun ω τ => f n (ω, τ)) (hf_int n)]
    refine integral_congr_ae ?_
    filter_upwards [bilin_inner_eq ha hb haA hbB n] with τ hτ
    rw [hτ, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hfdef, hBn]
    ring
  have hR : ∫ τ, g τ * ∫ ω, a (ω, τ) * b (ω, τ) ∂μ ∂ν = ∫ ω, ∫ τ, f0 (ω, τ) ∂ν ∂μ := by
    rw [integral_integral_swap (f := fun ω τ => f0 (ω, τ)) hf0_int]
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    simp only
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hf0def]
    ring
  simp_rw [hL, hR]
  -- dominated convergence in `ω`
  have hslice_ae : ∀ᵐ ω ∂μ, (AEStronglyMeasurable (fun τ => a (ω, τ)) ν) ∧
      (∀ᵐ τ ∂ν, |a (ω, τ)| ≤ A) ∧ (∀ n, AEStronglyMeasurable (fun τ => Bn n (ω, τ)) ν) ∧
      (∀ n τ, |Bn n (ω, τ)| ≤ B) ∧
      (∀ᵐ τ ∂ν, Tendsto (fun n => Bn n (ω, τ)) atTop (𝓝 (b (ω, τ)))) := by
    have h1 := ha.prodMk_left
    have h2 := Measure.ae_ae_of_ae_prod haA
    have h3 : ∀ᵐ ω ∂μ, ∀ n, AEStronglyMeasurable (fun τ => Bn n (ω, τ)) ν :=
      ae_all_iff.2 fun n => (hBn_meas n).prodMk_left
    have h4 : ∀ᵐ ω ∂μ, ∀ n τ, |Bn n (ω, τ)| ≤ B :=
      ae_all_iff.2 fun n => bilin_B_bound hB0 hb hbB n
    have h5 := bilin_B_tendsto hb hbB
    filter_upwards [h1, h2, h3, h4, h5] with ω w1 w2 w3 w4 w5
    exact ⟨w1, w2, w3, w4, w5⟩
  refine tendsto_integral_of_dominated_convergence (fun _ => Cg * A * B * ν.real univ)
    (fun n => (hf_meas n).integral_prod_right') (integrable_const _) ?_ ?_
  · intro n
    filter_upwards [Measure.ae_ae_of_ae_prod (hf_bd n)] with ω hω
    exact norm_integral_le_of_norm_le_const hω
  · filter_upwards [hslice_ae] with ω ⟨w1, w2, w3, w4, w5⟩
    refine tendsto_integral_of_dominated_convergence (fun _ => Cg * A * B)
      (fun n => ((hg.aestronglyMeasurable.mul w1).mul (w3 n))) (integrable_const _) ?_ ?_
    · intro n
      filter_upwards [w2, ae_restrict_mem measurableSet_Icc] with τ hτ hτm
      simp only [hfdef, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (mul_le_mul (hCg τ hτm) hτ (abs_nonneg _) hCg0') (w4 n τ) (abs_nonneg _)
        (by positivity)
    · filter_upwards [w5] with τ hτ
      simp only [hf0def, hfdef]
      exact hτ.const_mul _

end PDE
