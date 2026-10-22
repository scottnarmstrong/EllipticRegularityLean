module

public import PDEFoundation.Euler.TimeBilinear
public import PDEFoundation.Euler.TimeProduct
public import PDEFoundation.Euler.WeakCont

/-!
# Finite sums of bilinear time forms

Linearity of the doubly time-integrated expression in the form, and integrability of the diagonal
of a bilinear form.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace PDE

theorem time_mollify_sum_eq (n : ℕ) {T : ℝ} {ι : Type*} (s : Finset ι) {Φ : ι → ℝ → ℝ → ℝ}
    (hΦ : ∀ k ∈ s, Integrable (fun p : ℝ × ℝ => Φ k p.1 p.2)
      ((volume.restrict (Icc (0 : ℝ) T)).prod (volume.restrict (Icc (0 : ℝ) T))))
    {g : ℝ → ℝ} (hg : Continuous g) :
    ∫ τ, g τ * ∫ σ, etaK n (σ - τ) * (∑ k ∈ s, Φ k τ σ) ∂(volume.restrict (Icc (0 : ℝ) T))
        ∂(volume.restrict (Icc (0 : ℝ) T)) =
      ∑ k ∈ s, ∫ τ, g τ * ∫ σ, etaK n (σ - τ) * Φ k τ σ ∂(volume.restrict (Icc (0 : ℝ) T))
        ∂(volume.restrict (Icc (0 : ℝ) T)) := by
  set ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) T) with hν
  have hηc : Continuous (etaK n) := (etaK_contDiff n).continuous
  have hs : Continuous (fun p : ℝ × ℝ => p.2 - p.1) := continuous_snd.sub continuous_fst
  have hprod : ∀ k ∈ s, Integrable (fun p : ℝ × ℝ => etaK n (p.2 - p.1) * Φ k p.1 p.2) (ν.prod ν) :=
    fun k hk => integrable_continuous_mul (g := fun τ σ => etaK n (σ - τ)) (hΦ k hk) (hηc.comp hs)
  have hprod2 : ∀ k ∈ s, Integrable (fun p : ℝ × ℝ => g p.1 * (etaK n (p.2 - p.1) * Φ k p.1 p.2)) (ν.prod ν) :=
    fun k hk => integrable_continuous_mul (T := T) (f := fun τ σ => etaK n (σ - τ) * Φ k τ σ) (g := fun τ _ => g τ)
      (hprod k hk) (hg.comp continuous_fst)
  have hout : ∀ k ∈ s, Integrable (fun τ => g τ * ∫ σ, etaK n (σ - τ) * Φ k τ σ ∂ν) ν := by
    intro k hk
    have := (hprod2 k hk).integral_prod_left
    refine this.congr (Filter.Eventually.of_forall fun τ => ?_)
    simp only
    rw [integral_const_mul]
  have hae : ∀ᵐ τ ∂ν, ∀ k ∈ s, Integrable (fun σ => etaK n (σ - τ) * Φ k τ σ) ν := by
    rw [Filter.eventually_all_finset]
    intro k hk
    exact (hprod k hk).prod_right_ae
  have hin : ∀ᵐ τ ∂ν, ∫ σ, etaK n (σ - τ) * (∑ k ∈ s, Φ k τ σ) ∂ν =
      ∑ k ∈ s, ∫ σ, etaK n (σ - τ) * Φ k τ σ ∂ν := by
    filter_upwards [hae] with τ hτ
    simp_rw [Finset.mul_sum]
    exact integral_finsetSum _ hτ
  rw [integral_congr_ae (hin.mono fun τ hτ => by rw [hτ])]
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum _ hout

theorem bilin_diag_integrable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {T : ℝ}
    {a b : Ω × ℝ → ℝ} {A B : ℝ}
    (ha : AEStronglyMeasurable a (μ.prod (volume.restrict (Icc (0 : ℝ) T))))
    (hb : AEStronglyMeasurable b (μ.prod (volume.restrict (Icc (0 : ℝ) T))))
    (haA : ∀ᵐ p ∂(μ.prod (volume.restrict (Icc (0 : ℝ) T))), |a p| ≤ A)
    (hbB : ∀ᵐ p ∂(μ.prod (volume.restrict (Icc (0 : ℝ) T))), |b p| ≤ B) :
    Integrable (fun τ => ∫ ω, a (ω, τ) * b (ω, τ) ∂μ) (volume.restrict (Icc (0 : ℝ) T)) := by
  set ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) T) with hν
  have : IsFiniteMeasure ν := ⟨by rw [hν, Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
  have hm : AEStronglyMeasurable (fun p : Ω × ℝ => a p * b p) (μ.prod ν) := ha.mul hb
  have hm' : AEStronglyMeasurable (fun p : ℝ × Ω => a (p.2, p.1) * b (p.2, p.1)) (ν.prod μ) := hm.prod_swap
  refine Integrable.of_bound (C := A * B * μ.real univ) hm'.integral_prod_right' ?_
  have h1 : ∀ᵐ τ ∂ν, ∀ᵐ ω ∂μ, |a (ω, τ)| ≤ A := by
    have := (Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae haA
    exact Measure.ae_ae_of_ae_prod this
  have h2 : ∀ᵐ τ ∂ν, ∀ᵐ ω ∂μ, |b (ω, τ)| ≤ B := by
    have := (Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae hbB
    exact Measure.ae_ae_of_ae_prod this
  filter_upwards [h1, h2] with τ hτ1 hτ2
  have hbd : ∀ᵐ ω ∂μ, ‖a (ω, τ) * b (ω, τ)‖ ≤ A * B := by
    filter_upwards [hτ1, hτ2] with ω w1 w2
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul w1 w2 (abs_nonneg _) ((abs_nonneg _).trans w1)
  exact norm_integral_le_of_norm_le_const hbd

/-- Diagonal limit for a finite sum of bilinear forms. -/
theorem tendsto_time_mollify_sum {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {T : ℝ}
    {ι : Type*} (s : Finset ι) {a b : ι → Ω × ℝ → ℝ} {A B : ι → ℝ}
    (hA0 : ∀ k ∈ s, 0 ≤ A k)
    (ha : ∀ k ∈ s, AEStronglyMeasurable (a k) (μ.prod (volume.restrict (Icc (0 : ℝ) T))))
    (hb : ∀ k ∈ s, AEStronglyMeasurable (b k) (μ.prod (volume.restrict (Icc (0 : ℝ) T))))
    (haA : ∀ k ∈ s, ∀ᵐ p ∂(μ.prod (volume.restrict (Icc (0 : ℝ) T))), |a k p| ≤ A k)
    (hbB : ∀ k ∈ s, ∀ᵐ p ∂(μ.prod (volume.restrict (Icc (0 : ℝ) T))), |b k p| ≤ B k)
    (hB0 : ∀ k ∈ s, 0 ≤ B k) {g : ℝ → ℝ} (hg : Continuous g) :
    Tendsto (fun n : ℕ => ∫ τ, g τ * ∫ σ, etaK n (σ - τ) *
        (∑ k ∈ s, ∫ ω, a k (ω, τ) * b k (ω, σ) ∂μ)
        ∂(volume.restrict (Icc (0 : ℝ) T)) ∂(volume.restrict (Icc (0 : ℝ) T))) atTop
      (𝓝 (∫ τ, g τ * ∑ k ∈ s, ∫ ω, a k (ω, τ) * b k (ω, τ) ∂μ ∂(volume.restrict (Icc (0 : ℝ) T)))) := by
  set ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) T) with hν
  have hΦ : ∀ k ∈ s, Integrable (fun p : ℝ × ℝ => (fun τ σ => ∫ ω, a k (ω, τ) * b k (ω, σ) ∂μ) p.1 p.2)
      (ν.prod ν) := fun k hk => bilin_integrable (hA0 k hk) (ha k hk) (hb k hk) (haA k hk) (hbB k hk)
  have hlim := tendsto_finsetSum s (fun k hk => tendsto_time_mollify_bilinear (hA0 k hk) (hB0 k hk)
    (ha k hk) (hb k hk) (haA k hk) (hbB k hk) hg)
  have hL : ∀ n : ℕ, ∫ τ, g τ * ∫ σ, etaK n (σ - τ) * (∑ k ∈ s, ∫ ω, a k (ω, τ) * b k (ω, σ) ∂μ) ∂ν ∂ν =
      ∑ k ∈ s, ∫ τ, g τ * ∫ σ, etaK n (σ - τ) * (∫ ω, a k (ω, τ) * b k (ω, σ) ∂μ) ∂ν ∂ν :=
    fun n => time_mollify_sum_eq n s hΦ hg
  have hdiag : ∀ k ∈ s, Integrable (fun τ => g τ * ∫ ω, a k (ω, τ) * b k (ω, τ) ∂μ) ν := fun k hk =>
    integrable_cont_mul_time hg (bilin_diag_integrable (ha k hk) (hb k hk) (haA k hk) (hbB k hk))
  have hR : ∫ τ, g τ * ∑ k ∈ s, ∫ ω, a k (ω, τ) * b k (ω, τ) ∂μ ∂ν =
      ∑ k ∈ s, ∫ τ, g τ * ∫ ω, a k (ω, τ) * b k (ω, τ) ∂μ ∂ν := by
    simp_rw [Finset.mul_sum]
    exact integral_finsetSum _ hdiag
  simp_rw [hL, hR]
  exact hlim

end PDE
