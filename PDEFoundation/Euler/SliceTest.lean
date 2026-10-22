module

public import PDEFoundation.Euler.Defs
public import PDEFoundation.Euler.SmoothPartial
public import PDEFoundation.Euler.TorusTranslate
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Time-separated test functions and the one-test-function slice identity

For `A, B₀, B₁ ∈ L¹(eulerMeasure T)` with
`∫ (A ψ + B₀ ∂₁ψ + B₁ ∂₂ψ) = 0` for all admissible space-time `ψ`, and a fixed smooth periodic `φ`,
the slice functional `G_φ(t) = ∫_cube (A φ + B₀ ∂₁φ + B₁ ∂₂φ)(x,t) dx` vanishes for a.e. `t ∈ [0,T]`
(test with `ψ(x,t) = χ(t) φ(x)`, `χ ∈ C_c^∞(0,T)`).
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

/-- The slice functional `G_φ(t)`. -/
noncomputable def sliceFunctional (A B₀ B₁ : Vec 2 × ℝ → ℝ) (φ : Vec 2 → ℝ) (t : ℝ) : ℝ :=
  ∫ x in torusCube, (A (x, t) * φ x + B₀ (x, t) * pd 0 φ x + B₁ (x, t) * pd 1 φ x)

/-- The product test function `χ(t) φ(x)`. -/
noncomputable def timeSplit (χ : ℝ → ℝ) (φ : Vec 2 → ℝ) : Vec 2 × ℝ → ℝ := fun z => χ z.2 * φ z.1

theorem isPeriodicSmooth_timeSplit {χ : ℝ → ℝ} {φ : Vec 2 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hp : IsTorusPeriodic φ) : IsPeriodicSmooth (timeSplit χ φ) := by
  refine ⟨ContDiff.mul (ContDiff.comp hχ contDiff_snd) (ContDiff.comp hφ contDiff_fst), ?_⟩
  intro t i x
  simp only [timeSplit]
  rw [hp i x]

theorem fderiv_timeSplit {χ : ℝ → ℝ} {φ : Vec 2 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (z : Vec 2 × ℝ) (j : Fin 2) :
    fderiv ℝ (timeSplit χ φ) z (basisVec j, 0) = χ z.2 * pd j φ z.1 := by
  have h1 : HasFDerivAt (fun z : Vec 2 × ℝ => χ z.2)
      ((fderiv ℝ χ z.2).comp (ContinuousLinearMap.snd ℝ (Vec 2) ℝ)) z :=
    ((hχ.differentiable (by simp)) z.2).hasFDerivAt.comp z (ContinuousLinearMap.snd ℝ (Vec 2) ℝ).hasFDerivAt
  have h2 : HasFDerivAt (fun z : Vec 2 × ℝ => φ z.1)
      ((fderiv ℝ φ z.1).comp (ContinuousLinearMap.fst ℝ (Vec 2) ℝ)) z :=
    ((hφ.differentiable (by simp)) z.1).hasFDerivAt.comp z (ContinuousLinearMap.fst ℝ (Vec 2) ℝ).hasFDerivAt
  have h3 : HasFDerivAt (fun z : Vec 2 × ℝ => χ z.2 * φ z.1)
      (χ z.2 • (fderiv ℝ φ z.1).comp (ContinuousLinearMap.fst ℝ (Vec 2) ℝ) +
        φ z.1 • (fderiv ℝ χ z.2).comp (ContinuousLinearMap.snd ℝ (Vec 2) ℝ)) z := h1.mul h2
  rw [show timeSplit χ φ = fun z => χ z.2 * φ z.1 from rfl, h3.fderiv]
  simp [pd]

/-- A smooth compactly supported function with `tsupport ⊆ (0,T)` vanishes outside some `[a,b] ⊆ (0,T)`. -/
theorem exists_Icc_of_tsupport_subset {T : ℝ} (hT : 0 < T) {χ : ℝ → ℝ} (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo 0 T) : ∃ a b : ℝ, 0 < a ∧ b < T ∧ ∀ t, t ∉ Icc a b → χ t = 0 := by
  by_cases hne : (tsupport χ).Nonempty
  · have hK : IsCompact (tsupport χ) := hc
    refine ⟨sInf (tsupport χ), sSup (tsupport χ), (hs (hK.sInf_mem hne)).1, (hs (hK.sSup_mem hne)).2, ?_⟩
    intro t ht
    by_contra hχ
    have hmem : t ∈ tsupport χ := subset_tsupport _ hχ
    exact ht ⟨csInf_le hK.bddBelow hmem, le_csSup hK.bddAbove hmem⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    refine ⟨T / 3, T / 2, by positivity, by linarith, fun t _ => ?_⟩
    by_contra hχ
    have : t ∈ tsupport χ := subset_tsupport _ hχ
    rw [hne] at this
    exact this

theorem integrable_mul_cont_fst {T : ℝ} {A : Vec 2 × ℝ → ℝ} (hA : Integrable A (eulerMeasure T))
    {g : Vec 2 → ℝ} (hg : Continuous g) :
    Integrable (fun z => A z * g z.1) (eulerMeasure T) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact torusCube).exists_bound_of_continuousOn hg.continuousOn
  refine hA.mul_bdd (c := C) (hg.comp continuous_fst).aestronglyMeasurable ?_
  have : ∀ᵐ z ∂(eulerMeasure T), z ∈ torusCube ×ˢ Icc (0 : ℝ) T := by
    unfold eulerMeasure
    exact ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)
  filter_upwards [this] with z hz
  exact hC z.1 hz.1

theorem ae_sliceFunctional_eq_zero {T : ℝ} (hT : 0 < T) {A B₀ B₁ : Vec 2 × ℝ → ℝ}
    (hA : Integrable A (eulerMeasure T)) (hB₀ : Integrable B₀ (eulerMeasure T))
    (hB₁ : Integrable B₁ (eulerMeasure T))
    (hweak : ∀ ψ : Vec 2 × ℝ → ℝ, IsPeriodicSmooth ψ → VanishesOutsideInterior T ψ →
      ∫ z, (A z * ψ z + B₀ z * fderiv ℝ ψ z (basisVec 0, 0) + B₁ z * fderiv ℝ ψ z (basisVec 1, 0))
        ∂(eulerMeasure T) = 0)
    {φ : Vec 2 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hp : IsTorusPeriodic φ) :
    ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), sliceFunctional A B₀ B₁ φ t = 0 := by
  set μc : Measure (Vec 2) := volume.restrict torusCube with hμc
  set νT : Measure ℝ := volume.restrict (Icc 0 T) with hνT
  have hprod : eulerMeasure T = μc.prod νT := eulerMeasure_eq_prod T
  have hc0 : Continuous φ := hφ.continuous
  have hc1 : ∀ j, Continuous (pd j φ) := fun j => (contDiff_pd_top hφ j).continuous
  set Fφ : Vec 2 × ℝ → ℝ := fun z => A z * φ z.1 + B₀ z * pd 0 φ z.1 + B₁ z * pd 1 φ z.1 with hF
  have hFint : Integrable Fφ (eulerMeasure T) :=
    ((integrable_mul_cont_fst hA hc0).add (integrable_mul_cont_fst hB₀ (hc1 0))).add
      (integrable_mul_cont_fst hB₁ (hc1 1))
  have hFint' : Integrable Fφ (μc.prod νT) := by rw [← hprod]; exact hFint
  -- the slice functional is integrable in t
  have hGint : Integrable (sliceFunctional A B₀ B₁ φ) νT := by
    have := hFint'.integral_prod_right
    exact this
  have hkey : ∀ χ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → tsupport χ ⊆ Ioo 0 T →
      ∫ t, χ t • sliceFunctional A B₀ B₁ φ t ∂νT = 0 := by
    intro χ hχ hcs hsub
    obtain ⟨a, b, ha, hb, hout⟩ := exists_Icc_of_tsupport_subset hT hcs hsub
    have hψ := isPeriodicSmooth_timeSplit hχ hφ hp
    have hv : VanishesOutsideInterior T (timeSplit χ φ) :=
      ⟨a, b, ha, hb, fun x t ht => by simp [timeSplit, hout t ht]⟩
    have h0 := hweak _ hψ hv
    have hpt : ∀ z : Vec 2 × ℝ, A z * timeSplit χ φ z + B₀ z * fderiv ℝ (timeSplit χ φ) z (basisVec 0, 0) +
        B₁ z * fderiv ℝ (timeSplit χ φ) z (basisVec 1, 0) = χ z.2 * Fφ z := by
      intro z
      rw [fderiv_timeSplit hχ hφ, fderiv_timeSplit hχ hφ]
      simp only [timeSplit, hF]; ring
    simp only [hpt] at h0
    have hχb : ∃ C, ∀ t, ‖χ t‖ ≤ C := by
      obtain ⟨C, hC⟩ := hχ.continuous.bounded_above_of_compact_support hcs
      exact ⟨C, hC⟩
    obtain ⟨C, hC⟩ := hχb
    have hint2 : Integrable (fun z : Vec 2 × ℝ => χ z.2 * Fφ z) (μc.prod νT) :=
      hFint'.bdd_mul (hχ.continuous.comp continuous_snd).aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => hC z.2)
    rw [hprod] at h0
    rw [integral_prod_symm _ hint2] at h0
    simpa [sliceFunctional, integral_const_mul, hF, smul_eq_mul] using h0
  have hae := (isOpen_Ioo (a := (0 : ℝ)) (b := T)).ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (μ := νT) (f := sliceFunctional A B₀ B₁ φ) (hGint.locallyIntegrable.locallyIntegrableOn _)
    (fun g hg hcs hsub => hkey g hg hcs hsub)
  have hin : ∀ᵐ t ∂νT, t ∈ Ioo (0 : ℝ) T := by
    have h1 : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Icc (0 : ℝ) T → t ∈ Ioo 0 T := by
      filter_upwards [Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := T) (μ := volume)] with t ht hmem
      exact Eq.mpr ht hmem
    filter_upwards [ae_restrict_of_ae h1, ae_restrict_mem measurableSet_Icc] with t h2 h3
    exact h2 h3
  filter_upwards [hae, hin] with t h1 h2
  exact h1 h2

end PDE
