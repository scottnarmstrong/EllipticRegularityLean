module

public import PDEFoundation.Monotonicity.FriedlandHayman.Local.Zonal

/-!
# Friedland--Hayman: cap integrals and the cap moments

The zonal integral of a function supported on the cap `cos ε < ⟪x, e₀⟫`, the cap moments
`m_ε` and `m'_ε`, the positivity of `m_ε`, and the asymptotics `m'_ε / m_ε → 0`.
-/

@[expose] public section

open MeasureTheory

namespace PDE.FHLane

noncomputable section

/-- The cap second moment `m_ε`. -/
noncomputable def capMom (D : ℕ) (ε : ℝ) : ℝ :=
  sphereArea (D - 1) / ((D : ℝ) - 1) * ∫ φ in (0 : ℝ)..ε, Real.sin φ ^ D

/-- The cap moment `m'_ε = ∫_cap (1 - ⟪x, e₀⟫)² dσ`. -/
noncomputable def capMom' (D : ℕ) (ε : ℝ) : ℝ :=
  sphereArea (D - 1) * ∫ φ in (0 : ℝ)..ε, (1 - Real.cos φ) ^ 2 * Real.sin φ ^ (D - 2)

namespace Local

theorem inner_le_one {D : ℕ} (x : Sph D) [NeZero D] : inner ℝ (x : HilbertVec D) (pole D) ≤ 1 := by
  have h := real_inner_le_norm (x : HilbertVec D) (pole D)
  have h1 : ‖(x : HilbertVec D)‖ = 1 := by simp
  have h2 : ‖pole D‖ = 1 := by
    rw [PiLp.norm_eq_of_L2]
    rw [Real.sqrt_eq_one, Finset.sum_eq_single (0 : Fin D)]
    · simp [pole_apply]
    · intro b _ hb
      simp [pole_apply, hb]
    · simp
  rw [h1, h2] at h
  linarith

end Local

theorem norm_pole (D : ℕ) [NeZero D] : ‖pole D‖ = 1 := by
  rw [PiLp.norm_eq_of_L2, Real.sqrt_eq_one, Finset.sum_eq_single (0 : Fin D)]
  · simp [Local.pole_apply]
  · intro b _ hb
    simp [Local.pole_apply, hb]
  · simp

namespace Local

theorem integral_cap_zonal {D : ℕ} (hD : 2 ≤ D) [NeZero D] {F : ℝ → ℝ} (hF : Continuous F)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < Real.pi) :
    ∫ x : Sph D, (if Real.cos ε < inner ℝ (x : HilbertVec D) (pole D) then
        F (inner ℝ (x : HilbertVec D) (pole D)) else 0) ∂(sphMeasure D) =
      sphereArea (D - 1) * ∫ φ in (0 : ℝ)..ε, F (Real.cos φ) * Real.sin φ ^ (D - 2) := by
  set G : ℝ → ℝ := (Set.Ioc (Real.cos ε) 1).indicator F with hG
  have hGm : Measurable G := hF.measurable.indicator measurableSet_Ioc
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hF.continuousOn
  have hGb : ∃ C, ∀ t, |G t| ≤ C := by
    refine ⟨max C 0, fun t => ?_⟩
    by_cases ht : t ∈ Set.Ioc (Real.cos ε) 1
    · rw [hG, Set.indicator_of_mem ht]
      exact (hC t ⟨by linarith [Real.neg_one_le_cos ε, ht.1], ht.2⟩).trans (le_max_left _ _)
    · rw [hG, Set.indicator_of_notMem ht]; simp
  have hpt : ∀ x : Sph D, (if Real.cos ε < inner ℝ (x : HilbertVec D) (pole D) then
        F (inner ℝ (x : HilbertVec D) (pole D)) else 0) =
      G (inner ℝ (x : HilbertVec D) (pole D)) := by
    intro x
    by_cases h : Real.cos ε < inner ℝ (x : HilbertVec D) (pole D)
    · have hm : inner ℝ (x : HilbertVec D) (pole D) ∈ Set.Ioc (Real.cos ε) 1 :=
        ⟨h, inner_le_one x⟩
      rw [hG, Set.indicator_of_mem hm]
      simp only [h, ↓reduceIte]
    · have hm : inner ℝ (x : HilbertVec D) (pole D) ∉ Set.Ioc (Real.cos ε) 1 := fun h' => h h'.1
      rw [hG, Set.indicator_of_notMem hm]
      simp only [h, ↓reduceIte]
  simp_rw [hpt]
  rw [integral_zonal hD G hGm hGb]
  congr 1
  set h : ℝ → ℝ := fun φ => G (Real.cos φ) * Real.sin φ ^ (D - 2) with hh
  obtain ⟨C', hC'⟩ := hGb
  have hhm : Measurable h := (hGm.comp Real.measurable_cos).mul (Real.measurable_sin.pow_const _)
  have hint : ∀ a b, IntervalIntegrable h volume a b := fun a b =>
    intervalIntegrable_of_bdd hhm (C := C') (fun φ => by
      rw [hh]
      simp only [abs_mul, abs_pow]
      calc |G (Real.cos φ)| * |Real.sin φ| ^ (D - 2) ≤ C' * 1 :=
            mul_le_mul (hC' _) (pow_le_one₀ (abs_nonneg _) (Real.abs_sin_le_one _))
              (by positivity) ((abs_nonneg _).trans (hC' 0))
        _ = C' := mul_one C') a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 ε) (hint ε Real.pi)]
  have h2 : ∫ φ in ε..Real.pi, h φ = 0 := by
    have : ∀ φ ∈ Set.uIcc ε Real.pi, h φ = 0 := by
      intro φ hφ
      rw [Set.uIcc_of_le hε'.le] at hφ
      have hc : Real.cos φ ≤ Real.cos ε :=
        Real.cos_le_cos_of_nonneg_of_le_pi hε.le hφ.2 hφ.1
      rw [hh]
      simp only [hG, Set.indicator_of_notMem (fun h' : Real.cos φ ∈ Set.Ioc (Real.cos ε) 1 =>
        absurd h'.1 (not_lt.2 hc)), zero_mul]
    rw [intervalIntegral.integral_congr this]; simp
  rw [h2, add_zero]
  rw [intervalIntegral.integral_of_le hε.le, intervalIntegral.integral_of_le hε.le,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun φ hφ => ?_
  have hc : Real.cos ε < Real.cos φ :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hφ.1.le hε'.le hφ.2
  simp only [hh, hG, Set.indicator_of_mem (show Real.cos φ ∈ Set.Ioc (Real.cos ε) 1 from
    ⟨hc, Real.cos_le_one _⟩)]

end Local

end

end PDE.FHLane
