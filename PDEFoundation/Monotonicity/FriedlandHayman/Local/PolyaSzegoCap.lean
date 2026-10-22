module

public import PDEFoundation.Monotonicity.FriedlandHayman.Local.PolyaSzegoAux
public import PDEFoundation.Monotonicity.FriedlandHayman.Transport.Weights

/-!
# Friedland--Hayman: measures of polar caps and zonal integrals of profiles

The measure of the set `{x | arccos ⟪x, e₀⟫ < θ}` is `σ_{D-2} ∫_0^θ sin^{D-2}`, hence
`capFrac D θ * σ_{D-1} = σ_{D-2} ∫_0^θ sin^{D-2}`, and the zonal integral of a bounded profile
`h (arccos ⟪x, e₀⟫)` is `σ_{D-2} ∫_0^π h(φ) sin^{D-2} φ dφ`.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PDE.FHLane

noncomputable section

namespace Local

variable {D : ℕ} [NeZero D]

theorem sphereArea_eq_mul_zTot (hD : 2 ≤ D) :
    sphereArea D = sphereArea (D - 1) * Transp.zTot D := by
  have h := integral_zonal hD (fun _ => (1 : ℝ)) measurable_const ⟨1, fun _ => by simp⟩
  simp only [integral_const, smul_eq_mul, mul_one, one_mul] at h
  rw [sphereArea_eq_real_univ]
  unfold Transp.zTot
  exact h

theorem capFrac_mul_sphereArea (hD : 2 ≤ D) (θ : ℝ) :
    capFrac D θ * sphereArea D = sphereArea (D - 1) * ∫ φ in (0 : ℝ)..θ, sinW D φ := by
  rw [sphereArea_eq_mul_zTot hD, capFrac_eq]
  have := (Transp.zTot_pos D).ne'
  field_simp

/-- The zonal integral of a bounded measurable profile of the angle. -/
theorem integral_profile (hD : 2 ≤ D) {h : ℝ → ℝ} (hm : Measurable h) {C : ℝ}
    (hC : ∀ φ, φ ∈ Set.Icc 0 Real.pi → |h φ| ≤ C) :
    ∫ x : Sph D, h (Real.arccos (inner ℝ (x : HilbertVec D) (pole D))) ∂(sphMeasure D) =
      sphereArea (D - 1) * ∫ φ in (0 : ℝ)..Real.pi, h φ * sinW D φ := by
  set G : ℝ → ℝ := fun t => h (Real.arccos t) with hG
  have hGm : Measurable G := hm.comp Real.continuous_arccos.measurable
  have hGb : ∃ C', ∀ t, |G t| ≤ C' := ⟨C, fun t =>
    hC _ ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩⟩
  refine (integral_zonal hD G hGm hGb).trans ?_
  congr 1
  refine intervalIntegral.integral_congr fun φ hφ => ?_
  rw [Set.uIcc_of_le Real.pi_pos.le] at hφ
  simp only [hG, Real.arccos_cos hφ.1 hφ.2, sinW]

theorem real_measure_arccos_lt (hD : 2 ≤ D) {θ : ℝ} (hθ : θ ≤ Real.pi) (hθ0 : 0 < θ) :
    (sphMeasure D).real {x : Sph D | Real.arccos (inner ℝ (x : HilbertVec D) (pole D)) < θ} =
      sphereArea (D - 1) * ∫ φ in (0 : ℝ)..θ, sinW D φ := by
  set T : Set ℝ := {t | Real.arccos t < θ} with hT
  have hTm : MeasurableSet T := measurableSet_lt Real.continuous_arccos.measurable measurable_const
  set G : ℝ → ℝ := T.indicator (fun _ => (1 : ℝ)) with hG
  have hGm : Measurable G := measurable_const.indicator hTm
  have hGb : ∃ C, ∀ t, |G t| ≤ C := ⟨1, fun t => by
    by_cases ht : t ∈ T <;> simp [hG, ht]⟩
  have hS : MeasurableSet {x : Sph D | Real.arccos (inner ℝ (x : HilbertVec D) (pole D)) < θ} :=
    hTm.preimage (continuous_subtype_val.inner continuous_const).measurable
  have h1 : (sphMeasure D).real {x : Sph D | Real.arccos (inner ℝ (x : HilbertVec D) (pole D)) < θ}
      = ∫ x : Sph D, G (inner ℝ (x : HilbertVec D) (pole D)) ∂(sphMeasure D) := by
    rw [← integral_indicator_one hS]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    by_cases hx : Real.arccos (inner ℝ (x : HilbertVec D) (pole D)) < θ
    · have : inner ℝ (x : HilbertVec D) (pole D) ∈ T := hx
      simp [hG, this, Set.indicator_of_mem (show x ∈ {x : Sph D | Real.arccos
        (inner ℝ (x : HilbertVec D) (pole D)) < θ} from hx)]
    · have : inner ℝ (x : HilbertVec D) (pole D) ∉ T := hx
      simp [hG, this, Set.indicator_of_notMem (show x ∉ {x : Sph D | Real.arccos
        (inner ℝ (x : HilbertVec D) (pole D)) < θ} from hx)]
  rw [h1, integral_zonal hD G hGm hGb]
  congr 1
  obtain ⟨C, hC⟩ := hGb
  have hint : ∀ a b, IntervalIntegrable (fun φ => G (Real.cos φ) * Real.sin φ ^ (D - 2)) volume a b :=
    fun a b => intervalIntegrable_of_bdd
      ((hGm.comp Real.measurable_cos).mul (Real.measurable_sin.pow_const _)) (C := C) (fun φ => by
        show |G (Real.cos φ) * Real.sin φ ^ (D - 2)| ≤ C
        rw [abs_mul, abs_pow]
        calc |G (Real.cos φ)| * |Real.sin φ| ^ (D - 2) ≤ C * 1 :=
              mul_le_mul (hC _) (pow_le_one₀ (abs_nonneg _) (Real.abs_sin_le_one _))
                (by positivity) ((abs_nonneg _).trans (hC 0))
          _ = C := mul_one C) a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 θ) (hint θ Real.pi)]
  have h2 : ∫ φ in θ..Real.pi, G (Real.cos φ) * Real.sin φ ^ (D - 2) = 0 := by
    have : ∀ φ ∈ Set.uIoc θ Real.pi, G (Real.cos φ) * Real.sin φ ^ (D - 2) = 0 := by
      intro φ hφ
      rw [Set.uIoc_of_le hθ] at hφ
      have hn : Real.cos φ ∉ T := by
        show ¬ Real.arccos (Real.cos φ) < θ
        rw [Real.arccos_cos (hθ0.le.trans hφ.1.le) hφ.2]
        exact not_lt.2 hφ.1.le
      simp [hG, hn]
    rw [intervalIntegral.integral_congr_ae (Eventually.of_forall this)]
    simp
  rw [h2, add_zero]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [(Set.toFinite ({θ} : Set ℝ)).countable.ae_notMem volume] with φ hne hφ
  rw [Set.uIoc_of_le hθ0.le] at hφ
  have hlt : φ < θ := lt_of_le_of_ne hφ.2 fun h' => hne (by simp [h'])
  have hm : Real.cos φ ∈ T := by
    show Real.arccos (Real.cos φ) < θ
    rw [Real.arccos_cos hφ.1.le (hφ.2.trans hθ)]
    exact hlt
  simp [hG, hm, sinW]

end Local

end

end PDE.FHLane
