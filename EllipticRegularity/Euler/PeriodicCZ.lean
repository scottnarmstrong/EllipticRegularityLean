module

public import EllipticRegularity.Euler.PeriodicCZStep

/-!
# Periodic Calderón–Zygmund estimate on the torus (manuscript Lemma 3.14, in the form used by Yudovich)

For a smooth `ℤ²`-periodic divergence-free field `u` with `|curl u| ≤ M` pointwise, and every `p ≥ 2`:
`∫_{[0,1]²} |∇u|^p ≤ (K p M)^p` with `K` absolute (independent of `u`, `M`, `p`).
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

/-- The Frobenius norm `|∇u| = (∑ᵢⱼ (∂ⱼuᵢ)²)^{1/2}` of the gradient of a planar field. -/
noncomputable def torusGradNorm (u : Vec 2 → Vec 2) (x : Vec 2) : ℝ :=
  Real.sqrt (∑ i, ∑ j, pd j (fun y => u y i) x ^ 2)

theorem torusGradNorm_nonneg (u : Vec 2 → Vec 2) (x : Vec 2) : 0 ≤ torusGradNorm u x :=
  Real.sqrt_nonneg _

theorem vecEuclideanNorm_classicalGradient (g : Vec 2 → ℝ) (x : Vec 2) :
    vecEuclideanNorm (classicalGradient g x) = Real.sqrt (∑ j, pd j g x ^ 2) := by
  rw [vecEuclideanNorm, vecNormSq_classicalGradient]

theorem sqrt_add_le_add_sqrt' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

theorem torusGradNorm_le (u : Vec 2 → Vec 2) (x : Vec 2) :
    torusGradNorm u x ≤ vecEuclideanNorm (classicalGradient (fun y => u y 0) x) +
      vecEuclideanNorm (classicalGradient (fun y => u y 1) x) := by
  simp only [vecEuclideanNorm_classicalGradient]
  unfold torusGradNorm
  rw [Fin.sum_univ_two (f := fun i => ∑ j, pd j (fun y => u y i) x ^ 2)]
  exact sqrt_add_le_add_sqrt' (Finset.sum_nonneg fun j _ => sq_nonneg _)
    (Finset.sum_nonneg fun j _ => sq_nonneg _)

theorem rpow_add_le_two_mul {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 1 ≤ p) :
    (a + b) ^ p ≤ 2 ^ p * (a ^ p + b ^ p) := by
  have hp0 : 0 ≤ p := by linarith
  have h1 : (a + b) ^ p ≤ (2 * max a b) ^ p :=
    Real.rpow_le_rpow (by positivity) (by cases max_cases a b <;> linarith [le_max_left a b, le_max_right a b]) hp0
  rw [Real.mul_rpow (by norm_num) (le_max_of_le_left ha)] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rcases le_total a b with h | h
  · rw [max_eq_right h]; exact le_add_of_nonneg_left (Real.rpow_nonneg ha _)
  · rw [max_eq_left h]; exact le_add_of_nonneg_right (Real.rpow_nonneg hb _)

theorem continuous_component_gradNorm {u : Vec 2 → Vec 2}
    (hu : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => u x i)) (i : Fin 2) :
    Continuous fun x => vecEuclideanNorm (classicalGradient (fun y => u y i) x) := by
  simp only [vecEuclideanNorm_classicalGradient]
  exact Real.continuous_sqrt.comp
    (continuous_finsetSum _ fun j _ => (contDiff_pd_top (hu i) j).continuous.pow 2)

theorem continuous_torusGradNorm {u : Vec 2 → Vec 2}
    (hu : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => u x i)) : Continuous (torusGradNorm u) := by
  unfold torusGradNorm
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => (contDiff_pd_top (hu i) j).continuous.pow 2)

/-- **Periodic CZ estimate**: `∫_{cube} |∇u|^p ≤ (K p M)^p` for `p ≥ 2`, with an absolute constant `K`. -/
theorem exists_torus_cz :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p : ℝ, 2 ≤ p → ∀ (u : Vec 2 → Vec 2) (M : ℝ),
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => u x i)) → IsTorusPeriodic u → (∀ x, torusDiv u x = 0) →
      (∀ x, |torusCurl u x| ≤ M) →
      ∫ x in torusCube, torusGradNorm u x ^ p ≤ (K * p * M) ^ p := by
  obtain ⟨C, hC1, hC⟩ := exists_component_cz
  set V := ballVolHalf with hV
  set c0 : ℝ := 3 * Real.sqrt ballVolOne⁻¹ with hc0
  have hc00 : 0 ≤ c0 := by positivity
  have hV0 : 0 ≤ V := ballVolHalf_nonneg
  have hC0 : 0 ≤ C := by linarith
  refine ⟨max 1 (8 * V) * 2 * C * (c0 / 2 + 1), by positivity, ?_⟩
  intro p hp u M hu hup hdiv hω
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hω 0)
  have hp0 : 0 ≤ p := by linarith
  have hp1 : 1 ≤ p := by linarith
  have hIcc : ∀ {F : Vec 2 → ℝ}, Continuous F → IntegrableOn F torusCube :=
    fun hF => hF.continuousOn.integrableOn_Icc
  have hcN : ∀ i, Continuous fun x => vecEuclideanNorm (classicalGradient (fun y => u y i) x) ^ p :=
    fun i => Continuous.rpow_const (continuous_component_gradNorm hu i) (fun _ => Or.inr hp0)
  have hS : ∀ i, ∫ x in torusCube, vecEuclideanNorm (classicalGradient (fun y => u y i) x) ^ p ≤
      4 * (V * (C * (c0 * M + p * M)) ^ p) := by
    intro i
    calc _ ≤ ∑ idx : Fin 2 → Fin 2, ∫ x in euclideanBall (0 : Vec 2) (1 / 2 : ℝ),
          vecEuclideanNorm (classicalGradient (fun y => u y i) (ballCentre idx + x)) ^ p :=
          setIntegral_cube_le_sum_balls (hcN i) (fun x => Real.rpow_nonneg (vecEuclideanNorm_nonneg _) _)
      _ ≤ ∑ _idx : Fin 2 → Fin 2, V * (C * (c0 * M + p * M)) ^ p :=
          Finset.sum_le_sum fun idx _ => hC p hp u M hu hup hdiv hω i _ (ballCentre_mem idx)
      _ = 4 * (V * (C * (c0 * M + p * M)) ^ p) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun]
          simp
  have hpt : ∀ x, torusGradNorm u x ^ p ≤ 2 ^ p *
      (vecEuclideanNorm (classicalGradient (fun y => u y 0) x) ^ p +
        vecEuclideanNorm (classicalGradient (fun y => u y 1) x) ^ p) := fun x =>
    (Real.rpow_le_rpow (torusGradNorm_nonneg u x) (torusGradNorm_le u x) hp0).trans
      (rpow_add_le_two_mul (vecEuclideanNorm_nonneg _) (vecEuclideanNorm_nonneg _) hp1)
  have hcG : Continuous fun x => torusGradNorm u x ^ p :=
    Continuous.rpow_const (continuous_torusGradNorm hu) (fun _ => Or.inr hp0)
  have hint : ∫ x in torusCube, torusGradNorm u x ^ p ≤ 2 ^ p * (2 * (4 * (V * (C * (c0 * M + p * M)) ^ p))) := by
    calc _ ≤ ∫ x in torusCube, 2 ^ p *
          (vecEuclideanNorm (classicalGradient (fun y => u y 0) x) ^ p +
            vecEuclideanNorm (classicalGradient (fun y => u y 1) x) ^ p) :=
          setIntegral_mono (hIcc hcG) (Integrable.const_mul (Integrable.add (hIcc (hcN 0)) (hIcc (hcN 1))) _) hpt
      _ = 2 ^ p * ((∫ x in torusCube, vecEuclideanNorm (classicalGradient (fun y => u y 0) x) ^ p) +
            ∫ x in torusCube, vecEuclideanNorm (classicalGradient (fun y => u y 1) x) ^ p) := by
          rw [integral_const_mul, integral_add (hIcc (hcN 0)) (hIcc (hcN 1))]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith [hS 0, hS 1]
  refine hint.trans ?_
  set L := max 1 (8 * V) with hL
  have hL1 : 1 ≤ L := le_max_left _ _
  have h8 : 8 * V ≤ L ^ p := (le_max_right _ _).trans (Real.self_le_rpow_of_one_le hL1 hp1)
  have hbase : 2 * C * (c0 + p) * M ≤ 2 * C * (c0 / 2 + 1) * p * M := by
    have : c0 + p ≤ (c0 / 2 + 1) * p := by nlinarith
    have h2C : 0 ≤ 2 * C := by positivity
    calc 2 * C * (c0 + p) * M ≤ 2 * C * ((c0 / 2 + 1) * p) * M :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this h2C) hM
      _ = _ := by ring
  have hlhs : 2 ^ p * (2 * (4 * (V * (C * (c0 * M + p * M)) ^ p))) =
      (8 * V) * (2 * C * (c0 + p) * M) ^ p := by
    have : (2 * C * (c0 + p) * M) = 2 * (C * (c0 * M + p * M)) := by ring
    rw [this, Real.mul_rpow (x := 2) (y := C * (c0 * M + p * M)) (by norm_num)
      (mul_nonneg hC0 (by positivity))]
    ring
  rw [hlhs]
  have hb0 : 0 ≤ 2 * C * (c0 + p) * M := by positivity
  calc (8 * V) * (2 * C * (c0 + p) * M) ^ p
      ≤ L ^ p * (2 * C * (c0 / 2 + 1) * p * M) ^ p :=
        mul_le_mul h8 (Real.rpow_le_rpow hb0 hbase hp0) (Real.rpow_nonneg hb0 _) (by positivity)
    _ = (L * 2 * C * (c0 / 2 + 1) * p * M) ^ p := by
        rw [← Real.mul_rpow (by positivity) (by positivity)]
        ring_nf

/-- **Periodic CZ estimate in plain `L^p(cube)` form**: `‖∇u‖_{L^p(cube)} ≤ K p M`, same hypotheses. -/
theorem exists_torus_cz_eLpNorm :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p : ℝ, 2 ≤ p → ∀ (u : Vec 2 → Vec 2) (M : ℝ),
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => u x i)) → IsTorusPeriodic u → (∀ x, torusDiv u x = 0) →
      (∀ x, |torusCurl u x| ≤ M) →
      MemLp (torusGradNorm u) (ENNReal.ofReal p) (volume.restrict torusCube) ∧
      eLpNorm (torusGradNorm u) (ENNReal.ofReal p) (volume.restrict torusCube) ≤
        ENNReal.ofReal (K * p * M) := by
  obtain ⟨K, hK, hcz⟩ := exists_torus_cz
  refine ⟨K, hK, ?_⟩
  intro p hp u M hu hup hdiv hω
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hω 0)
  have hp0 : 0 < p := by linarith
  have : IsFiniteMeasure (volume.restrict torusCube) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (isCompact_Icc : IsCompact torusCube).measure_lt_top⟩
  have hc := continuous_torusGradNorm hu
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact torusCube).exists_bound_of_continuousOn hc.continuousOn
  have hmem : MemLp (torusGradNorm u) (ENNReal.ofReal p) (volume.restrict torusCube) :=
    MemLp.of_bound hc.aestronglyMeasurable B
      ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall hB))
  refine ⟨hmem, ?_⟩
  have hne0 : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hnetop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have htr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  rw [hmem.eLpNorm_eq_integral_rpow_norm hne0 hnetop, htr]
  refine ENNReal.ofReal_le_ofReal ?_
  have hI : ∫ x in torusCube, ‖torusGradNorm u x‖ ^ p = ∫ x in torusCube, torusGradNorm u x ^ p :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp [abs_of_nonneg (torusGradNorm_nonneg u x)])
  rw [hI, ← one_div]
  have hKpM : 0 ≤ K * p * M := by positivity
  calc (∫ x in torusCube, torusGradNorm u x ^ p) ^ (1 / p) ≤ ((K * p * M) ^ p) ^ (1 / p) :=
        Real.rpow_le_rpow (setIntegral_nonneg measurableSet_Icc fun x _ =>
          Real.rpow_nonneg (torusGradNorm_nonneg u x) _) (hcz p hp u M hu hup hdiv hω)
          (by positivity)
    _ = K * p * M := by
        rw [← Real.rpow_mul hKpM, mul_one_div_cancel hp0.ne', Real.rpow_one]

end PDE
