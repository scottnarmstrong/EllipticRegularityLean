module

public import EllipticRegularity.Parabolic.WeakHarnack.LogEstimateBasic
public import EllipticRegularity.Parabolic.WeakHarnack.WeightedPoincareBall
public import PDEFoundation.Sobolev.ClassicalGradient

/-!
# The slice estimate for the logarithmic inequality

For `h ∈ H¹(B₁)`, `ν = ζ² dx / ∫ζ²` and `Λ ≥ 0`:
`c V(h) - Λ K₀ ≤ (∫ζ²)⁻¹ ∫_{B₁} (½ ζ² |∇h|² - 2Λ |∇ζ|²)`, where `V(h) = ∫ |h - ∫h dν|² dν`,
`c = 1/(2 C_P)` (`logTailC d`) and `K₀` depends only on `d` (`logTailK0 d`).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Parabolic.WeakHarnack

variable {d : ℕ}

theorem exists_radialCutoff_gradSq_bound (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Vec d, vecNormSq (spaceGradC1 (radialCutoff d) x) ≤ C := by
  obtain ⟨C, hC0, hC⟩ := radialCutoff_fderiv_bound d
  refine ⟨C ^ 2, by positivity, fun x => ?_⟩
  set g := spaceGradC1 (radialCutoff d) x with hg
  have h1 : vecNormSq g ≤ C * vecEuclideanNorm g := by
    have := hC x g
    have e : fderiv ℝ (radialCutoff d) x g = vecDot g g := by
      rw [PDE.fderiv_apply_eq_vecDot_classicalGradient, vecDot_comm]
      rfl
    rw [e] at this
    have h2 : vecDot g g = vecNormSq g := rfl
    rwa [h2, abs_of_nonneg (vecNormSq_nonneg g)] at this
  have h3 : vecNormSq g = vecEuclideanNorm g ^ 2 := (vecEuclideanNorm_sq g).symm
  have h4 : vecEuclideanNorm g ≤ C := by
    by_cases h0 : vecEuclideanNorm g = 0
    · rw [h0]; exact hC0
    · have hpos : 0 < vecEuclideanNorm g := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm h0)
      rw [h3] at h1
      nlinarith
  rw [h3]
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h4 2

/-- `sup |∇ζ|²`. -/
noncomputable def logGradBound (d : ℕ) : ℝ := (exists_radialCutoff_gradSq_bound d).choose

theorem logGradBound_nonneg (d : ℕ) : 0 ≤ logGradBound d :=
  (exists_radialCutoff_gradSq_bound d).choose_spec.1

theorem vecNormSq_spaceGrad_le (d : ℕ) (x : Vec d) :
    vecNormSq (spaceGradC1 (radialCutoff d) x) ≤ logGradBound d :=
  (exists_radialCutoff_gradSq_bound d).choose_spec.2 x

/-- The constant `c(d) = 1 / (2 C_P)` in the differential inequality for the mean. -/
noncomputable def logTailC (d : ℕ) : ℝ := 1 / (2 * weightedPoincareConst d)

theorem logTailC_pos (d : ℕ) : 0 < logTailC d := by
  have := weightedPoincareConst_pos d
  unfold logTailC; positivity

/-- The constant `K₀(d)`; the differential inequality holds with `K = Λ K₀`. -/
noncomputable def logTailK0 (d : ℕ) : ℝ :=
  2 * logGradBound d * (volume (euclideanBall (0 : Vec d) 1)).toReal / cutoffZ d

theorem logTailK0_nonneg (d : ℕ) : 0 ≤ logTailK0 d := by
  have := logGradBound_nonneg d
  have := cutoffZ_pos d
  unfold logTailK0; positivity

theorem continuous_vecNormSq_spaceGrad (d : ℕ) :
    Continuous fun x : Vec d => vecNormSq (spaceGradC1 (radialCutoff d) x) := by
  have : ∀ i, Continuous fun x : Vec d => spaceGradC1 (radialCutoff d) x i := fun i =>
    PDE.Parabolic.WeakSlice.spaceGradC1_continuous
      ((radialCutoff_contDiff d).of_le (by exact_mod_cast le_top)) i
  simp only [vecNormSq_eq_sum_sq]
  exact continuous_finsetSum _ fun i _ => (this i).pow 2

theorem integrableOn_gradNeg (d : ℕ) (Λ : ℝ) :
    IntegrableOn (fun x : Vec d => 2 * Λ * vecNormSq (spaceGradC1 (radialCutoff d) x))
      (euclideanBall (0 : Vec d) 1) := by
  have hfin : IsFiniteMeasure (volume.restrict (euclideanBall (0 : Vec d) 1)) :=
    isFiniteMeasure_restrict.mpr (volume_euclideanBall_ne_top 0 zero_le_one)
  refine Integrable.mono' (g := fun _ => |2 * Λ| * logGradBound d) (integrable_const _)
    ((continuous_vecNormSq_spaceGrad d).const_mul (2 * Λ)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (vecNormSq_nonneg _)]
  exact mul_le_mul_of_nonneg_left (vecNormSq_spaceGrad_le d x) (abs_nonneg _)

theorem integrableOn_zeta_grad (d : ℕ) (h : H1Function (euclideanBall (0 : Vec d) 1)) :
    IntegrableOn (fun x => radialCutoff d x ^ 2 * vecNormSq (h.grad x))
      (euclideanBall (0 : Vec d) 1) := by
  refine Integrable.mono' (integrableOn_grad_ball h (R := 1) subset_rfl)
    (((measurable_radialCutoff d).pow_const 2).aestronglyMeasurable.mul
      (integrableOn_grad_ball h (R := 1) subset_rfl).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  have h0 := radialCutoff_nonneg (d := d) x
  have h1 := radialCutoff_le_one (d := d) x
  have h2 := vecNormSq_nonneg (h.grad x)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have : radialCutoff d x ^ 2 ≤ 1 := by nlinarith
  nlinarith

theorem logSlice_aux {zi Cp W E Ib Kt : ℝ} (hzi : 0 ≤ zi) (hCP : 0 < Cp) (hP : W ≤ Cp * E)
    (hIb : Ib ≤ Kt) : 1 / (2 * Cp) * (zi * W) - zi * Kt ≤ zi * (1 / 2 * E - Ib) := by
  have h1 : 1 / (2 * Cp) * W ≤ 1 / 2 * E := by
    calc _ ≤ 1 / (2 * Cp) * (Cp * E) := mul_le_mul_of_nonneg_left hP (by positivity)
      _ = 1 / 2 * E := by field_simp
  have h2 := mul_le_mul_of_nonneg_left h1 hzi
  have h3 := mul_le_mul_of_nonneg_left hIb hzi
  have e1 : zi * (1 / 2 * E - Ib) = zi * (1 / 2 * E) - zi * Ib := by ring
  have e2 : 1 / (2 * Cp) * (zi * W) = zi * (1 / (2 * Cp) * W) := by ring
  rw [e1, e2]
  linarith

/-- **Slice estimate.** -/
theorem logSlice_lower {Λ : ℝ} (hΛ : 0 ≤ Λ) (h : H1Function (euclideanBall (0 : Vec d) 1)) :
    logTailC d * (∫ x, (h x - ∫ y, h y ∂(cutoffMeasure d)) ^ 2 ∂(cutoffMeasure d)) -
        Λ * logTailK0 d ≤
      (cutoffZ d)⁻¹ * ∫ x in euclideanBall (0 : Vec d) 1,
        (1 / 2 * radialCutoff d x ^ 2 * vecNormSq (h.grad x) -
          2 * Λ * vecNormSq (spaceGradC1 (radialCutoff d) x)) := by
  have hZ := cutoffZ_pos d
  have hP := weightedPoincare_radialCutoff (subset_rfl : (euclideanBall (0 : Vec d) 1) ⊆ (euclideanBall (0 : Vec d) 1)) h
  have hmean : (∫ y in euclideanBall (0 : Vec d) 1, h y * radialCutoff d y ^ 2) / (∫ y in euclideanBall (0 : Vec d) 1, radialCutoff d y ^ 2) =
      ∫ y, h y ∂(cutoffMeasure d) := by
    rw [integral_cutoffMeasure]
    change _ / cutoffZ d = _
    rw [div_eq_inv_mul]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only; ring
  rw [hmean] at hP
  have hV : ∫ x, (h x - ∫ y, h y ∂(cutoffMeasure d)) ^ 2 ∂(cutoffMeasure d) =
      (cutoffZ d)⁻¹ * ∫ x in euclideanBall (0 : Vec d) 1, (h x - ∫ y, h y ∂(cutoffMeasure d)) ^ 2 * radialCutoff d x ^ 2 := by
    rw [integral_cutoffMeasure]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only; ring
  have hi1 : Integrable (fun x : Vec d => 1 / 2 * radialCutoff d x ^ 2 * vecNormSq (h.grad x))
      (volume.restrict (euclideanBall (0 : Vec d) 1)) :=
    ((integrableOn_zeta_grad d h).const_mul (1 / 2)).congr
      (Filter.Eventually.of_forall fun x => by simp only; ring)
  have hsplit : ∫ x in (euclideanBall (0 : Vec d) 1), (1 / 2 * radialCutoff d x ^ 2 * vecNormSq (h.grad x) -
        2 * Λ * vecNormSq (spaceGradC1 (radialCutoff d) x)) =
      1 / 2 * (∫ x in (euclideanBall (0 : Vec d) 1), vecNormSq (h.grad x) * radialCutoff d x ^ 2) -
        ∫ x in (euclideanBall (0 : Vec d) 1), 2 * Λ * vecNormSq (spaceGradC1 (radialCutoff d) x) := by
    have hc := integral_const_mul (μ := volume.restrict (euclideanBall (0 : Vec d) 1)) (1 / 2 : ℝ)
      (fun x => vecNormSq (h.grad x) * radialCutoff d x ^ 2)
    rw [integral_sub hi1 (integrableOn_gradNeg d Λ), ← hc]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only; ring
  have hneg : ∫ x in euclideanBall (0 : Vec d) 1, 2 * Λ * vecNormSq (spaceGradC1 (radialCutoff d) x) ≤
      2 * Λ * logGradBound d * (volume (euclideanBall (0 : Vec d) 1)).toReal := by
    have := setIntegral_mono_on (integrableOn_gradNeg d Λ) (integrableOn_const (μ := volume)
      (s := (euclideanBall (0 : Vec d) 1)) (C := 2 * Λ * logGradBound d) (hs := (volume_euclideanBall_ne_top 0 zero_le_one)))
      (measurableSet_euclideanBall _ _) (fun x _ => by
        have := vecNormSq_spaceGrad_le d x
        nlinarith)
    simpa [Measure.real, mul_comm] using this
  have hK : Λ * logTailK0 d = (cutoffZ d)⁻¹ * (2 * Λ * logGradBound d * (volume (euclideanBall (0 : Vec d) 1)).toReal) := by
    unfold logTailK0; field_simp
  rw [hsplit, hV, hK, logTailC]
  exact logSlice_aux (inv_nonneg.2 hZ.le) (weightedPoincareConst_pos d) hP hneg

end PDE.Parabolic.WeakHarnack
